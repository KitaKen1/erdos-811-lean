#!/bin/zsh
set -e

start=${1:-0}
end=${2:-197}
min_free=${MIN_FREE_PERCENT:-70}
min_disk_gb=${MIN_FREE_DISK_GB:-5}
min_disk_kb=$((min_disk_gb * 1024 * 1024))

free_disk_kb() {
  df -Pk . 2>/dev/null | awk 'END {print $4}'
}

# Optional resource controls for the large generated LRAT modules.  Unset
# variables preserve the historical compiler settings; on constrained hosts,
# e.g. LEAN_THREADS=1 LEAN_MEMORY_MB=12000 limits Lean's parallelism/heap.
lean_args=()
if [[ -n "${LEAN_THREADS:-}" ]]; then
  lean_args+=("-j" "$LEAN_THREADS")
fi
if [[ -n "${LEAN_MEMORY_MB:-}" ]]; then
  lean_args+=("-M" "$LEAN_MEMORY_MB")
fi

worker_pid=""
kill_worker_tree() {
  local pid=$1
  [[ -z "$pid" ]] && return 0
  local child
  for child in $(pgrep -P "$pid" 2>/dev/null); do
    kill_worker_tree "$child"
  done
  kill "$pid" 2>/dev/null || true
}
cleanup_worker() {
  if [[ -n "$worker_pid" ]]; then
    kill_worker_tree "$worker_pid"
    worker_pid=""
  fi
}
trap 'cleanup_worker; exit 130' INT TERM
trap cleanup_worker EXIT

for i in $(seq "$start" "$end"); do
  src="Q9R4Stage${i}.lean"
  out=".lake/build/lib/lean/Q9R4Stage${i}.olean"
  log="/private/tmp/q9_r4_stage${i}.log"
  if [[ -f "$out" && "${FORCE_REBUILD:-0}" != "1" ]]; then
    echo "skipping r=4 stage $i: existing $out"
    continue
  fi
  mem_line=$(memory_pressure -Q 2>/dev/null | awk '/free percentage/ {print $NF; exit}')
  mem_pct=${mem_line%%%}
  if [[ -n "$mem_pct" && "$mem_pct" -lt "$min_free" ]]; then
    echo "stopping before stage $i: memory free ${mem_pct}% < ${min_free}%"
    exit 3
  fi
  disk_kb=$(free_disk_kb)
  if [[ -n "$disk_kb" && "$disk_kb" -lt "$min_disk_kb" ]]; then
    echo "stopping before stage $i: disk free ${disk_kb}KB < ${min_disk_gb}GB"
    exit 4
  fi
  /usr/bin/time -p lake env lean "${lean_args[@]}" -o "$out" "$src" >"$log" 2>&1 &
  worker_pid=$!
  if wait "$worker_pid"; then
    stage_status=0
  else
    stage_status=$?
  fi
  worker_pid=""
  tail -4 "$log"
  if [[ "$stage_status" -ne 0 ]]; then
    exit "$stage_status"
  fi
  mem_line=$(memory_pressure -Q 2>/dev/null | awk '/free percentage/ {print $NF; exit}')
  mem_pct=${mem_line%%%}
  if [[ -n "$mem_pct" && "$mem_pct" -lt "$min_free" ]]; then
    echo "stopping after stage $i: memory free ${mem_pct}% < ${min_free}%"
    exit 3
  fi
  disk_kb=$(free_disk_kb)
  if [[ -n "$disk_kb" && "$disk_kb" -lt "$min_disk_kb" ]]; then
    echo "stopping after stage $i: disk free ${disk_kb}KB < ${min_disk_gb}GB"
    exit 4
  fi
done
