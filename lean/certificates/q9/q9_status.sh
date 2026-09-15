#!/bin/zsh
set -e

# Lightweight status/resume helper.  It never invokes Lean.
script_dir=${0:A:h}
lean_dir=${script_dir:h:h}
cd "$lean_dir"

min_free=${MIN_FREE_PERCENT:-50}
min_disk_gb=${MIN_FREE_DISK_GB:-5}

mem_line=$(memory_pressure -Q 2>/dev/null | awk '/free percentage/ {print $NF; exit}' || true)
mem_pct=${mem_line%%%}
disk_kb=$(df -Pk . 2>/dev/null | awk 'END {print $4}' || true)
disk_gb=""
if [[ -n "$disk_kb" ]]; then
  disk_gb=$((disk_kb / 1024 / 1024))
fi

count_outputs() {
  local prefix=$1
  find .lake/build/lib/lean -maxdepth 1 -name "${prefix}Stage*.olean" 2>/dev/null \
    | awk -F 'Stage' 'match($2, /^[0-9]+/) {print substr($2, RSTART, RLENGTH)}' \
    | sort -n | uniq | wc -l | tr -d ' '
}

first_missing() {
  local prefix=$1
  local last=$2
  local i
  for i in $(seq 0 "$last"); do
    if [[ ! -f ".lake/build/lib/lean/${prefix}Stage${i}.olean" ]]; then
      print "$i"
      return 0
    fi
  done
  print "none"
}

r4_count=$(count_outputs Q9R4)
r5_count=$(count_outputs Q9R5)
r4_next=$(first_missing Q9R4 197)
r5_next=$(first_missing Q9R5 127)

print "memory_free=${mem_pct:-unknown}% (gate=${min_free}%)"
print "disk_free=${disk_gb:-unknown}GiB (gate=${min_disk_gb}GiB)"
print "r4_olean=${r4_count}/198 next=${r4_next}"
print "r5_olean=${r5_count}/128 next=${r5_next}"
if [[ "$r4_next" != "none" && "$r5_next" != "none" ]]; then
  print "resume_r4: MIN_FREE_PERCENT=${min_free} zsh certificates/q9/compile_lrat_stages.sh ${r4_next} 197"
  print "resume_r5: MIN_FREE_PERCENT=${min_free} zsh certificates/q9/compile_lrat_stages_r5.sh ${r5_next} 127"
fi
if [[ -n "$mem_pct" && "$mem_pct" -lt "$min_free" ]]; then
  exit 3
fi
if [[ -n "$disk_kb" && "$disk_kb" -lt $((min_disk_gb * 1024 * 1024)) ]]; then
  exit 4
fi
