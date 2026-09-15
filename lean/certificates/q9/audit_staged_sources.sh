#!/bin/zsh
set -e

# Reproducible, source-only audit for the generated q=9 staged LRAT chain.
# This intentionally does not invoke Lean, so it is safe to run while the
# large .olean replay is paused for memory pressure.  Pass R4_LAST/R5_LAST to
# restrict the scan when only a completed prefix is available.

r4_last=${R4_LAST:-197}
r5_last=${R5_LAST:-127}
check_olean=${CHECK_OLEAN:-0}

# CHECK_OLEAN=1 additionally requires the compiled artifact for every stage
# in the requested prefix.  The default remains source-only so this script is
# safe before a replay job has produced any `.olean` files.
olean_dir=".lake/build/lib/lean"

audit_family() {
  local family=$1
  local last=$2
  local lower="q9_${family:l}"
  local count=0

  for i in $(seq 0 "$last"); do
    local src="Q9${family:u}Stage${i}.lean"
    test -f "$src"
    if [[ "$check_olean" == "1" ]]; then
      test -f "${olean_dir}/Q9${family:u}Stage${i}.olean"
    fi
    if [[ "$i" -eq 0 ]]; then
      awk -v seed="${lower}_stage${i}_seed" \
          -v ids="${lower}_stage${i}_export_ids" \
          -v export_name="${lower}_stage${i}_export" \
          -v dummy="proof_export ${lower}_stage0_dummy_export" \
          'index($0, "def " seed) { found_seed=1 }
           index($0, "def " ids) { found_ids=1 }
           index($0, export_name) { found_export=1 }
           index($0, dummy) { found_dummy=1 }
           index($0, "import Q9R4Stage") || index($0, "import Q9R5Stage") { found_import=1 }
           END { exit !(found_seed && found_ids && found_export && found_dummy && !found_import) }' "$src"
    else
      awk -v seed="${lower}_stage${i}_seed" \
          -v ids="${lower}_stage${i}_export_ids" \
          -v export_name="${lower}_stage${i}_export" \
          -v import_name="import Q9${family:u}Stage$((i-1))" \
          -v proof="proof_export ${lower}_stage$((i-1))_export" \
          'index($0, "def " seed) { found_seed=1 }
           index($0, "def " ids) { found_ids=1 }
           index($0, export_name) { found_export=1 }
           index($0, import_name) { found_import=1 }
           index($0, proof) { found_proof=1 }
           END { exit !(found_seed && found_ids && found_export && found_import && found_proof) }' "$src"
    fi
    count=$((count + 1))
  done
  print "${family}: ${count} staged sources OK"
}

audit_family r4 "$r4_last"
audit_family r5 "$r5_last"

rg -q 'import Q9R4Stage197' Q9NoInfR4LRATStagedProof.lean
rg -q 'q9_r4_stage197' Q9NoInfR4LRATStagedProof.lean
rg -q 'import Q9R5Stage127' Q9NoInfR5LRATStagedProof.lean
rg -q 'q9_r5_stage127' Q9NoInfR5LRATStagedProof.lean
rg -q 'import Q9NoInfR4LRATStagedProof' Q9NoInfLRATFinal.lean
rg -q 'import Q9NoInfR5LRATStagedProof' Q9NoInfLRATFinal.lean
rg -q 'q9_no_rainbow_lrat' Q9NoInfLRATFinal.lean
rg -q 'import Q9NoInfLRATFinal' Erdos811FC.lean
rg -q 'q9_no_rainbow_staged_lrat' Erdos811FC.lean
rg -q 'erdos_811.variants.axenovich_clemen_all_cliques' Erdos811FC.lean

print 'final staged wrapper references OK'
