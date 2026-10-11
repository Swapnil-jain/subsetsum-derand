#!/usr/bin/env bash
# One-command kernel check of Stage 5b (certificate cert_stage5b.py): build every module it needs one at a time under
# build_watch.sh (nice -n 19, one Lean thread, optional RSS abort (set LIMIT_MB=3072 on an 8 GB machine)), then print the axioms of every Stage 5b theorem.
# Stage 5b reuses Stage 4's cell checker and Stage 5's row checker and circuit data, so those modules come first (each
# is a no-op once built). Modules are built in import order: a bare `lake build` would run independent modules in
# parallel, above 3 GB on an 8 GB machine.
# Expect: every build "exit 0", and axioms_stage5b.out listing only propext, Classical.choice, Quot.sound.
set -euo pipefail
cd "$(dirname "$0")"
mods=$(cat stage4_modules.txt
       printf '%s\n' Stage4ECheck Stage4Defs Stage4EDefs Stage4Base Stage5ECheck Stage5Data Stage5EDefs Stage5Base
       cat stage5b_modules.txt
       printf '%s\n' Stage5bDefs
       cat stage5b_light_modules.txt
       printf '%s\n' Stage5bBase
       for t in f104 f111 f118 f125 f145 f110; do printf '%s\n' Stage5bFam_$t Stage5bCtl_${t}_F1 Stage5bCtl_${t}_NEED; done
       printf '%s\n' Stage5bE Stage5b)
for m in $mods; do
  ./build_watch.sh build "SubsetsumLean.$m" | grep -v '^trace' | tail -1
done
./build_watch.sh env lean SubsetsumLean/Stage5bAxioms.lean > axioms_stage5b.out
if [ -x ./axioms_ok.sh ]; then
  ./axioms_ok.sh axioms_stage5b.out SubsetsumLean/Stage5bAxioms.lean | sed 's/^AXIOMS/STAGE 5b LEAN/'
  exit "${PIPESTATUS[0]}"
fi
if grep -q "sorryAx\|ofReduceBool\|error" axioms_stage5b.out; then echo "STAGE 5b LEAN: FAIL"; exit 1; fi
n=$(grep -c "depends on axioms" axioms_stage5b.out)
[ "$n" -eq "$(grep -c '^#print axioms' SubsetsumLean/Stage5bAxioms.lean)" ] || { echo "STAGE 5b LEAN: FAIL (missing)"; exit 1; }
echo "STAGE 5b LEAN: PASS ($n theorems, standard axioms only)"
