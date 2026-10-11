#!/usr/bin/env bash
# One-command kernel check of Stage 5 (certificates/stage5): build every module it needs one at a time under build_watch.sh
# (nice -n 19, one Lean thread, abort above 3 GB RSS), then print the axioms of every Stage 5 theorem.
# Stage 5 reuses Stage 4's cell checker, its s = 11/100, 1/8 and family circuits, and its entropy lemmas, so the
# Stage 4 modules come first (each is a no-op once built). Modules are built in import order: a bare `lake build`
# would run independent modules in parallel, above 3 GB on the 8 GB Mac.
# Expect: every build "exit 0", and axioms_stage5.out listing only propext, Classical.choice, Quot.sound.
set -euo pipefail
cd "$(dirname "$0")"
mods=$(cat stage4_modules.txt; printf '%s\n' Stage4ECheck Stage4Defs Stage4EDefs Stage4Base Stage4XI Stage5ECheck
       cat stage5_modules.txt stage5_light_modules.txt
       printf '%s\n' Stage5EDefs Stage5Base Stage5XI Stage5Ctl_0 Stage5Ctl_1 Stage5E Stage5)
for m in $mods; do
  ./build_watch.sh build "SubsetsumLean.$m" | grep -v '^trace' | tail -1
done
./build_watch.sh env lean SubsetsumLean/Stage5Axioms.lean > axioms_stage5.out
./axioms_ok.sh axioms_stage5.out SubsetsumLean/Stage5Axioms.lean | sed 's/^AXIOMS/STAGE 5 LEAN/'
exit "${PIPESTATUS[0]}"
