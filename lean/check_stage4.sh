#!/usr/bin/env bash
# One-command kernel check of Stage 4 (certificates/stage4): build every Stage 4 module one at a time under
# build_watch.sh (nice -n 19, one Lean thread, abort above 3 GB RSS), then print the axioms of every theorem.
# Expect: every build "exit 0", and axioms_stage4.out listing only propext, Classical.choice, Quot.sound.
set -euo pipefail
cd "$(dirname "$0")"
mods=$(cat stage4_modules.txt; printf '%s\n' Stage4ECheck Stage4Defs Stage4EDefs Stage4ERows Stage4Base Stage4XI Stage4E Stage4)
for m in $mods; do
  ./build_watch.sh build "SubsetsumLean.$m" | grep -v '^trace' | tail -1
done
./build_watch.sh env lean SubsetsumLean/Stage4Axioms.lean > axioms_stage4.out
./axioms_ok.sh axioms_stage4.out SubsetsumLean/Stage4Axioms.lean | sed 's/^AXIOMS/STAGE 4 LEAN/'
exit "${PIPESTATUS[0]}"
