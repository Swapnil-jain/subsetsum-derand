#!/usr/bin/env bash
# axioms_ok.sh OUT AXIOMS.lean: every `#print axioms` line of AXIOMS.lean printed exactly one result in OUT, and each
# result names only the standard axioms propext, Classical.choice and Quot.sound (or a subset, or none).
set -u
out=$1; src=$2
want=$(grep -c '^#print axioms' "$src")
ax='(propext|Classical\.choice|Quot\.sound)'
good=$(grep -cE "(depends on axioms: \[$ax(, $ax)*\]|does not depend on any axioms)$" "$out")
any=$(grep -cE "depends on axioms|does not depend on any axioms" "$out")
if grep -qE "sorryAx|ofReduceBool|error" "$out" || [ "$good" -ne "$want" ] || [ "$any" -ne "$want" ]; then
  echo "AXIOMS: FAIL ($good standard of $want printed, $any results)"; exit 1
fi
echo "AXIOMS: PASS ($want theorems, standard axioms only)"
