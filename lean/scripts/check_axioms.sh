#!/bin/sh
# Fails if any theorem of the hand-written library (scripts/CheckAxioms.lean: the listed theorems
# and `#audit_axioms ReflectZphi`) depends on an axiom outside {propext, Classical.choice,
# Quot.sound}. The imported results (ReflectZphi/Imported.lean) are hypotheses, not axioms, so
# nothing else is allowed. The certificate library is audited by ReflectZphi/Results.lean.
cd "$(dirname "$0")/.." || exit 1
out=$(lake env lean scripts/CheckAxioms.lean 2>&1) || { echo "$out"; exit 1; }
echo "$out"
bad=$(echo "$out" | tr ',[]' '\n\n\n' | sed 's/^ *//' | grep -v "^$" | grep -v "depends on axioms:" \
      | grep -vx "propext\|Classical.choice\|Quot.sound" | grep -v "does not depend on any axioms" \
      | grep -v -E "^#audit_axioms .*: [0-9]+ theorems$|^axioms used: ?$")
if [ -n "$bad" ]; then echo "UNEXPECTED AXIOMS:"; echo "$bad"; exit 1; fi
echo "axioms OK"
