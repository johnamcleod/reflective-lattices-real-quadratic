#!/bin/sh
# Fails if any listed theorem depends on an axiom outside {propext, Classical.choice, Quot.sound}
# (plus the approved imported theorems in ReflectZphi/Imported.lean, none yet).
cd "$(dirname "$0")/.." || exit 1
out=$(lake env lean scripts/CheckAxioms.lean 2>&1) || { echo "$out"; exit 1; }
echo "$out"
bad=$(echo "$out" | tr ',[]' '\n\n\n' | sed 's/^ *//' | grep -v "^$" | grep -v "depends on axioms:" \
      | grep -vx "propext\|Classical.choice\|Quot.sound" | grep -v "does not depend on any axioms")
if [ -n "$bad" ]; then echo "UNEXPECTED AXIOMS:"; echo "$bad"; exit 1; fi
echo "axioms OK"
