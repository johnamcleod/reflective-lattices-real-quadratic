import Lean

/-!
# Axiom audit

`#audit_axioms P` collects every theorem whose name has the prefix `P` and the axioms they
depend on, and fails with an error if any of them is not one of `propext`,
`Classical.choice`, `Quot.sound`. It is the batch version of `#print axioms`: the
certificate library has thousands of theorems (`ReflectZphi.Data.*`), and a file that runs
`#audit_axioms ReflectZphi.Data` does not compile unless all of them are axiom-clean.

Imported results (`ReflectZphi.Imported`) are hypotheses of the theorems that use them, not
axioms, so they do not appear here.
-/

namespace ReflectZphi.Audit

open Lean Elab Command

/-- The axioms of Lean's standard foundations, the only ones allowed. -/
def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The theorems in the environment whose name has the prefix `p`. -/
def theoremsWithPrefix (env : Environment) (p : Name) : Array Name :=
  env.constants.fold (init := #[]) fun acc nm ci =>
    match ci with
    | .thmInfo _ => if p.isPrefixOf nm then acc.push nm else acc
    | _ => acc

/-- `#audit_axioms P`: every theorem under the prefix `P` uses only the standard axioms. -/
elab "#audit_axioms " pre:ident : command => do
  let env ← getEnv
  let p := pre.getId
  let names := theoremsWithPrefix env p
  if names.isEmpty then
    throwError "#audit_axioms: no theorems with prefix {p}"
  let mut used : NameSet := {}
  let mut bad : Array (Name × Name) := #[]
  for nm in names do
    for a in (← collectAxioms nm) do
      used := used.insert a
      unless standardAxioms.contains a do bad := bad.push (nm, a)
  unless bad.isEmpty do
    throwError "#audit_axioms {p}: non-standard axioms (theorem, axiom): {bad.toList.take 20}"
  logInfo m!"#audit_axioms {p}: {names.size} theorems, axioms used: {used.toList}"

end ReflectZphi.Audit
