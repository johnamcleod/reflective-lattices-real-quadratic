import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨1, 1⟩, ⟨3, 1⟩, ⟨2, 2⟩, ⟨6, 2⟩, ⟨3, 3⟩, ⟨9, 3⟩, ⟨6, 6⟩, ⟨18, 6⟩]]
theorem nw0 : winRows 1 1 D2 7 1 106 (18 * 0) 18 = winCsL.getD 0 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 106 (18 * 1) 6 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 24 106 = normsL :=
  (windowNorms_of_chunks D2 7 1 106 18 1 6 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C096
