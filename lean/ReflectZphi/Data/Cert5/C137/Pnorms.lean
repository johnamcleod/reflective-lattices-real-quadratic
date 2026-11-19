import ReflectZphi.Data.Cert5.C137.Base

namespace ReflectZphi.Data.Cert5.C137

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨1, 1⟩, ⟨5, 1⟩, ⟨2, 2⟩, ⟨10, 2⟩, ⟨4, 4⟩, ⟨20, 4⟩]]
theorem nw0 : winRows 1 1 D2 7 1 114 (17 * 0) 17 = winCsL.getD 0 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 114 (17 * 1) 9 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 26 114 = normsL :=
  (windowNorms_of_chunks D2 7 1 114 17 1 9 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C137
