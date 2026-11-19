import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩, ⟨6, 0⟩, ⟨12, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨3, 3⟩, ⟨6, 3⟩, ⟨4, 4⟩, ⟨8, 4⟩, ⟨6, 6⟩, ⟨12, 6⟩, ⟨12, 12⟩, ⟨24, 12⟩], []]
theorem nw0 : winRows 1 1 D2 7 1 142 (14 * 0) 14 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 142 (14 * 1) 14 = winCsL.getD 1 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 142 (14 * 2) 4 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 32 142 = normsL :=
  (windowNorms_of_chunks D2 7 1 142 14 2 4 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C110
