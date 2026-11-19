import ReflectZphi.Data.Cert5.C141.Base

namespace ReflectZphi.Data.Cert5.C141

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨3, 1⟩, ⟨2, 2⟩, ⟨5, 2⟩, ⟨6, 2⟩, ⟨10, 4⟩], [⟨17, 13⟩], [⟨34, 26⟩], []]
theorem nw0 : winRows 1 1 D2 7 1 196 (10 * 0) 10 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 196 (10 * 1) 10 = winCsL.getD 1 [] := by decide +kernel
theorem nw2 : winRows 1 1 D2 7 1 196 (10 * 2) 10 = winCsL.getD 2 [] := by decide +kernel
theorem nw3 : winRows 1 1 D2 7 1 196 (10 * 3) 10 = winCsL.getD 3 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 196 (10 * 4) 4 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 44 196 = normsL :=
  (windowNorms_of_chunks D2 7 1 196 10 4 4 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1, nw2, nw3]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C141
