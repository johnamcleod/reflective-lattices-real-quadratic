import ReflectZphi.Data.Cert5.C118.Base

namespace ReflectZphi.Data.Cert5.C118

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨3, 2⟩, ⟨4, 3⟩, ⟨6, 4⟩, ⟨13, 5⟩, ⟨8, 6⟩, ⟨26, 10⟩], []]
theorem nw0 : winRows 1 1 D2 7 1 153 (13 * 0) 13 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 153 (13 * 1) 13 = winCsL.getD 1 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 153 (13 * 2) 9 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 35 153 = normsL :=
  (windowNorms_of_chunks D2 7 1 153 13 2 9 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C118
