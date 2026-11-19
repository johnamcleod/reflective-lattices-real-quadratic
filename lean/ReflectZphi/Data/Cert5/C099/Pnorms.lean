import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨1, 1⟩, ⟨4, 1⟩, ⟨2, 2⟩, ⟨3, 2⟩, ⟨8, 2⟩, ⟨4, 4⟩, ⟨6, 4⟩, ⟨16, 4⟩], [⟨12, 8⟩], [⟨14, 13⟩], [], [⟨28, 26⟩], [], [], [], [⟨56, 52⟩], [], []]
theorem nw0 : winRows 1 1 D2 7 1 306 (6 * 0) 6 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 306 (6 * 1) 6 = winCsL.getD 1 [] := by decide +kernel
theorem nw2 : winRows 1 1 D2 7 1 306 (6 * 2) 6 = winCsL.getD 2 [] := by decide +kernel
theorem nw3 : winRows 1 1 D2 7 1 306 (6 * 3) 6 = winCsL.getD 3 [] := by decide +kernel
theorem nw4 : winRows 1 1 D2 7 1 306 (6 * 4) 6 = winCsL.getD 4 [] := by decide +kernel
theorem nw5 : winRows 1 1 D2 7 1 306 (6 * 5) 6 = winCsL.getD 5 [] := by decide +kernel
theorem nw6 : winRows 1 1 D2 7 1 306 (6 * 6) 6 = winCsL.getD 6 [] := by decide +kernel
theorem nw7 : winRows 1 1 D2 7 1 306 (6 * 7) 6 = winCsL.getD 7 [] := by decide +kernel
theorem nw8 : winRows 1 1 D2 7 1 306 (6 * 8) 6 = winCsL.getD 8 [] := by decide +kernel
theorem nw9 : winRows 1 1 D2 7 1 306 (6 * 9) 6 = winCsL.getD 9 [] := by decide +kernel
theorem nw10 : winRows 1 1 D2 7 1 306 (6 * 10) 6 = winCsL.getD 10 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 306 (6 * 11) 3 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 69 306 = normsL :=
  (windowNorms_of_chunks D2 7 1 306 6 11 3 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1, nw2, nw3, nw4, nw5, nw6, nw7, nw8, nw9, nw10]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C099
