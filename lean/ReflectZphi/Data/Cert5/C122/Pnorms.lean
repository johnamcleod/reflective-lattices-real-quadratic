import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨6, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨6, 2⟩, ⟨3, 3⟩, ⟨6, 3⟩, ⟨9, 3⟩, ⟨6, 6⟩, ⟨7, 6⟩, ⟨12, 6⟩, ⟨18, 6⟩], [⟨14, 12⟩], [⟨21, 18⟩], [], [⟨42, 36⟩], []]
theorem nw0 : winRows 1 1 D2 7 1 236 (8 * 0) 8 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 236 (8 * 1) 8 = winCsL.getD 1 [] := by decide +kernel
theorem nw2 : winRows 1 1 D2 7 1 236 (8 * 2) 8 = winCsL.getD 2 [] := by decide +kernel
theorem nw3 : winRows 1 1 D2 7 1 236 (8 * 3) 8 = winCsL.getD 3 [] := by decide +kernel
theorem nw4 : winRows 1 1 D2 7 1 236 (8 * 4) 8 = winCsL.getD 4 [] := by decide +kernel
theorem nw5 : winRows 1 1 D2 7 1 236 (8 * 5) 8 = winCsL.getD 5 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 236 (8 * 6) 5 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 53 236 = normsL :=
  (windowNorms_of_chunks D2 7 1 236 8 6 5 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1, nw2, nw3, nw4, nw5]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C122
