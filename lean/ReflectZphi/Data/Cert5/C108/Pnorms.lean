import ReflectZphi.Data.Cert5.C108.Base

namespace ReflectZphi.Data.Cert5.C108

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩, ⟨6, 0⟩, ⟨12, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨5, 2⟩, ⟨3, 3⟩, ⟨4, 4⟩, ⟨10, 4⟩], [⟨6, 6⟩, ⟨15, 6⟩, ⟨20, 8⟩], [⟨12, 12⟩, ⟨30, 12⟩], [], [⟨60, 24⟩], [], [], [], [], [], [], [], [], [], [], []]
theorem nw0 : winRows 1 1 D2 7 1 354 (5 * 0) 5 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 354 (5 * 1) 5 = winCsL.getD 1 [] := by decide +kernel
theorem nw2 : winRows 1 1 D2 7 1 354 (5 * 2) 5 = winCsL.getD 2 [] := by decide +kernel
theorem nw3 : winRows 1 1 D2 7 1 354 (5 * 3) 5 = winCsL.getD 3 [] := by decide +kernel
theorem nw4 : winRows 1 1 D2 7 1 354 (5 * 4) 5 = winCsL.getD 4 [] := by decide +kernel
theorem nw5 : winRows 1 1 D2 7 1 354 (5 * 5) 5 = winCsL.getD 5 [] := by decide +kernel
theorem nw6 : winRows 1 1 D2 7 1 354 (5 * 6) 5 = winCsL.getD 6 [] := by decide +kernel
theorem nw7 : winRows 1 1 D2 7 1 354 (5 * 7) 5 = winCsL.getD 7 [] := by decide +kernel
theorem nw8 : winRows 1 1 D2 7 1 354 (5 * 8) 5 = winCsL.getD 8 [] := by decide +kernel
theorem nw9 : winRows 1 1 D2 7 1 354 (5 * 9) 5 = winCsL.getD 9 [] := by decide +kernel
theorem nw10 : winRows 1 1 D2 7 1 354 (5 * 10) 5 = winCsL.getD 10 [] := by decide +kernel
theorem nw11 : winRows 1 1 D2 7 1 354 (5 * 11) 5 = winCsL.getD 11 [] := by decide +kernel
theorem nw12 : winRows 1 1 D2 7 1 354 (5 * 12) 5 = winCsL.getD 12 [] := by decide +kernel
theorem nw13 : winRows 1 1 D2 7 1 354 (5 * 13) 5 = winCsL.getD 13 [] := by decide +kernel
theorem nw14 : winRows 1 1 D2 7 1 354 (5 * 14) 5 = winCsL.getD 14 [] := by decide +kernel
theorem nw15 : winRows 1 1 D2 7 1 354 (5 * 15) 5 = winCsL.getD 15 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 354 (5 * 16) 0 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 80 354 = normsL :=
  (windowNorms_of_chunks D2 7 1 354 5 16 0 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1, nw2, nw3, nw4, nw5, nw6, nw7, nw8, nw9, nw10, nw11, nw12, nw13, nw14, nw15]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C108
