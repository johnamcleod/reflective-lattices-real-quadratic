import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨4, 0⟩, ⟨6, 0⟩, ⟨12, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨6, 2⟩, ⟨3, 3⟩, ⟨6, 3⟩, ⟨9, 3⟩], [⟨4, 4⟩, ⟨8, 4⟩, ⟨12, 4⟩, ⟨6, 6⟩, ⟨7, 6⟩, ⟨12, 6⟩, ⟨18, 6⟩], [], [⟨12, 12⟩, ⟨14, 12⟩, ⟨24, 12⟩, ⟨36, 12⟩], [⟨21, 18⟩], [], [⟨28, 24⟩], [], [], [⟨42, 36⟩], [], [], [], [], [], [], [], [], [⟨84, 72⟩], [], [], [], [], [], [], []]
theorem nw0 : winRows 1 1 D2 7 1 471 (4 * 0) 4 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 471 (4 * 1) 4 = winCsL.getD 1 [] := by decide +kernel
theorem nw2 : winRows 1 1 D2 7 1 471 (4 * 2) 4 = winCsL.getD 2 [] := by decide +kernel
theorem nw3 : winRows 1 1 D2 7 1 471 (4 * 3) 4 = winCsL.getD 3 [] := by decide +kernel
theorem nw4 : winRows 1 1 D2 7 1 471 (4 * 4) 4 = winCsL.getD 4 [] := by decide +kernel
theorem nw5 : winRows 1 1 D2 7 1 471 (4 * 5) 4 = winCsL.getD 5 [] := by decide +kernel
theorem nw6 : winRows 1 1 D2 7 1 471 (4 * 6) 4 = winCsL.getD 6 [] := by decide +kernel
theorem nw7 : winRows 1 1 D2 7 1 471 (4 * 7) 4 = winCsL.getD 7 [] := by decide +kernel
theorem nw8 : winRows 1 1 D2 7 1 471 (4 * 8) 4 = winCsL.getD 8 [] := by decide +kernel
theorem nw9 : winRows 1 1 D2 7 1 471 (4 * 9) 4 = winCsL.getD 9 [] := by decide +kernel
theorem nw10 : winRows 1 1 D2 7 1 471 (4 * 10) 4 = winCsL.getD 10 [] := by decide +kernel
theorem nw11 : winRows 1 1 D2 7 1 471 (4 * 11) 4 = winCsL.getD 11 [] := by decide +kernel
theorem nw12 : winRows 1 1 D2 7 1 471 (4 * 12) 4 = winCsL.getD 12 [] := by decide +kernel
theorem nw13 : winRows 1 1 D2 7 1 471 (4 * 13) 4 = winCsL.getD 13 [] := by decide +kernel
theorem nw14 : winRows 1 1 D2 7 1 471 (4 * 14) 4 = winCsL.getD 14 [] := by decide +kernel
theorem nw15 : winRows 1 1 D2 7 1 471 (4 * 15) 4 = winCsL.getD 15 [] := by decide +kernel
theorem nw16 : winRows 1 1 D2 7 1 471 (4 * 16) 4 = winCsL.getD 16 [] := by decide +kernel
theorem nw17 : winRows 1 1 D2 7 1 471 (4 * 17) 4 = winCsL.getD 17 [] := by decide +kernel
theorem nw18 : winRows 1 1 D2 7 1 471 (4 * 18) 4 = winCsL.getD 18 [] := by decide +kernel
theorem nw19 : winRows 1 1 D2 7 1 471 (4 * 19) 4 = winCsL.getD 19 [] := by decide +kernel
theorem nw20 : winRows 1 1 D2 7 1 471 (4 * 20) 4 = winCsL.getD 20 [] := by decide +kernel
theorem nw21 : winRows 1 1 D2 7 1 471 (4 * 21) 4 = winCsL.getD 21 [] := by decide +kernel
theorem nw22 : winRows 1 1 D2 7 1 471 (4 * 22) 4 = winCsL.getD 22 [] := by decide +kernel
theorem nw23 : winRows 1 1 D2 7 1 471 (4 * 23) 4 = winCsL.getD 23 [] := by decide +kernel
theorem nw24 : winRows 1 1 D2 7 1 471 (4 * 24) 4 = winCsL.getD 24 [] := by decide +kernel
theorem nw25 : winRows 1 1 D2 7 1 471 (4 * 25) 4 = winCsL.getD 25 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 471 (4 * 26) 2 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 106 471 = normsL :=
  (windowNorms_of_chunks D2 7 1 471 4 26 2 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1, nw2, nw3, nw4, nw5, nw6, nw7, nw8, nw9, nw10, nw11, nw12, nw13, nw14, nw15, nw16, nw17, nw18, nw19, nw20, nw21, nw22, nw23, nw24, nw25]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C124
