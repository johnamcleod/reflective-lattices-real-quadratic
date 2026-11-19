import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨19, 2⟩, ⟨38, 4⟩, ⟨8, 5⟩], [⟨16, 10⟩], [], [], []]
theorem nw0 : winRows 1 1 D2 7 1 211 (9 * 0) 9 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 211 (9 * 1) 9 = winCsL.getD 1 [] := by decide +kernel
theorem nw2 : winRows 1 1 D2 7 1 211 (9 * 2) 9 = winCsL.getD 2 [] := by decide +kernel
theorem nw3 : winRows 1 1 D2 7 1 211 (9 * 3) 9 = winCsL.getD 3 [] := by decide +kernel
theorem nw4 : winRows 1 1 D2 7 1 211 (9 * 4) 9 = winCsL.getD 4 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 211 (9 * 5) 3 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 48 211 = normsL :=
  (windowNorms_of_chunks D2 7 1 211 9 5 3 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1, nw2, nw3, nw4]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C142
