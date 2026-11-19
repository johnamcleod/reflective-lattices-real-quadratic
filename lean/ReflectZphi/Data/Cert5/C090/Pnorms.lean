import ReflectZphi.Data.Cert5.C090.Base

namespace ReflectZphi.Data.Cert5.C090

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨5, 1⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨10, 2⟩, ⟨4, 4⟩, ⟨8, 4⟩, ⟨20, 4⟩], [⟨11, 8⟩], [⟨22, 16⟩], [], [⟨44, 32⟩], [], [], []]
theorem nw0 : winRows 1 1 D2 7 1 255 (7 * 0) 7 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 255 (7 * 1) 7 = winCsL.getD 1 [] := by decide +kernel
theorem nw2 : winRows 1 1 D2 7 1 255 (7 * 2) 7 = winCsL.getD 2 [] := by decide +kernel
theorem nw3 : winRows 1 1 D2 7 1 255 (7 * 3) 7 = winCsL.getD 3 [] := by decide +kernel
theorem nw4 : winRows 1 1 D2 7 1 255 (7 * 4) 7 = winCsL.getD 4 [] := by decide +kernel
theorem nw5 : winRows 1 1 D2 7 1 255 (7 * 5) 7 = winCsL.getD 5 [] := by decide +kernel
theorem nw6 : winRows 1 1 D2 7 1 255 (7 * 6) 7 = winCsL.getD 6 [] := by decide +kernel
theorem nw7 : winRows 1 1 D2 7 1 255 (7 * 7) 7 = winCsL.getD 7 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 255 (7 * 8) 1 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 57 255 = normsL :=
  (windowNorms_of_chunks D2 7 1 255 7 8 1 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1, nw2, nw3, nw4, nw5, nw6, nw7]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C090
