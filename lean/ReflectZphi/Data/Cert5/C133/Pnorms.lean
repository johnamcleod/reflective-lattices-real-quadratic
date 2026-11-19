import ReflectZphi.Data.Cert5.C133.Base

namespace ReflectZphi.Data.Cert5.C133

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨3, 1⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨6, 2⟩, ⟨4, 4⟩, ⟨8, 4⟩, ⟨12, 4⟩, ⟨7, 6⟩], [⟨14, 12⟩], [⟨28, 24⟩]]
theorem nw0 : winRows 1 1 D2 7 1 157 (12 * 0) 12 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 157 (12 * 1) 12 = winCsL.getD 1 [] := by decide +kernel
theorem nw2 : winRows 1 1 D2 7 1 157 (12 * 2) 12 = winCsL.getD 2 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 157 (12 * 3) 0 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 36 157 = normsL :=
  (windowNorms_of_chunks D2 7 1 157 12 3 0 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1, nw2]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C133
