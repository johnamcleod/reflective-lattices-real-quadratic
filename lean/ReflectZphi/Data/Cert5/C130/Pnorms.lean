import ReflectZphi.Data.Cert5.C130.Base

namespace ReflectZphi.Data.Cert5.C130

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨5, 2⟩, ⟨10, 4⟩, ⟨12, 11⟩], [⟨24, 22⟩]]
theorem nw0 : winRows 1 1 D2 7 1 132 (15 * 0) 15 = winCsL.getD 0 [] := by decide +kernel
theorem nw1 : winRows 1 1 D2 7 1 132 (15 * 1) 15 = winCsL.getD 1 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 132 (15 * 2) 0 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 30 132 = normsL :=
  (windowNorms_of_chunks D2 7 1 132 15 2 0 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0, nw1]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C130
