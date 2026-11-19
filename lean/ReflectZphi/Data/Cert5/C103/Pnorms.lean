import ReflectZphi.Data.Cert5.C103.Base

namespace ReflectZphi.Data.Cert5.C103

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨4, 1⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨8, 2⟩, ⟨9, 7⟩, ⟨18, 14⟩]]
theorem nw0 : winRows 1 1 D2 7 1 104 (19 * 0) 19 = winCsL.getD 0 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 104 (19 * 1) 5 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 24 104 = normsL :=
  (windowNorms_of_chunks D2 7 1 104 19 1 5 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C103
