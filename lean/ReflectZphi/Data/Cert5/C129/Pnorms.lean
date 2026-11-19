import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨4, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨4, 3⟩, ⟨4, 4⟩, ⟨8, 6⟩, ⟨16, 12⟩]]
theorem nw0 : winRows 1 1 D2 7 1 93 (21 * 0) 21 = winCsL.getD 0 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 93 (21 * 1) 0 = [] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 21 93 = normsL :=
  (windowNorms_of_chunks D2 7 1 93 21 1 0 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C129
