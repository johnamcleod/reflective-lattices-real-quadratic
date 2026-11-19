import ReflectZphi.Data.Cert5.C131.Base

namespace ReflectZphi.Data.Cert5.C131

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := []
theorem nwr : winRows 1 1 D2 7 1 90 (22 * 0) 20 = [⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨8, 1⟩, ⟨2, 2⟩, ⟨16, 2⟩] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 20 90 = normsL :=
  (windowNorms_of_chunks D2 7 1 90 22 0 20 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C131
