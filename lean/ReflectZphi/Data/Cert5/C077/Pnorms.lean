import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

def winCsL : List (List OK) := [[⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨5, 1⟩, ⟨2, 2⟩, ⟨4, 2⟩, ⟨10, 2⟩, ⟨11, 8⟩]]
theorem nw0 : winRows 1 1 D2 7 1 128 (15 * 0) 15 = winCsL.getD 0 [] := by decide +kernel
theorem nwr : winRows 1 1 D2 7 1 128 (15 * 1) 14 = [⟨22, 16⟩] := by decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 29 128 = normsL :=
  (windowNorms_of_chunks D2 7 1 128 15 1 14 (fun i => winCsL.getD i []) _
    (by intro i hi; interval_cases i; exacts [nw0]) nwr).trans
    (by decide +kernel)

end ReflectZphi.Data.Cert5.C077
