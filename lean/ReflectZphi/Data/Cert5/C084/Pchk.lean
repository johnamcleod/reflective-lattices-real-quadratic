import ReflectZphi.Data.Cert5.C084.Base

namespace ReflectZphi.Data.Cert5.C084

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem poly_ok : polyCheck G n f rs Ps Xs cf = true := by decide +kernel
theorem adm_ok : admCheck G f = true := by decide +kernel
theorem basis_ok : basisCheck G f = true := by decide +kernel
theorem win_ok : winCheck G D2 u uinv 7 1 19 83 = true := by
  decide +kernel
theorem norms_eq : windowNorms 1 1 D2 7 1 19 83 = normsL := by
  decide +kernel
theorem chain_ok : chainCheck G f n Ps N Bs idx nc cells seg = true := by decide +kernel

end ReflectZphi.Data.Cert5.C084
