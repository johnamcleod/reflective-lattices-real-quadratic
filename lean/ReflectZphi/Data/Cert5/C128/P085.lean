import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_4_0 : subd14_4 [-2] = true := by decide +kernel
theorem subd14_4_1 : subd14_4 [-1] = true := by decide +kernel
theorem subd14_4_2 : subd14_4 [0] = true := by decide +kernel
theorem subd14_4_3 : subd14_4 [1] = true := by decide +kernel
theorem subd14_4_4 : subd14_4 [2] = true := by decide +kernel
theorem sbd14_4_0 : ∀ q ∈ blkd14_4_0, subd14_4 q = true := by
  unfold blkd14_4_0
  exact List.forall_mem_cons.2 ⟨subd14_4_0, List.forall_mem_cons.2 ⟨subd14_4_1, List.forall_mem_cons.2 ⟨subd14_4_2, List.forall_mem_cons.2 ⟨subd14_4_3, List.forall_mem_cons.2 ⟨subd14_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_5 : ldCheck G d14_5.U d14_5.ms ldd14_5 = true := by decide +kernel
theorem pre_okd14_5 : subPre G cell14 d14_5 = true := by decide +kernel
theorem subd14_5_0 : subd14_5 [-2] = true := by decide +kernel
theorem subd14_5_1 : subd14_5 [-1] = true := by decide +kernel
theorem subd14_5_2 : subd14_5 [0] = true := by decide +kernel
theorem subd14_5_3 : subd14_5 [1] = true := by decide +kernel
theorem subd14_5_4 : subd14_5 [2] = true := by decide +kernel
theorem sbd14_5_0 : ∀ q ∈ blkd14_5_0, subd14_5 q = true := by
  unfold blkd14_5_0
  exact List.forall_mem_cons.2 ⟨subd14_5_0, List.forall_mem_cons.2 ⟨subd14_5_1, List.forall_mem_cons.2 ⟨subd14_5_2, List.forall_mem_cons.2 ⟨subd14_5_3, List.forall_mem_cons.2 ⟨subd14_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_6 : ldCheck G d14_6.U d14_6.ms ldd14_6 = true := by decide +kernel
theorem pre_okd14_6 : subPre G cell14 d14_6 = true := by decide +kernel
theorem subd14_6_0 : subd14_6 [-1] = true := by decide +kernel
theorem subd14_6_1 : subd14_6 [0, -2] = true := by decide +kernel
theorem subd14_6_2 : subd14_6 [0, -1] = true := by decide +kernel
theorem subd14_6_3 : subd14_6 [0, 0] = true := by decide +kernel
theorem subd14_6_4 : subd14_6 [0, 1] = true := by decide +kernel
theorem subd14_6_5 : subd14_6 [1] = true := by decide +kernel
theorem sbd14_6_0 : ∀ q ∈ blkd14_6_0, subd14_6 q = true := by
  unfold blkd14_6_0
  exact List.forall_mem_cons.2 ⟨subd14_6_0, List.forall_mem_cons.2 ⟨subd14_6_1, List.forall_mem_cons.2 ⟨subd14_6_2, List.forall_mem_cons.2 ⟨subd14_6_3, List.forall_mem_cons.2 ⟨subd14_6_4, List.forall_mem_cons.2 ⟨subd14_6_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd14_7 : ldCheck G d14_7.U d14_7.ms ldd14_7 = true := by decide +kernel
theorem pre_okd14_7 : subPre G cell14 d14_7 = true := by decide +kernel
theorem subd14_7_0 : subd14_7 [-1] = true := by decide +kernel
theorem subd14_7_1 : subd14_7 [0] = true := by decide +kernel
theorem subd14_7_2 : subd14_7 [1] = true := by decide +kernel
theorem sbd14_7_0 : ∀ q ∈ blkd14_7_0, subd14_7 q = true := by
  unfold blkd14_7_0
  exact List.forall_mem_cons.2 ⟨subd14_7_0, List.forall_mem_cons.2 ⟨subd14_7_1, List.forall_mem_cons.2 ⟨subd14_7_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
