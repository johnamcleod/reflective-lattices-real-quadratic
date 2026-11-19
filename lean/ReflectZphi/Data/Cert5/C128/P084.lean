import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd13_5_0 : subd13_5 [-1] = true := by decide +kernel
theorem subd13_5_1 : subd13_5 [0] = true := by decide +kernel
theorem subd13_5_2 : subd13_5 [1] = true := by decide +kernel
theorem sbd13_5_0 : ∀ q ∈ blkd13_5_0, subd13_5 q = true := by
  unfold blkd13_5_0
  exact List.forall_mem_cons.2 ⟨subd13_5_0, List.forall_mem_cons.2 ⟨subd13_5_1, List.forall_mem_cons.2 ⟨subd13_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd13_6 : ldCheck G d13_6.U d13_6.ms ldd13_6 = true := by decide +kernel
theorem pre_okd13_6 : subPre G cell13 d13_6 = true := by decide +kernel
theorem subd13_6_0 : subd13_6 [-1] = true := by decide +kernel
theorem subd13_6_1 : subd13_6 [0, -2] = true := by decide +kernel
theorem subd13_6_2 : subd13_6 [0, -1] = true := by decide +kernel
theorem subd13_6_3 : subd13_6 [0, 0] = true := by decide +kernel
theorem subd13_6_4 : subd13_6 [0, 1] = true := by decide +kernel
theorem subd13_6_5 : subd13_6 [1] = true := by decide +kernel
theorem sbd13_6_0 : ∀ q ∈ blkd13_6_0, subd13_6 q = true := by
  unfold blkd13_6_0
  exact List.forall_mem_cons.2 ⟨subd13_6_0, List.forall_mem_cons.2 ⟨subd13_6_1, List.forall_mem_cons.2 ⟨subd13_6_2, List.forall_mem_cons.2 ⟨subd13_6_3, List.forall_mem_cons.2 ⟨subd13_6_4, List.forall_mem_cons.2 ⟨subd13_6_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd13_7 : ldCheck G d13_7.U d13_7.ms ldd13_7 = true := by decide +kernel
theorem pre_okd13_7 : subPre G cell13 d13_7 = true := by decide +kernel
theorem subd13_7_0 : subd13_7 [-1] = true := by decide +kernel
theorem subd13_7_1 : subd13_7 [0, -2] = true := by decide +kernel
theorem subd13_7_2 : subd13_7 [0, -1] = true := by decide +kernel
theorem subd13_7_3 : subd13_7 [0, 0] = true := by decide +kernel
theorem subd13_7_4 : subd13_7 [0, 1] = true := by decide +kernel
theorem subd13_7_5 : subd13_7 [1] = true := by decide +kernel
theorem sbd13_7_0 : ∀ q ∈ blkd13_7_0, subd13_7 q = true := by
  unfold blkd13_7_0
  exact List.forall_mem_cons.2 ⟨subd13_7_0, List.forall_mem_cons.2 ⟨subd13_7_1, List.forall_mem_cons.2 ⟨subd13_7_2, List.forall_mem_cons.2 ⟨subd13_7_3, List.forall_mem_cons.2 ⟨subd13_7_4, List.forall_mem_cons.2 ⟨subd13_7_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_nil _⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [-2] = true := by decide +kernel
theorem subd14_1_1 : subd14_1 [-1] = true := by decide +kernel
theorem subd14_1_2 : subd14_1 [0] = true := by decide +kernel
theorem subd14_1_3 : subd14_1 [1] = true := by decide +kernel
theorem subd14_1_4 : subd14_1 [2] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_cons.2 ⟨subd14_1_1, List.forall_mem_cons.2 ⟨subd14_1_2, List.forall_mem_cons.2 ⟨subd14_1_3, List.forall_mem_cons.2 ⟨subd14_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_2 : ldCheck G d14_2.U d14_2.ms ldd14_2 = true := by decide +kernel
theorem pre_okd14_2 : subPre G cell14 d14_2 = true := by decide +kernel
theorem subd14_2_0 : subd14_2 [-2] = true := by decide +kernel
theorem subd14_2_1 : subd14_2 [-1] = true := by decide +kernel
theorem subd14_2_2 : subd14_2 [0] = true := by decide +kernel
theorem subd14_2_3 : subd14_2 [1] = true := by decide +kernel
theorem subd14_2_4 : subd14_2 [2] = true := by decide +kernel
theorem sbd14_2_0 : ∀ q ∈ blkd14_2_0, subd14_2 q = true := by
  unfold blkd14_2_0
  exact List.forall_mem_cons.2 ⟨subd14_2_0, List.forall_mem_cons.2 ⟨subd14_2_1, List.forall_mem_cons.2 ⟨subd14_2_2, List.forall_mem_cons.2 ⟨subd14_2_3, List.forall_mem_cons.2 ⟨subd14_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [-2] = true := by decide +kernel
theorem subd14_3_1 : subd14_3 [-1] = true := by decide +kernel
theorem subd14_3_2 : subd14_3 [0] = true := by decide +kernel
theorem subd14_3_3 : subd14_3 [1] = true := by decide +kernel
theorem subd14_3_4 : subd14_3 [2] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_cons.2 ⟨subd14_3_1, List.forall_mem_cons.2 ⟨subd14_3_2, List.forall_mem_cons.2 ⟨subd14_3_3, List.forall_mem_cons.2 ⟨subd14_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd14_4 : ldCheck G d14_4.U d14_4.ms ldd14_4 = true := by decide +kernel
theorem pre_okd14_4 : subPre G cell14 d14_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
