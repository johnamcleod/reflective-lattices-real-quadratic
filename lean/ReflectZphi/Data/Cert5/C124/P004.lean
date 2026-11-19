import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd2_2 : ldCheck G d2_2.U d2_2.ms ldd2_2 = true := by decide +kernel
theorem pre_okd2_2 : subPre G cell2 d2_2 = true := by decide +kernel
theorem subd2_2_0 : subd2_2 [] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_nil _⟩
theorem ld_okd2_3 : ldCheck G d2_3.U d2_3.ms ldd2_3 = true := by decide +kernel
theorem pre_okd2_3 : subPre G cell2 d2_3 = true := by decide +kernel
theorem subd2_3_0 : subd2_3 [] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_nil _⟩
theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel
theorem subd2_4_0 : subd2_4 [] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_nil _⟩
theorem ld_okd2_5 : ldCheck G d2_5.U d2_5.ms ldd2_5 = true := by decide +kernel
theorem pre_okd2_5 : subPre G cell2 d2_5 = true := by decide +kernel
theorem subd2_5_0 : subd2_5 [] = true := by decide +kernel
theorem sbd2_5_0 : ∀ q ∈ blkd2_5_0, subd2_5 q = true := by
  unfold blkd2_5_0
  exact List.forall_mem_cons.2 ⟨subd2_5_0, List.forall_mem_nil _⟩
theorem ld_okd2_6 : ldCheck G d2_6.U d2_6.ms ldd2_6 = true := by decide +kernel
theorem pre_okd2_6 : subPre G cell2 d2_6 = true := by decide +kernel
theorem subd2_6_0 : subd2_6 [-1] = true := by decide +kernel
theorem subd2_6_1 : subd2_6 [0] = true := by decide +kernel
theorem subd2_6_2 : subd2_6 [1] = true := by decide +kernel
theorem sbd2_6_0 : ∀ q ∈ blkd2_6_0, subd2_6 q = true := by
  unfold blkd2_6_0
  exact List.forall_mem_cons.2 ⟨subd2_6_0, List.forall_mem_cons.2 ⟨subd2_6_1, List.forall_mem_cons.2 ⟨subd2_6_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd2_7 : ldCheck G d2_7.U d2_7.ms ldd2_7 = true := by decide +kernel
theorem pre_okd2_7 : subPre G cell2 d2_7 = true := by decide +kernel
theorem subd2_7_0 : subd2_7 [-2] = true := by decide +kernel
theorem subd2_7_1 : subd2_7 [-1] = true := by decide +kernel
theorem subd2_7_2 : subd2_7 [0] = true := by decide +kernel
theorem subd2_7_3 : subd2_7 [1] = true := by decide +kernel
theorem subd2_7_4 : subd2_7 [2] = true := by decide +kernel
theorem sbd2_7_0 : ∀ q ∈ blkd2_7_0, subd2_7 q = true := by
  unfold blkd2_7_0
  exact List.forall_mem_cons.2 ⟨subd2_7_0, List.forall_mem_cons.2 ⟨subd2_7_1, List.forall_mem_cons.2 ⟨subd2_7_2, List.forall_mem_cons.2 ⟨subd2_7_3, List.forall_mem_cons.2 ⟨subd2_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_8 : ldCheck G d2_8.U d2_8.ms ldd2_8 = true := by decide +kernel
theorem pre_okd2_8 : subPre G cell2 d2_8 = true := by decide +kernel
theorem subd2_8_0 : subd2_8 [-2] = true := by decide +kernel
theorem subd2_8_1 : subd2_8 [-1, -3] = true := by decide +kernel
theorem subd2_8_2 : subd2_8 [-1, -2] = true := by decide +kernel
theorem subd2_8_3 : subd2_8 [-1, -1] = true := by decide +kernel
theorem subd2_8_4 : subd2_8 [-1, 0] = true := by decide +kernel
theorem subd2_8_5 : subd2_8 [-1, 1] = true := by decide +kernel
theorem subd2_8_6 : subd2_8 [0, -3] = true := by decide +kernel
theorem subd2_8_7 : subd2_8 [0, -2] = true := by decide +kernel
theorem subd2_8_8 : subd2_8 [0, -1] = true := by decide +kernel
theorem subd2_8_9 : subd2_8 [0, 0] = true := by decide +kernel
theorem subd2_8_10 : subd2_8 [0, 1] = true := by decide +kernel
theorem subd2_8_11 : subd2_8 [0, 2] = true := by decide +kernel
theorem subd2_8_12 : subd2_8 [1, -2] = true := by decide +kernel
theorem subd2_8_13 : subd2_8 [1, -1] = true := by decide +kernel
theorem subd2_8_14 : subd2_8 [1, 0] = true := by decide +kernel
theorem subd2_8_15 : subd2_8 [1, 1] = true := by decide +kernel
theorem subd2_8_16 : subd2_8 [1, 2] = true := by decide +kernel
theorem subd2_8_17 : subd2_8 [2] = true := by decide +kernel
theorem sbd2_8_0 : ∀ q ∈ blkd2_8_0, subd2_8 q = true := by
  unfold blkd2_8_0
  exact List.forall_mem_cons.2 ⟨subd2_8_0, List.forall_mem_cons.2 ⟨subd2_8_1, List.forall_mem_cons.2 ⟨subd2_8_2, List.forall_mem_cons.2 ⟨subd2_8_3, List.forall_mem_cons.2 ⟨subd2_8_4, List.forall_mem_cons.2 ⟨subd2_8_5, List.forall_mem_cons.2 ⟨subd2_8_6, List.forall_mem_cons.2 ⟨subd2_8_7, List.forall_mem_cons.2 ⟨subd2_8_8, List.forall_mem_cons.2 ⟨subd2_8_9, List.forall_mem_cons.2 ⟨subd2_8_10, List.forall_mem_cons.2 ⟨subd2_8_11, List.forall_mem_cons.2 ⟨subd2_8_12, List.forall_mem_cons.2 ⟨subd2_8_13, List.forall_mem_cons.2 ⟨subd2_8_14, List.forall_mem_cons.2 ⟨subd2_8_15, List.forall_mem_cons.2 ⟨subd2_8_16, List.forall_mem_cons.2 ⟨subd2_8_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd2_9 : ldCheck G d2_9.U d2_9.ms ldd2_9 = true := by decide +kernel
theorem pre_okd2_9 : subPre G cell2 d2_9 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
