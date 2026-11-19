import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_5_0 : subd4_5 [-3] = true := by decide +kernel
theorem subd4_5_1 : subd4_5 [-2, -3] = true := by decide +kernel
theorem subd4_5_2 : subd4_5 [-2, -2] = true := by decide +kernel
theorem subd4_5_3 : subd4_5 [-2, -1] = true := by decide +kernel
theorem subd4_5_4 : subd4_5 [-2, 0] = true := by decide +kernel
theorem subd4_5_5 : subd4_5 [-2, 1] = true := by decide +kernel
theorem subd4_5_6 : subd4_5 [-2, 2] = true := by decide +kernel
theorem subd4_5_7 : subd4_5 [-1, -4] = true := by decide +kernel
theorem subd4_5_8 : subd4_5 [-1, -3] = true := by decide +kernel
theorem subd4_5_9 : subd4_5 [-1, -2] = true := by decide +kernel
theorem subd4_5_10 : subd4_5 [-1, -1] = true := by decide +kernel
theorem subd4_5_11 : subd4_5 [-1, 0] = true := by decide +kernel
theorem subd4_5_12 : subd4_5 [-1, 1] = true := by decide +kernel
theorem subd4_5_13 : subd4_5 [-1, 2] = true := by decide +kernel
theorem subd4_5_14 : subd4_5 [-1, 3] = true := by decide +kernel
theorem subd4_5_15 : subd4_5 [0, -4] = true := by decide +kernel
theorem subd4_5_16 : subd4_5 [0, -3] = true := by decide +kernel
theorem subd4_5_17 : subd4_5 [0, -2] = true := by decide +kernel
theorem subd4_5_18 : subd4_5 [0, -1] = true := by decide +kernel
theorem subd4_5_19 : subd4_5 [0, 0] = true := by decide +kernel
theorem subd4_5_20 : subd4_5 [0, 1] = true := by decide +kernel
theorem subd4_5_21 : subd4_5 [0, 2] = true := by decide +kernel
theorem subd4_5_22 : subd4_5 [0, 3] = true := by decide +kernel
theorem subd4_5_23 : subd4_5 [1, -4] = true := by decide +kernel
theorem subd4_5_24 : subd4_5 [1, -3] = true := by decide +kernel
theorem subd4_5_25 : subd4_5 [1, -2] = true := by decide +kernel
theorem subd4_5_26 : subd4_5 [1, -1] = true := by decide +kernel
theorem subd4_5_27 : subd4_5 [1, 0] = true := by decide +kernel
theorem subd4_5_28 : subd4_5 [1, 1] = true := by decide +kernel
theorem subd4_5_29 : subd4_5 [1, 2] = true := by decide +kernel
theorem subd4_5_30 : subd4_5 [1, 3] = true := by decide +kernel
theorem subd4_5_31 : subd4_5 [2, -3] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_cons.2 ⟨subd4_5_1, List.forall_mem_cons.2 ⟨subd4_5_2, List.forall_mem_cons.2 ⟨subd4_5_3, List.forall_mem_cons.2 ⟨subd4_5_4, List.forall_mem_cons.2 ⟨subd4_5_5, List.forall_mem_cons.2 ⟨subd4_5_6, List.forall_mem_cons.2 ⟨subd4_5_7, List.forall_mem_cons.2 ⟨subd4_5_8, List.forall_mem_cons.2 ⟨subd4_5_9, List.forall_mem_cons.2 ⟨subd4_5_10, List.forall_mem_cons.2 ⟨subd4_5_11, List.forall_mem_cons.2 ⟨subd4_5_12, List.forall_mem_cons.2 ⟨subd4_5_13, List.forall_mem_cons.2 ⟨subd4_5_14, List.forall_mem_cons.2 ⟨subd4_5_15, List.forall_mem_cons.2 ⟨subd4_5_16, List.forall_mem_cons.2 ⟨subd4_5_17, List.forall_mem_cons.2 ⟨subd4_5_18, List.forall_mem_cons.2 ⟨subd4_5_19, List.forall_mem_cons.2 ⟨subd4_5_20, List.forall_mem_cons.2 ⟨subd4_5_21, List.forall_mem_cons.2 ⟨subd4_5_22, List.forall_mem_cons.2 ⟨subd4_5_23, List.forall_mem_cons.2 ⟨subd4_5_24, List.forall_mem_cons.2 ⟨subd4_5_25, List.forall_mem_cons.2 ⟨subd4_5_26, List.forall_mem_cons.2 ⟨subd4_5_27, List.forall_mem_cons.2 ⟨subd4_5_28, List.forall_mem_cons.2 ⟨subd4_5_29, List.forall_mem_cons.2 ⟨subd4_5_30, List.forall_mem_cons.2 ⟨subd4_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_5_32 : subd4_5 [2, -2] = true := by decide +kernel
theorem subd4_5_33 : subd4_5 [2, -1] = true := by decide +kernel
theorem subd4_5_34 : subd4_5 [2, 0] = true := by decide +kernel
theorem subd4_5_35 : subd4_5 [2, 1] = true := by decide +kernel
theorem subd4_5_36 : subd4_5 [2, 2] = true := by decide +kernel
theorem subd4_5_37 : subd4_5 [3] = true := by decide +kernel
theorem sbd4_5_1 : ∀ q ∈ blkd4_5_1, subd4_5 q = true := by
  unfold blkd4_5_1
  exact List.forall_mem_cons.2 ⟨subd4_5_32, List.forall_mem_cons.2 ⟨subd4_5_33, List.forall_mem_cons.2 ⟨subd4_5_34, List.forall_mem_cons.2 ⟨subd4_5_35, List.forall_mem_cons.2 ⟨subd4_5_36, List.forall_mem_cons.2 ⟨subd4_5_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [-1] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [0] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [1] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [-2] = true := by decide +kernel
theorem subd4_7_1 : subd4_7 [-1] = true := by decide +kernel
theorem subd4_7_2 : subd4_7 [0] = true := by decide +kernel
theorem subd4_7_3 : subd4_7 [1] = true := by decide +kernel
theorem subd4_7_4 : subd4_7 [2] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_cons.2 ⟨subd4_7_1, List.forall_mem_cons.2 ⟨subd4_7_2, List.forall_mem_cons.2 ⟨subd4_7_3, List.forall_mem_cons.2 ⟨subd4_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-2] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-1] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [0] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [2] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-1] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [0] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [1] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C122
