import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [-2] = true := by decide +kernel
theorem subd4_3_1 : subd4_3 [-1] = true := by decide +kernel
theorem subd4_3_2 : subd4_3 [0, -3] = true := by decide +kernel
theorem subd4_3_3 : subd4_3 [0, -2] = true := by decide +kernel
theorem subd4_3_4 : subd4_3 [0, -1] = true := by decide +kernel
theorem subd4_3_5 : subd4_3 [0, 0] = true := by decide +kernel
theorem subd4_3_6 : subd4_3 [0, 1] = true := by decide +kernel
theorem subd4_3_7 : subd4_3 [0, 2] = true := by decide +kernel
theorem subd4_3_8 : subd4_3 [1] = true := by decide +kernel
theorem subd4_3_9 : subd4_3 [2] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_cons.2 ⟨subd4_3_1, List.forall_mem_cons.2 ⟨subd4_3_2, List.forall_mem_cons.2 ⟨subd4_3_3, List.forall_mem_cons.2 ⟨subd4_3_4, List.forall_mem_cons.2 ⟨subd4_3_5, List.forall_mem_cons.2 ⟨subd4_3_6, List.forall_mem_cons.2 ⟨subd4_3_7, List.forall_mem_cons.2 ⟨subd4_3_8, List.forall_mem_cons.2 ⟨subd4_3_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [-2, -4] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [-2, -3] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [-2, -2] = true := by decide +kernel
theorem subd4_4_3 : subd4_4 [-2, -1] = true := by decide +kernel
theorem subd4_4_4 : subd4_4 [-2, 0] = true := by decide +kernel
theorem subd4_4_5 : subd4_4 [-2, 1] = true := by decide +kernel
theorem subd4_4_6 : subd4_4 [-1, -4] = true := by decide +kernel
theorem subd4_4_7 : subd4_4 [-1, -3] = true := by decide +kernel
theorem subd4_4_8 : subd4_4 [-1, -2] = true := by decide +kernel
theorem subd4_4_9 : subd4_4 [-1, -1] = true := by decide +kernel
theorem subd4_4_10 : subd4_4 [-1, 0] = true := by decide +kernel
theorem subd4_4_11 : subd4_4 [-1, 1] = true := by decide +kernel
theorem subd4_4_12 : subd4_4 [-1, 2] = true := by decide +kernel
theorem subd4_4_13 : subd4_4 [0, -4] = true := by decide +kernel
theorem subd4_4_14 : subd4_4 [0, -3] = true := by decide +kernel
theorem subd4_4_15 : subd4_4 [0, -2] = true := by decide +kernel
theorem subd4_4_16 : subd4_4 [0, -1] = true := by decide +kernel
theorem subd4_4_17 : subd4_4 [0, 0] = true := by decide +kernel
theorem subd4_4_18 : subd4_4 [0, 1] = true := by decide +kernel
theorem subd4_4_19 : subd4_4 [0, 2] = true := by decide +kernel
theorem subd4_4_20 : subd4_4 [0, 3] = true := by decide +kernel
theorem subd4_4_21 : subd4_4 [1, -3] = true := by decide +kernel
theorem subd4_4_22 : subd4_4 [1, -2] = true := by decide +kernel
theorem subd4_4_23 : subd4_4 [1, -1] = true := by decide +kernel
theorem subd4_4_24 : subd4_4 [1, 0] = true := by decide +kernel
theorem subd4_4_25 : subd4_4 [1, 1] = true := by decide +kernel
theorem subd4_4_26 : subd4_4 [1, 2] = true := by decide +kernel
theorem subd4_4_27 : subd4_4 [1, 3] = true := by decide +kernel
theorem subd4_4_28 : subd4_4 [2, -2] = true := by decide +kernel
theorem subd4_4_29 : subd4_4 [2, -1] = true := by decide +kernel
theorem subd4_4_30 : subd4_4 [2, 0] = true := by decide +kernel
theorem subd4_4_31 : subd4_4 [2, 1] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_cons.2 ⟨subd4_4_3, List.forall_mem_cons.2 ⟨subd4_4_4, List.forall_mem_cons.2 ⟨subd4_4_5, List.forall_mem_cons.2 ⟨subd4_4_6, List.forall_mem_cons.2 ⟨subd4_4_7, List.forall_mem_cons.2 ⟨subd4_4_8, List.forall_mem_cons.2 ⟨subd4_4_9, List.forall_mem_cons.2 ⟨subd4_4_10, List.forall_mem_cons.2 ⟨subd4_4_11, List.forall_mem_cons.2 ⟨subd4_4_12, List.forall_mem_cons.2 ⟨subd4_4_13, List.forall_mem_cons.2 ⟨subd4_4_14, List.forall_mem_cons.2 ⟨subd4_4_15, List.forall_mem_cons.2 ⟨subd4_4_16, List.forall_mem_cons.2 ⟨subd4_4_17, List.forall_mem_cons.2 ⟨subd4_4_18, List.forall_mem_cons.2 ⟨subd4_4_19, List.forall_mem_cons.2 ⟨subd4_4_20, List.forall_mem_cons.2 ⟨subd4_4_21, List.forall_mem_cons.2 ⟨subd4_4_22, List.forall_mem_cons.2 ⟨subd4_4_23, List.forall_mem_cons.2 ⟨subd4_4_24, List.forall_mem_cons.2 ⟨subd4_4_25, List.forall_mem_cons.2 ⟨subd4_4_26, List.forall_mem_cons.2 ⟨subd4_4_27, List.forall_mem_cons.2 ⟨subd4_4_28, List.forall_mem_cons.2 ⟨subd4_4_29, List.forall_mem_cons.2 ⟨subd4_4_30, List.forall_mem_cons.2 ⟨subd4_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_4_32 : subd4_4 [2, 2] = true := by decide +kernel
theorem subd4_4_33 : subd4_4 [2, 3] = true := by decide +kernel
theorem sbd4_4_1 : ∀ q ∈ blkd4_4_1, subd4_4 q = true := by
  unfold blkd4_4_1
  exact List.forall_mem_cons.2 ⟨subd4_4_32, List.forall_mem_cons.2 ⟨subd4_4_33, List.forall_mem_nil _⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-3] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-2, -5] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-2, -4] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-2, -3] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [-2, -2] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [-2, -1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [-2, 0] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [-2, 1] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [-2, 2] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [-1, -5] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [-1, -4] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [-1, -3] = true := by decide +kernel
theorem subd5_0_12 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_13 : subd5_0 [-1, -1] = true := by decide +kernel
theorem subd5_0_14 : subd5_0 [-1, 0] = true := by decide +kernel
theorem subd5_0_15 : subd5_0 [-1, 1] = true := by decide +kernel
theorem subd5_0_16 : subd5_0 [-1, 2] = true := by decide +kernel
theorem subd5_0_17 : subd5_0 [-1, 3] = true := by decide +kernel
theorem subd5_0_18 : subd5_0 [0, -5] = true := by decide +kernel
theorem subd5_0_19 : subd5_0 [0, -4] = true := by decide +kernel
theorem subd5_0_20 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_21 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_22 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_23 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_24 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_25 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_26 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_27 : subd5_0 [0, 4] = true := by decide +kernel
theorem subd5_0_28 : subd5_0 [1, -4] = true := by decide +kernel
theorem subd5_0_29 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_30 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_31 : subd5_0 [1, -1] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_cons.2 ⟨subd5_0_12, List.forall_mem_cons.2 ⟨subd5_0_13, List.forall_mem_cons.2 ⟨subd5_0_14, List.forall_mem_cons.2 ⟨subd5_0_15, List.forall_mem_cons.2 ⟨subd5_0_16, List.forall_mem_cons.2 ⟨subd5_0_17, List.forall_mem_cons.2 ⟨subd5_0_18, List.forall_mem_cons.2 ⟨subd5_0_19, List.forall_mem_cons.2 ⟨subd5_0_20, List.forall_mem_cons.2 ⟨subd5_0_21, List.forall_mem_cons.2 ⟨subd5_0_22, List.forall_mem_cons.2 ⟨subd5_0_23, List.forall_mem_cons.2 ⟨subd5_0_24, List.forall_mem_cons.2 ⟨subd5_0_25, List.forall_mem_cons.2 ⟨subd5_0_26, List.forall_mem_cons.2 ⟨subd5_0_27, List.forall_mem_cons.2 ⟨subd5_0_28, List.forall_mem_cons.2 ⟨subd5_0_29, List.forall_mem_cons.2 ⟨subd5_0_30, List.forall_mem_cons.2 ⟨subd5_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_32 : subd5_0 [1, 0] = true := by decide +kernel
theorem subd5_0_33 : subd5_0 [1, 1] = true := by decide +kernel
theorem subd5_0_34 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_35 : subd5_0 [1, 3] = true := by decide +kernel
theorem subd5_0_36 : subd5_0 [1, 4] = true := by decide +kernel
theorem subd5_0_37 : subd5_0 [2, -3] = true := by decide +kernel
theorem subd5_0_38 : subd5_0 [2, -2] = true := by decide +kernel
theorem subd5_0_39 : subd5_0 [2, -1] = true := by decide +kernel
theorem subd5_0_40 : subd5_0 [2, 0] = true := by decide +kernel
theorem subd5_0_41 : subd5_0 [2, 1] = true := by decide +kernel
theorem subd5_0_42 : subd5_0 [2, 2] = true := by decide +kernel
theorem subd5_0_43 : subd5_0 [2, 3] = true := by decide +kernel
theorem subd5_0_44 : subd5_0 [2, 4] = true := by decide +kernel
theorem subd5_0_45 : subd5_0 [3] = true := by decide +kernel
theorem sbd5_0_1 : ∀ q ∈ blkd5_0_1, subd5_0 q = true := by
  unfold blkd5_0_1
  exact List.forall_mem_cons.2 ⟨subd5_0_32, List.forall_mem_cons.2 ⟨subd5_0_33, List.forall_mem_cons.2 ⟨subd5_0_34, List.forall_mem_cons.2 ⟨subd5_0_35, List.forall_mem_cons.2 ⟨subd5_0_36, List.forall_mem_cons.2 ⟨subd5_0_37, List.forall_mem_cons.2 ⟨subd5_0_38, List.forall_mem_cons.2 ⟨subd5_0_39, List.forall_mem_cons.2 ⟨subd5_0_40, List.forall_mem_cons.2 ⟨subd5_0_41, List.forall_mem_cons.2 ⟨subd5_0_42, List.forall_mem_cons.2 ⟨subd5_0_43, List.forall_mem_cons.2 ⟨subd5_0_44, List.forall_mem_cons.2 ⟨subd5_0_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C110
