import ReflectZphi.Data.Cert5.C061.Base

namespace ReflectZphi.Data.Cert5.C061

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_0_0 : subd4_0 [-3] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [-2, -3] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [-2, -2] = true := by decide +kernel
theorem subd4_0_3 : subd4_0 [-2, -1] = true := by decide +kernel
theorem subd4_0_4 : subd4_0 [-2, 0] = true := by decide +kernel
theorem subd4_0_5 : subd4_0 [-2, 1] = true := by decide +kernel
theorem subd4_0_6 : subd4_0 [-2, 2] = true := by decide +kernel
theorem subd4_0_7 : subd4_0 [-2, 3] = true := by decide +kernel
theorem subd4_0_8 : subd4_0 [-1, -4] = true := by decide +kernel
theorem subd4_0_9 : subd4_0 [-1, -3] = true := by decide +kernel
theorem subd4_0_10 : subd4_0 [-1, -2] = true := by decide +kernel
theorem subd4_0_11 : subd4_0 [-1, -1] = true := by decide +kernel
theorem subd4_0_12 : subd4_0 [-1, 0] = true := by decide +kernel
theorem subd4_0_13 : subd4_0 [-1, 1] = true := by decide +kernel
theorem subd4_0_14 : subd4_0 [-1, 2] = true := by decide +kernel
theorem subd4_0_15 : subd4_0 [-1, 3] = true := by decide +kernel
theorem subd4_0_16 : subd4_0 [-1, 4] = true := by decide +kernel
theorem subd4_0_17 : subd4_0 [0, -4] = true := by decide +kernel
theorem subd4_0_18 : subd4_0 [0, -3] = true := by decide +kernel
theorem subd4_0_19 : subd4_0 [0, -2] = true := by decide +kernel
theorem subd4_0_20 : subd4_0 [0, -1] = true := by decide +kernel
theorem subd4_0_21 : subd4_0 [0, 0] = true := by decide +kernel
theorem subd4_0_22 : subd4_0 [0, 1] = true := by decide +kernel
theorem subd4_0_23 : subd4_0 [0, 2] = true := by decide +kernel
theorem subd4_0_24 : subd4_0 [0, 3] = true := by decide +kernel
theorem subd4_0_25 : subd4_0 [1, -5] = true := by decide +kernel
theorem subd4_0_26 : subd4_0 [1, -4] = true := by decide +kernel
theorem subd4_0_27 : subd4_0 [1, -3] = true := by decide +kernel
theorem subd4_0_28 : subd4_0 [1, -2] = true := by decide +kernel
theorem subd4_0_29 : subd4_0 [1, -1] = true := by decide +kernel
theorem subd4_0_30 : subd4_0 [1, 0] = true := by decide +kernel
theorem subd4_0_31 : subd4_0 [1, 1] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_cons.2 ⟨subd4_0_3, List.forall_mem_cons.2 ⟨subd4_0_4, List.forall_mem_cons.2 ⟨subd4_0_5, List.forall_mem_cons.2 ⟨subd4_0_6, List.forall_mem_cons.2 ⟨subd4_0_7, List.forall_mem_cons.2 ⟨subd4_0_8, List.forall_mem_cons.2 ⟨subd4_0_9, List.forall_mem_cons.2 ⟨subd4_0_10, List.forall_mem_cons.2 ⟨subd4_0_11, List.forall_mem_cons.2 ⟨subd4_0_12, List.forall_mem_cons.2 ⟨subd4_0_13, List.forall_mem_cons.2 ⟨subd4_0_14, List.forall_mem_cons.2 ⟨subd4_0_15, List.forall_mem_cons.2 ⟨subd4_0_16, List.forall_mem_cons.2 ⟨subd4_0_17, List.forall_mem_cons.2 ⟨subd4_0_18, List.forall_mem_cons.2 ⟨subd4_0_19, List.forall_mem_cons.2 ⟨subd4_0_20, List.forall_mem_cons.2 ⟨subd4_0_21, List.forall_mem_cons.2 ⟨subd4_0_22, List.forall_mem_cons.2 ⟨subd4_0_23, List.forall_mem_cons.2 ⟨subd4_0_24, List.forall_mem_cons.2 ⟨subd4_0_25, List.forall_mem_cons.2 ⟨subd4_0_26, List.forall_mem_cons.2 ⟨subd4_0_27, List.forall_mem_cons.2 ⟨subd4_0_28, List.forall_mem_cons.2 ⟨subd4_0_29, List.forall_mem_cons.2 ⟨subd4_0_30, List.forall_mem_cons.2 ⟨subd4_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_0_32 : subd4_0 [1, 2] = true := by decide +kernel
theorem subd4_0_33 : subd4_0 [1, 3] = true := by decide +kernel
theorem subd4_0_34 : subd4_0 [2, -4] = true := by decide +kernel
theorem subd4_0_35 : subd4_0 [2, -3] = true := by decide +kernel
theorem subd4_0_36 : subd4_0 [2, -2] = true := by decide +kernel
theorem subd4_0_37 : subd4_0 [2, -1] = true := by decide +kernel
theorem subd4_0_38 : subd4_0 [2, 0] = true := by decide +kernel
theorem subd4_0_39 : subd4_0 [2, 1] = true := by decide +kernel
theorem subd4_0_40 : subd4_0 [2, 2] = true := by decide +kernel
theorem subd4_0_41 : subd4_0 [3] = true := by decide +kernel
theorem sbd4_0_1 : ∀ q ∈ blkd4_0_1, subd4_0 q = true := by
  unfold blkd4_0_1
  exact List.forall_mem_cons.2 ⟨subd4_0_32, List.forall_mem_cons.2 ⟨subd4_0_33, List.forall_mem_cons.2 ⟨subd4_0_34, List.forall_mem_cons.2 ⟨subd4_0_35, List.forall_mem_cons.2 ⟨subd4_0_36, List.forall_mem_cons.2 ⟨subd4_0_37, List.forall_mem_cons.2 ⟨subd4_0_38, List.forall_mem_cons.2 ⟨subd4_0_39, List.forall_mem_cons.2 ⟨subd4_0_40, List.forall_mem_cons.2 ⟨subd4_0_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [-3] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-2, -3] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-2, -2] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-2, -1] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-2, 0] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-2, 1] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-2, 2] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [-1, -4] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [-1, 3] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [0, -4] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_20 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_21 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_22 : subd4_1 [0, 3] = true := by decide +kernel
theorem subd4_1_23 : subd4_1 [1, -4] = true := by decide +kernel
theorem subd4_1_24 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_25 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_26 : subd4_1 [1, -1] = true := by decide +kernel
theorem subd4_1_27 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_28 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_29 : subd4_1 [1, 2] = true := by decide +kernel
theorem subd4_1_30 : subd4_1 [1, 3] = true := by decide +kernel
theorem subd4_1_31 : subd4_1 [2, -3] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_cons.2 ⟨subd4_1_20, List.forall_mem_cons.2 ⟨subd4_1_21, List.forall_mem_cons.2 ⟨subd4_1_22, List.forall_mem_cons.2 ⟨subd4_1_23, List.forall_mem_cons.2 ⟨subd4_1_24, List.forall_mem_cons.2 ⟨subd4_1_25, List.forall_mem_cons.2 ⟨subd4_1_26, List.forall_mem_cons.2 ⟨subd4_1_27, List.forall_mem_cons.2 ⟨subd4_1_28, List.forall_mem_cons.2 ⟨subd4_1_29, List.forall_mem_cons.2 ⟨subd4_1_30, List.forall_mem_cons.2 ⟨subd4_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_32 : subd4_1 [2, -2] = true := by decide +kernel
theorem subd4_1_33 : subd4_1 [2, -1] = true := by decide +kernel
theorem subd4_1_34 : subd4_1 [2, 0] = true := by decide +kernel
theorem subd4_1_35 : subd4_1 [2, 1] = true := by decide +kernel
theorem subd4_1_36 : subd4_1 [2, 2] = true := by decide +kernel
theorem subd4_1_37 : subd4_1 [3] = true := by decide +kernel
theorem sbd4_1_1 : ∀ q ∈ blkd4_1_1, subd4_1 q = true := by
  unfold blkd4_1_1
  exact List.forall_mem_cons.2 ⟨subd4_1_32, List.forall_mem_cons.2 ⟨subd4_1_33, List.forall_mem_cons.2 ⟨subd4_1_34, List.forall_mem_cons.2 ⟨subd4_1_35, List.forall_mem_cons.2 ⟨subd4_1_36, List.forall_mem_cons.2 ⟨subd4_1_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel
theorem subd4_2_0 : subd4_2 [-3] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-2] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [-1, -3] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [-1, -2] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [-1, -1] = true := by decide +kernel
theorem subd4_2_5 : subd4_2 [-1, 0] = true := by decide +kernel
theorem subd4_2_6 : subd4_2 [-1, 1] = true := by decide +kernel
theorem subd4_2_7 : subd4_2 [-1, 2] = true := by decide +kernel
theorem subd4_2_8 : subd4_2 [-1, 3] = true := by decide +kernel
theorem subd4_2_9 : subd4_2 [0, -4] = true := by decide +kernel
theorem subd4_2_10 : subd4_2 [0, -3] = true := by decide +kernel
theorem subd4_2_11 : subd4_2 [0, -2] = true := by decide +kernel
theorem subd4_2_12 : subd4_2 [0, -1] = true := by decide +kernel
theorem subd4_2_13 : subd4_2 [0, 0] = true := by decide +kernel
theorem subd4_2_14 : subd4_2 [0, 1] = true := by decide +kernel
theorem subd4_2_15 : subd4_2 [0, 2] = true := by decide +kernel
theorem subd4_2_16 : subd4_2 [0, 3] = true := by decide +kernel
theorem subd4_2_17 : subd4_2 [1, -4] = true := by decide +kernel
theorem subd4_2_18 : subd4_2 [1, -3] = true := by decide +kernel
theorem subd4_2_19 : subd4_2 [1, -2] = true := by decide +kernel
theorem subd4_2_20 : subd4_2 [1, -1] = true := by decide +kernel
theorem subd4_2_21 : subd4_2 [1, 0] = true := by decide +kernel
theorem subd4_2_22 : subd4_2 [1, 1] = true := by decide +kernel
theorem subd4_2_23 : subd4_2 [1, 2] = true := by decide +kernel
theorem subd4_2_24 : subd4_2 [2] = true := by decide +kernel
theorem subd4_2_25 : subd4_2 [3] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_cons.2 ⟨subd4_2_5, List.forall_mem_cons.2 ⟨subd4_2_6, List.forall_mem_cons.2 ⟨subd4_2_7, List.forall_mem_cons.2 ⟨subd4_2_8, List.forall_mem_cons.2 ⟨subd4_2_9, List.forall_mem_cons.2 ⟨subd4_2_10, List.forall_mem_cons.2 ⟨subd4_2_11, List.forall_mem_cons.2 ⟨subd4_2_12, List.forall_mem_cons.2 ⟨subd4_2_13, List.forall_mem_cons.2 ⟨subd4_2_14, List.forall_mem_cons.2 ⟨subd4_2_15, List.forall_mem_cons.2 ⟨subd4_2_16, List.forall_mem_cons.2 ⟨subd4_2_17, List.forall_mem_cons.2 ⟨subd4_2_18, List.forall_mem_cons.2 ⟨subd4_2_19, List.forall_mem_cons.2 ⟨subd4_2_20, List.forall_mem_cons.2 ⟨subd4_2_21, List.forall_mem_cons.2 ⟨subd4_2_22, List.forall_mem_cons.2 ⟨subd4_2_23, List.forall_mem_cons.2 ⟨subd4_2_24, List.forall_mem_cons.2 ⟨subd4_2_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
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
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C061
