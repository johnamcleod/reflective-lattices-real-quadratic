import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_4_0 : subd4_4 [-2] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [-1] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [0] = true := by decide +kernel
theorem subd4_4_3 : subd4_4 [1] = true := by decide +kernel
theorem subd4_4_4 : subd4_4 [2] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_cons.2 ⟨subd4_4_3, List.forall_mem_cons.2 ⟨subd4_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-2] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-1] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [1] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [2] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel
theorem subd5_1_0 : subd5_1 [-3] = true := by decide +kernel
theorem subd5_1_1 : subd5_1 [-2, -3] = true := by decide +kernel
theorem subd5_1_2 : subd5_1 [-2, -2] = true := by decide +kernel
theorem subd5_1_3 : subd5_1 [-2, -1] = true := by decide +kernel
theorem subd5_1_4 : subd5_1 [-2, 0] = true := by decide +kernel
theorem subd5_1_5 : subd5_1 [-2, 1] = true := by decide +kernel
theorem subd5_1_6 : subd5_1 [-2, 2] = true := by decide +kernel
theorem subd5_1_7 : subd5_1 [-1, -4] = true := by decide +kernel
theorem subd5_1_8 : subd5_1 [-1, -3] = true := by decide +kernel
theorem subd5_1_9 : subd5_1 [-1, -2] = true := by decide +kernel
theorem subd5_1_10 : subd5_1 [-1, -1] = true := by decide +kernel
theorem subd5_1_11 : subd5_1 [-1, 0] = true := by decide +kernel
theorem subd5_1_12 : subd5_1 [-1, 1] = true := by decide +kernel
theorem subd5_1_13 : subd5_1 [-1, 2] = true := by decide +kernel
theorem subd5_1_14 : subd5_1 [-1, 3] = true := by decide +kernel
theorem subd5_1_15 : subd5_1 [0, -4] = true := by decide +kernel
theorem subd5_1_16 : subd5_1 [0, -3] = true := by decide +kernel
theorem subd5_1_17 : subd5_1 [0, -2] = true := by decide +kernel
theorem subd5_1_18 : subd5_1 [0, -1] = true := by decide +kernel
theorem subd5_1_19 : subd5_1 [0, 0] = true := by decide +kernel
theorem subd5_1_20 : subd5_1 [0, 1] = true := by decide +kernel
theorem subd5_1_21 : subd5_1 [0, 2] = true := by decide +kernel
theorem subd5_1_22 : subd5_1 [0, 3] = true := by decide +kernel
theorem subd5_1_23 : subd5_1 [1, -4] = true := by decide +kernel
theorem subd5_1_24 : subd5_1 [1, -3] = true := by decide +kernel
theorem subd5_1_25 : subd5_1 [1, -2] = true := by decide +kernel
theorem subd5_1_26 : subd5_1 [1, -1] = true := by decide +kernel
theorem subd5_1_27 : subd5_1 [1, 0] = true := by decide +kernel
theorem subd5_1_28 : subd5_1 [1, 1] = true := by decide +kernel
theorem subd5_1_29 : subd5_1 [1, 2] = true := by decide +kernel
theorem subd5_1_30 : subd5_1 [1, 3] = true := by decide +kernel
theorem subd5_1_31 : subd5_1 [2, -3] = true := by decide +kernel
theorem sbd5_1_0 : ∀ q ∈ blkd5_1_0, subd5_1 q = true := by
  unfold blkd5_1_0
  exact List.forall_mem_cons.2 ⟨subd5_1_0, List.forall_mem_cons.2 ⟨subd5_1_1, List.forall_mem_cons.2 ⟨subd5_1_2, List.forall_mem_cons.2 ⟨subd5_1_3, List.forall_mem_cons.2 ⟨subd5_1_4, List.forall_mem_cons.2 ⟨subd5_1_5, List.forall_mem_cons.2 ⟨subd5_1_6, List.forall_mem_cons.2 ⟨subd5_1_7, List.forall_mem_cons.2 ⟨subd5_1_8, List.forall_mem_cons.2 ⟨subd5_1_9, List.forall_mem_cons.2 ⟨subd5_1_10, List.forall_mem_cons.2 ⟨subd5_1_11, List.forall_mem_cons.2 ⟨subd5_1_12, List.forall_mem_cons.2 ⟨subd5_1_13, List.forall_mem_cons.2 ⟨subd5_1_14, List.forall_mem_cons.2 ⟨subd5_1_15, List.forall_mem_cons.2 ⟨subd5_1_16, List.forall_mem_cons.2 ⟨subd5_1_17, List.forall_mem_cons.2 ⟨subd5_1_18, List.forall_mem_cons.2 ⟨subd5_1_19, List.forall_mem_cons.2 ⟨subd5_1_20, List.forall_mem_cons.2 ⟨subd5_1_21, List.forall_mem_cons.2 ⟨subd5_1_22, List.forall_mem_cons.2 ⟨subd5_1_23, List.forall_mem_cons.2 ⟨subd5_1_24, List.forall_mem_cons.2 ⟨subd5_1_25, List.forall_mem_cons.2 ⟨subd5_1_26, List.forall_mem_cons.2 ⟨subd5_1_27, List.forall_mem_cons.2 ⟨subd5_1_28, List.forall_mem_cons.2 ⟨subd5_1_29, List.forall_mem_cons.2 ⟨subd5_1_30, List.forall_mem_cons.2 ⟨subd5_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_32 : subd5_1 [2, -2] = true := by decide +kernel
theorem subd5_1_33 : subd5_1 [2, -1] = true := by decide +kernel
theorem subd5_1_34 : subd5_1 [2, 0] = true := by decide +kernel
theorem subd5_1_35 : subd5_1 [2, 1] = true := by decide +kernel
theorem subd5_1_36 : subd5_1 [2, 2] = true := by decide +kernel
theorem subd5_1_37 : subd5_1 [3] = true := by decide +kernel
theorem sbd5_1_1 : ∀ q ∈ blkd5_1_1, subd5_1 q = true := by
  unfold blkd5_1_1
  exact List.forall_mem_cons.2 ⟨subd5_1_32, List.forall_mem_cons.2 ⟨subd5_1_33, List.forall_mem_cons.2 ⟨subd5_1_34, List.forall_mem_cons.2 ⟨subd5_1_35, List.forall_mem_cons.2 ⟨subd5_1_36, List.forall_mem_cons.2 ⟨subd5_1_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd5_2 : ldCheck G d5_2.U d5_2.ms ldd5_2 = true := by decide +kernel
theorem pre_okd5_2 : subPre G cell5 d5_2 = true := by decide +kernel
theorem subd5_2_0 : subd5_2 [-4] = true := by decide +kernel
theorem subd5_2_1 : subd5_2 [-3, -5] = true := by decide +kernel
theorem subd5_2_2 : subd5_2 [-3, -4] = true := by decide +kernel
theorem subd5_2_3 : subd5_2 [-3, -3] = true := by decide +kernel
theorem subd5_2_4 : subd5_2 [-3, -2] = true := by decide +kernel
theorem subd5_2_5 : subd5_2 [-3, -1] = true := by decide +kernel
theorem subd5_2_6 : subd5_2 [-3, 0] = true := by decide +kernel
theorem subd5_2_7 : subd5_2 [-3, 1] = true := by decide +kernel
theorem subd5_2_8 : subd5_2 [-2, -5] = true := by decide +kernel
theorem subd5_2_9 : subd5_2 [-2, -4] = true := by decide +kernel
theorem subd5_2_10 : subd5_2 [-2, -3] = true := by decide +kernel
theorem subd5_2_11 : subd5_2 [-2, -2] = true := by decide +kernel
theorem subd5_2_12 : subd5_2 [-2, -1] = true := by decide +kernel
theorem subd5_2_13 : subd5_2 [-2, 0] = true := by decide +kernel
theorem subd5_2_14 : subd5_2 [-2, 1] = true := by decide +kernel
theorem subd5_2_15 : subd5_2 [-2, 2] = true := by decide +kernel
theorem subd5_2_16 : subd5_2 [-2, 3] = true := by decide +kernel
theorem subd5_2_17 : subd5_2 [-1, -5] = true := by decide +kernel
theorem subd5_2_18 : subd5_2 [-1, -4] = true := by decide +kernel
theorem subd5_2_19 : subd5_2 [-1, -3] = true := by decide +kernel
theorem subd5_2_20 : subd5_2 [-1, -2] = true := by decide +kernel
theorem subd5_2_21 : subd5_2 [-1, -1] = true := by decide +kernel
theorem subd5_2_22 : subd5_2 [-1, 0] = true := by decide +kernel
theorem subd5_2_23 : subd5_2 [-1, 1] = true := by decide +kernel
theorem subd5_2_24 : subd5_2 [-1, 2] = true := by decide +kernel
theorem subd5_2_25 : subd5_2 [-1, 3] = true := by decide +kernel
theorem subd5_2_26 : subd5_2 [-1, 4] = true := by decide +kernel
theorem subd5_2_27 : subd5_2 [0, -5] = true := by decide +kernel
theorem subd5_2_28 : subd5_2 [0, -4] = true := by decide +kernel
theorem subd5_2_29 : subd5_2 [0, -3] = true := by decide +kernel
theorem subd5_2_30 : subd5_2 [0, -2] = true := by decide +kernel
theorem subd5_2_31 : subd5_2 [0, -1] = true := by decide +kernel
theorem sbd5_2_0 : ∀ q ∈ blkd5_2_0, subd5_2 q = true := by
  unfold blkd5_2_0
  exact List.forall_mem_cons.2 ⟨subd5_2_0, List.forall_mem_cons.2 ⟨subd5_2_1, List.forall_mem_cons.2 ⟨subd5_2_2, List.forall_mem_cons.2 ⟨subd5_2_3, List.forall_mem_cons.2 ⟨subd5_2_4, List.forall_mem_cons.2 ⟨subd5_2_5, List.forall_mem_cons.2 ⟨subd5_2_6, List.forall_mem_cons.2 ⟨subd5_2_7, List.forall_mem_cons.2 ⟨subd5_2_8, List.forall_mem_cons.2 ⟨subd5_2_9, List.forall_mem_cons.2 ⟨subd5_2_10, List.forall_mem_cons.2 ⟨subd5_2_11, List.forall_mem_cons.2 ⟨subd5_2_12, List.forall_mem_cons.2 ⟨subd5_2_13, List.forall_mem_cons.2 ⟨subd5_2_14, List.forall_mem_cons.2 ⟨subd5_2_15, List.forall_mem_cons.2 ⟨subd5_2_16, List.forall_mem_cons.2 ⟨subd5_2_17, List.forall_mem_cons.2 ⟨subd5_2_18, List.forall_mem_cons.2 ⟨subd5_2_19, List.forall_mem_cons.2 ⟨subd5_2_20, List.forall_mem_cons.2 ⟨subd5_2_21, List.forall_mem_cons.2 ⟨subd5_2_22, List.forall_mem_cons.2 ⟨subd5_2_23, List.forall_mem_cons.2 ⟨subd5_2_24, List.forall_mem_cons.2 ⟨subd5_2_25, List.forall_mem_cons.2 ⟨subd5_2_26, List.forall_mem_cons.2 ⟨subd5_2_27, List.forall_mem_cons.2 ⟨subd5_2_28, List.forall_mem_cons.2 ⟨subd5_2_29, List.forall_mem_cons.2 ⟨subd5_2_30, List.forall_mem_cons.2 ⟨subd5_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
