import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [-2] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [-1, -2] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [-1, -1] = true := by decide +kernel
theorem subd4_6_3 : subd4_6 [-1, 0] = true := by decide +kernel
theorem subd4_6_4 : subd4_6 [-1, 1] = true := by decide +kernel
theorem subd4_6_5 : subd4_6 [-1, 2] = true := by decide +kernel
theorem subd4_6_6 : subd4_6 [0, -3] = true := by decide +kernel
theorem subd4_6_7 : subd4_6 [0, -2] = true := by decide +kernel
theorem subd4_6_8 : subd4_6 [0, -1] = true := by decide +kernel
theorem subd4_6_9 : subd4_6 [0, 0] = true := by decide +kernel
theorem subd4_6_10 : subd4_6 [0, 1] = true := by decide +kernel
theorem subd4_6_11 : subd4_6 [0, 2] = true := by decide +kernel
theorem subd4_6_12 : subd4_6 [1, -3] = true := by decide +kernel
theorem subd4_6_13 : subd4_6 [1, -2] = true := by decide +kernel
theorem subd4_6_14 : subd4_6 [1, -1] = true := by decide +kernel
theorem subd4_6_15 : subd4_6 [1, 0] = true := by decide +kernel
theorem subd4_6_16 : subd4_6 [1, 1] = true := by decide +kernel
theorem subd4_6_17 : subd4_6 [2] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_cons.2 ⟨subd4_6_3, List.forall_mem_cons.2 ⟨subd4_6_4, List.forall_mem_cons.2 ⟨subd4_6_5, List.forall_mem_cons.2 ⟨subd4_6_6, List.forall_mem_cons.2 ⟨subd4_6_7, List.forall_mem_cons.2 ⟨subd4_6_8, List.forall_mem_cons.2 ⟨subd4_6_9, List.forall_mem_cons.2 ⟨subd4_6_10, List.forall_mem_cons.2 ⟨subd4_6_11, List.forall_mem_cons.2 ⟨subd4_6_12, List.forall_mem_cons.2 ⟨subd4_6_13, List.forall_mem_cons.2 ⟨subd4_6_14, List.forall_mem_cons.2 ⟨subd4_6_15, List.forall_mem_cons.2 ⟨subd4_6_16, List.forall_mem_cons.2 ⟨subd4_6_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [-3] = true := by decide +kernel
theorem subd4_7_1 : subd4_7 [-2, -3] = true := by decide +kernel
theorem subd4_7_2 : subd4_7 [-2, -2] = true := by decide +kernel
theorem subd4_7_3 : subd4_7 [-2, -1] = true := by decide +kernel
theorem subd4_7_4 : subd4_7 [-2, 0] = true := by decide +kernel
theorem subd4_7_5 : subd4_7 [-2, 1] = true := by decide +kernel
theorem subd4_7_6 : subd4_7 [-2, 2] = true := by decide +kernel
theorem subd4_7_7 : subd4_7 [-2, 3] = true := by decide +kernel
theorem subd4_7_8 : subd4_7 [-1, -4] = true := by decide +kernel
theorem subd4_7_9 : subd4_7 [-1, -3] = true := by decide +kernel
theorem subd4_7_10 : subd4_7 [-1, -2] = true := by decide +kernel
theorem subd4_7_11 : subd4_7 [-1, -1] = true := by decide +kernel
theorem subd4_7_12 : subd4_7 [-1, 0] = true := by decide +kernel
theorem subd4_7_13 : subd4_7 [-1, 1] = true := by decide +kernel
theorem subd4_7_14 : subd4_7 [-1, 2] = true := by decide +kernel
theorem subd4_7_15 : subd4_7 [-1, 3] = true := by decide +kernel
theorem subd4_7_16 : subd4_7 [0, -4] = true := by decide +kernel
theorem subd4_7_17 : subd4_7 [0, -3] = true := by decide +kernel
theorem subd4_7_18 : subd4_7 [0, -2] = true := by decide +kernel
theorem subd4_7_19 : subd4_7 [0, -1] = true := by decide +kernel
theorem subd4_7_20 : subd4_7 [0, 0] = true := by decide +kernel
theorem subd4_7_21 : subd4_7 [0, 1] = true := by decide +kernel
theorem subd4_7_22 : subd4_7 [0, 2] = true := by decide +kernel
theorem subd4_7_23 : subd4_7 [0, 3] = true := by decide +kernel
theorem subd4_7_24 : subd4_7 [1, -4] = true := by decide +kernel
theorem subd4_7_25 : subd4_7 [1, -3] = true := by decide +kernel
theorem subd4_7_26 : subd4_7 [1, -2] = true := by decide +kernel
theorem subd4_7_27 : subd4_7 [1, -1] = true := by decide +kernel
theorem subd4_7_28 : subd4_7 [1, 0] = true := by decide +kernel
theorem subd4_7_29 : subd4_7 [1, 1] = true := by decide +kernel
theorem subd4_7_30 : subd4_7 [1, 2] = true := by decide +kernel
theorem subd4_7_31 : subd4_7 [1, 3] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_cons.2 ⟨subd4_7_1, List.forall_mem_cons.2 ⟨subd4_7_2, List.forall_mem_cons.2 ⟨subd4_7_3, List.forall_mem_cons.2 ⟨subd4_7_4, List.forall_mem_cons.2 ⟨subd4_7_5, List.forall_mem_cons.2 ⟨subd4_7_6, List.forall_mem_cons.2 ⟨subd4_7_7, List.forall_mem_cons.2 ⟨subd4_7_8, List.forall_mem_cons.2 ⟨subd4_7_9, List.forall_mem_cons.2 ⟨subd4_7_10, List.forall_mem_cons.2 ⟨subd4_7_11, List.forall_mem_cons.2 ⟨subd4_7_12, List.forall_mem_cons.2 ⟨subd4_7_13, List.forall_mem_cons.2 ⟨subd4_7_14, List.forall_mem_cons.2 ⟨subd4_7_15, List.forall_mem_cons.2 ⟨subd4_7_16, List.forall_mem_cons.2 ⟨subd4_7_17, List.forall_mem_cons.2 ⟨subd4_7_18, List.forall_mem_cons.2 ⟨subd4_7_19, List.forall_mem_cons.2 ⟨subd4_7_20, List.forall_mem_cons.2 ⟨subd4_7_21, List.forall_mem_cons.2 ⟨subd4_7_22, List.forall_mem_cons.2 ⟨subd4_7_23, List.forall_mem_cons.2 ⟨subd4_7_24, List.forall_mem_cons.2 ⟨subd4_7_25, List.forall_mem_cons.2 ⟨subd4_7_26, List.forall_mem_cons.2 ⟨subd4_7_27, List.forall_mem_cons.2 ⟨subd4_7_28, List.forall_mem_cons.2 ⟨subd4_7_29, List.forall_mem_cons.2 ⟨subd4_7_30, List.forall_mem_cons.2 ⟨subd4_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_7_32 : subd4_7 [2, -4] = true := by decide +kernel
theorem subd4_7_33 : subd4_7 [2, -3] = true := by decide +kernel
theorem subd4_7_34 : subd4_7 [2, -2] = true := by decide +kernel
theorem subd4_7_35 : subd4_7 [2, -1] = true := by decide +kernel
theorem subd4_7_36 : subd4_7 [2, 0] = true := by decide +kernel
theorem subd4_7_37 : subd4_7 [2, 1] = true := by decide +kernel
theorem subd4_7_38 : subd4_7 [2, 2] = true := by decide +kernel
theorem subd4_7_39 : subd4_7 [3] = true := by decide +kernel
theorem sbd4_7_1 : ∀ q ∈ blkd4_7_1, subd4_7 q = true := by
  unfold blkd4_7_1
  exact List.forall_mem_cons.2 ⟨subd4_7_32, List.forall_mem_cons.2 ⟨subd4_7_33, List.forall_mem_cons.2 ⟨subd4_7_34, List.forall_mem_cons.2 ⟨subd4_7_35, List.forall_mem_cons.2 ⟨subd4_7_36, List.forall_mem_cons.2 ⟨subd4_7_37, List.forall_mem_cons.2 ⟨subd4_7_38, List.forall_mem_cons.2 ⟨subd4_7_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [-3] = true := by decide +kernel
theorem subd5_0_1 : subd5_0 [-2, -3] = true := by decide +kernel
theorem subd5_0_2 : subd5_0 [-2, -2] = true := by decide +kernel
theorem subd5_0_3 : subd5_0 [-2, -1] = true := by decide +kernel
theorem subd5_0_4 : subd5_0 [-2, 0] = true := by decide +kernel
theorem subd5_0_5 : subd5_0 [-2, 1] = true := by decide +kernel
theorem subd5_0_6 : subd5_0 [-2, 2] = true := by decide +kernel
theorem subd5_0_7 : subd5_0 [-2, 3] = true := by decide +kernel
theorem subd5_0_8 : subd5_0 [-1, -4] = true := by decide +kernel
theorem subd5_0_9 : subd5_0 [-1, -3] = true := by decide +kernel
theorem subd5_0_10 : subd5_0 [-1, -2] = true := by decide +kernel
theorem subd5_0_11 : subd5_0 [-1, -1] = true := by decide +kernel
theorem subd5_0_12 : subd5_0 [-1, 0] = true := by decide +kernel
theorem subd5_0_13 : subd5_0 [-1, 1] = true := by decide +kernel
theorem subd5_0_14 : subd5_0 [-1, 2] = true := by decide +kernel
theorem subd5_0_15 : subd5_0 [-1, 3] = true := by decide +kernel
theorem subd5_0_16 : subd5_0 [0, -4] = true := by decide +kernel
theorem subd5_0_17 : subd5_0 [0, -3] = true := by decide +kernel
theorem subd5_0_18 : subd5_0 [0, -2] = true := by decide +kernel
theorem subd5_0_19 : subd5_0 [0, -1] = true := by decide +kernel
theorem subd5_0_20 : subd5_0 [0, 0] = true := by decide +kernel
theorem subd5_0_21 : subd5_0 [0, 1] = true := by decide +kernel
theorem subd5_0_22 : subd5_0 [0, 2] = true := by decide +kernel
theorem subd5_0_23 : subd5_0 [0, 3] = true := by decide +kernel
theorem subd5_0_24 : subd5_0 [1, -4] = true := by decide +kernel
theorem subd5_0_25 : subd5_0 [1, -3] = true := by decide +kernel
theorem subd5_0_26 : subd5_0 [1, -2] = true := by decide +kernel
theorem subd5_0_27 : subd5_0 [1, -1] = true := by decide +kernel
theorem subd5_0_28 : subd5_0 [1, 0] = true := by decide +kernel
theorem subd5_0_29 : subd5_0 [1, 1] = true := by decide +kernel
theorem subd5_0_30 : subd5_0 [1, 2] = true := by decide +kernel
theorem subd5_0_31 : subd5_0 [1, 3] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_cons.2 ⟨subd5_0_1, List.forall_mem_cons.2 ⟨subd5_0_2, List.forall_mem_cons.2 ⟨subd5_0_3, List.forall_mem_cons.2 ⟨subd5_0_4, List.forall_mem_cons.2 ⟨subd5_0_5, List.forall_mem_cons.2 ⟨subd5_0_6, List.forall_mem_cons.2 ⟨subd5_0_7, List.forall_mem_cons.2 ⟨subd5_0_8, List.forall_mem_cons.2 ⟨subd5_0_9, List.forall_mem_cons.2 ⟨subd5_0_10, List.forall_mem_cons.2 ⟨subd5_0_11, List.forall_mem_cons.2 ⟨subd5_0_12, List.forall_mem_cons.2 ⟨subd5_0_13, List.forall_mem_cons.2 ⟨subd5_0_14, List.forall_mem_cons.2 ⟨subd5_0_15, List.forall_mem_cons.2 ⟨subd5_0_16, List.forall_mem_cons.2 ⟨subd5_0_17, List.forall_mem_cons.2 ⟨subd5_0_18, List.forall_mem_cons.2 ⟨subd5_0_19, List.forall_mem_cons.2 ⟨subd5_0_20, List.forall_mem_cons.2 ⟨subd5_0_21, List.forall_mem_cons.2 ⟨subd5_0_22, List.forall_mem_cons.2 ⟨subd5_0_23, List.forall_mem_cons.2 ⟨subd5_0_24, List.forall_mem_cons.2 ⟨subd5_0_25, List.forall_mem_cons.2 ⟨subd5_0_26, List.forall_mem_cons.2 ⟨subd5_0_27, List.forall_mem_cons.2 ⟨subd5_0_28, List.forall_mem_cons.2 ⟨subd5_0_29, List.forall_mem_cons.2 ⟨subd5_0_30, List.forall_mem_cons.2 ⟨subd5_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_32 : subd5_0 [2, -4] = true := by decide +kernel
theorem subd5_0_33 : subd5_0 [2, -3] = true := by decide +kernel
theorem subd5_0_34 : subd5_0 [2, -2] = true := by decide +kernel
theorem subd5_0_35 : subd5_0 [2, -1] = true := by decide +kernel
theorem subd5_0_36 : subd5_0 [2, 0] = true := by decide +kernel
theorem subd5_0_37 : subd5_0 [2, 1] = true := by decide +kernel
theorem subd5_0_38 : subd5_0 [2, 2] = true := by decide +kernel
theorem subd5_0_39 : subd5_0 [3] = true := by decide +kernel
theorem sbd5_0_1 : ∀ q ∈ blkd5_0_1, subd5_0 q = true := by
  unfold blkd5_0_1
  exact List.forall_mem_cons.2 ⟨subd5_0_32, List.forall_mem_cons.2 ⟨subd5_0_33, List.forall_mem_cons.2 ⟨subd5_0_34, List.forall_mem_cons.2 ⟨subd5_0_35, List.forall_mem_cons.2 ⟨subd5_0_36, List.forall_mem_cons.2 ⟨subd5_0_37, List.forall_mem_cons.2 ⟨subd5_0_38, List.forall_mem_cons.2 ⟨subd5_0_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_1 : ldCheck G d5_1.U d5_1.ms ldd5_1 = true := by decide +kernel
theorem pre_okd5_1 : subPre G cell5 d5_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C134
