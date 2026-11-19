import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_4_32 : subd5_4 [1, -2] = true := by decide +kernel
theorem subd5_4_33 : subd5_4 [1, -1] = true := by decide +kernel
theorem subd5_4_34 : subd5_4 [1, 0] = true := by decide +kernel
theorem subd5_4_35 : subd5_4 [1, 1] = true := by decide +kernel
theorem subd5_4_36 : subd5_4 [1, 2] = true := by decide +kernel
theorem subd5_4_37 : subd5_4 [1, 3] = true := by decide +kernel
theorem subd5_4_38 : subd5_4 [2, -5] = true := by decide +kernel
theorem subd5_4_39 : subd5_4 [2, -4] = true := by decide +kernel
theorem subd5_4_40 : subd5_4 [2, -3] = true := by decide +kernel
theorem subd5_4_41 : subd5_4 [2, -2] = true := by decide +kernel
theorem subd5_4_42 : subd5_4 [2, -1] = true := by decide +kernel
theorem subd5_4_43 : subd5_4 [2, 0] = true := by decide +kernel
theorem subd5_4_44 : subd5_4 [2, 1] = true := by decide +kernel
theorem subd5_4_45 : subd5_4 [2, 2] = true := by decide +kernel
theorem subd5_4_46 : subd5_4 [2, 3] = true := by decide +kernel
theorem subd5_4_47 : subd5_4 [3] = true := by decide +kernel
theorem sbd5_4_1 : ∀ q ∈ blkd5_4_1, subd5_4 q = true := by
  unfold blkd5_4_1
  exact List.forall_mem_cons.2 ⟨subd5_4_32, List.forall_mem_cons.2 ⟨subd5_4_33, List.forall_mem_cons.2 ⟨subd5_4_34, List.forall_mem_cons.2 ⟨subd5_4_35, List.forall_mem_cons.2 ⟨subd5_4_36, List.forall_mem_cons.2 ⟨subd5_4_37, List.forall_mem_cons.2 ⟨subd5_4_38, List.forall_mem_cons.2 ⟨subd5_4_39, List.forall_mem_cons.2 ⟨subd5_4_40, List.forall_mem_cons.2 ⟨subd5_4_41, List.forall_mem_cons.2 ⟨subd5_4_42, List.forall_mem_cons.2 ⟨subd5_4_43, List.forall_mem_cons.2 ⟨subd5_4_44, List.forall_mem_cons.2 ⟨subd5_4_45, List.forall_mem_cons.2 ⟨subd5_4_46, List.forall_mem_cons.2 ⟨subd5_4_47, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_5 : ldCheck G d5_5.U d5_5.ms ldd5_5 = true := by decide +kernel
theorem pre_okd5_5 : subPre G cell5 d5_5 = true := by decide +kernel
theorem subd5_5_0 : subd5_5 [-3] = true := by decide +kernel
theorem subd5_5_1 : subd5_5 [-2, -4] = true := by decide +kernel
theorem subd5_5_2 : subd5_5 [-2, -3] = true := by decide +kernel
theorem subd5_5_3 : subd5_5 [-2, -2] = true := by decide +kernel
theorem subd5_5_4 : subd5_5 [-2, -1] = true := by decide +kernel
theorem subd5_5_5 : subd5_5 [-2, 0] = true := by decide +kernel
theorem subd5_5_6 : subd5_5 [-2, 1] = true := by decide +kernel
theorem subd5_5_7 : subd5_5 [-2, 2] = true := by decide +kernel
theorem subd5_5_8 : subd5_5 [-1, -4] = true := by decide +kernel
theorem subd5_5_9 : subd5_5 [-1, -3] = true := by decide +kernel
theorem subd5_5_10 : subd5_5 [-1, -2] = true := by decide +kernel
theorem subd5_5_11 : subd5_5 [-1, -1] = true := by decide +kernel
theorem subd5_5_12 : subd5_5 [-1, 0] = true := by decide +kernel
theorem subd5_5_13 : subd5_5 [-1, 1] = true := by decide +kernel
theorem subd5_5_14 : subd5_5 [-1, 2] = true := by decide +kernel
theorem subd5_5_15 : subd5_5 [0, -4] = true := by decide +kernel
theorem subd5_5_16 : subd5_5 [0, -3] = true := by decide +kernel
theorem subd5_5_17 : subd5_5 [0, -2] = true := by decide +kernel
theorem subd5_5_18 : subd5_5 [0, -1] = true := by decide +kernel
theorem subd5_5_19 : subd5_5 [0, 0] = true := by decide +kernel
theorem subd5_5_20 : subd5_5 [0, 1] = true := by decide +kernel
theorem subd5_5_21 : subd5_5 [0, 2] = true := by decide +kernel
theorem subd5_5_22 : subd5_5 [0, 3] = true := by decide +kernel
theorem subd5_5_23 : subd5_5 [1, -3] = true := by decide +kernel
theorem subd5_5_24 : subd5_5 [1, -2] = true := by decide +kernel
theorem subd5_5_25 : subd5_5 [1, -1] = true := by decide +kernel
theorem subd5_5_26 : subd5_5 [1, 0] = true := by decide +kernel
theorem subd5_5_27 : subd5_5 [1, 1] = true := by decide +kernel
theorem subd5_5_28 : subd5_5 [1, 2] = true := by decide +kernel
theorem subd5_5_29 : subd5_5 [1, 3] = true := by decide +kernel
theorem subd5_5_30 : subd5_5 [2, -3] = true := by decide +kernel
theorem subd5_5_31 : subd5_5 [2, -2] = true := by decide +kernel
theorem sbd5_5_0 : ∀ q ∈ blkd5_5_0, subd5_5 q = true := by
  unfold blkd5_5_0
  exact List.forall_mem_cons.2 ⟨subd5_5_0, List.forall_mem_cons.2 ⟨subd5_5_1, List.forall_mem_cons.2 ⟨subd5_5_2, List.forall_mem_cons.2 ⟨subd5_5_3, List.forall_mem_cons.2 ⟨subd5_5_4, List.forall_mem_cons.2 ⟨subd5_5_5, List.forall_mem_cons.2 ⟨subd5_5_6, List.forall_mem_cons.2 ⟨subd5_5_7, List.forall_mem_cons.2 ⟨subd5_5_8, List.forall_mem_cons.2 ⟨subd5_5_9, List.forall_mem_cons.2 ⟨subd5_5_10, List.forall_mem_cons.2 ⟨subd5_5_11, List.forall_mem_cons.2 ⟨subd5_5_12, List.forall_mem_cons.2 ⟨subd5_5_13, List.forall_mem_cons.2 ⟨subd5_5_14, List.forall_mem_cons.2 ⟨subd5_5_15, List.forall_mem_cons.2 ⟨subd5_5_16, List.forall_mem_cons.2 ⟨subd5_5_17, List.forall_mem_cons.2 ⟨subd5_5_18, List.forall_mem_cons.2 ⟨subd5_5_19, List.forall_mem_cons.2 ⟨subd5_5_20, List.forall_mem_cons.2 ⟨subd5_5_21, List.forall_mem_cons.2 ⟨subd5_5_22, List.forall_mem_cons.2 ⟨subd5_5_23, List.forall_mem_cons.2 ⟨subd5_5_24, List.forall_mem_cons.2 ⟨subd5_5_25, List.forall_mem_cons.2 ⟨subd5_5_26, List.forall_mem_cons.2 ⟨subd5_5_27, List.forall_mem_cons.2 ⟨subd5_5_28, List.forall_mem_cons.2 ⟨subd5_5_29, List.forall_mem_cons.2 ⟨subd5_5_30, List.forall_mem_cons.2 ⟨subd5_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_32 : subd5_5 [2, -1] = true := by decide +kernel
theorem subd5_5_33 : subd5_5 [2, 0] = true := by decide +kernel
theorem subd5_5_34 : subd5_5 [2, 1] = true := by decide +kernel
theorem subd5_5_35 : subd5_5 [2, 2] = true := by decide +kernel
theorem subd5_5_36 : subd5_5 [2, 3] = true := by decide +kernel
theorem subd5_5_37 : subd5_5 [3] = true := by decide +kernel
theorem sbd5_5_1 : ∀ q ∈ blkd5_5_1, subd5_5 q = true := by
  unfold blkd5_5_1
  exact List.forall_mem_cons.2 ⟨subd5_5_32, List.forall_mem_cons.2 ⟨subd5_5_33, List.forall_mem_cons.2 ⟨subd5_5_34, List.forall_mem_cons.2 ⟨subd5_5_35, List.forall_mem_cons.2 ⟨subd5_5_36, List.forall_mem_cons.2 ⟨subd5_5_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd5_6 : ldCheck G d5_6.U d5_6.ms ldd5_6 = true := by decide +kernel
theorem pre_okd5_6 : subPre G cell5 d5_6 = true := by decide +kernel
theorem subd5_6_0 : subd5_6 [-2] = true := by decide +kernel
theorem subd5_6_1 : subd5_6 [-1, -3] = true := by decide +kernel
theorem subd5_6_2 : subd5_6 [-1, -2] = true := by decide +kernel
theorem subd5_6_3 : subd5_6 [-1, -1] = true := by decide +kernel
theorem subd5_6_4 : subd5_6 [-1, 0] = true := by decide +kernel
theorem subd5_6_5 : subd5_6 [-1, 1] = true := by decide +kernel
theorem subd5_6_6 : subd5_6 [-1, 2] = true := by decide +kernel
theorem subd5_6_7 : subd5_6 [0, -3] = true := by decide +kernel
theorem subd5_6_8 : subd5_6 [0, -2] = true := by decide +kernel
theorem subd5_6_9 : subd5_6 [0, -1] = true := by decide +kernel
theorem subd5_6_10 : subd5_6 [0, 0] = true := by decide +kernel
theorem subd5_6_11 : subd5_6 [0, 1] = true := by decide +kernel
theorem subd5_6_12 : subd5_6 [0, 2] = true := by decide +kernel
theorem subd5_6_13 : subd5_6 [1, -3] = true := by decide +kernel
theorem subd5_6_14 : subd5_6 [1, -2] = true := by decide +kernel
theorem subd5_6_15 : subd5_6 [1, -1] = true := by decide +kernel
theorem subd5_6_16 : subd5_6 [1, 0] = true := by decide +kernel
theorem subd5_6_17 : subd5_6 [1, 1] = true := by decide +kernel
theorem subd5_6_18 : subd5_6 [1, 2] = true := by decide +kernel
theorem subd5_6_19 : subd5_6 [2] = true := by decide +kernel
theorem sbd5_6_0 : ∀ q ∈ blkd5_6_0, subd5_6 q = true := by
  unfold blkd5_6_0
  exact List.forall_mem_cons.2 ⟨subd5_6_0, List.forall_mem_cons.2 ⟨subd5_6_1, List.forall_mem_cons.2 ⟨subd5_6_2, List.forall_mem_cons.2 ⟨subd5_6_3, List.forall_mem_cons.2 ⟨subd5_6_4, List.forall_mem_cons.2 ⟨subd5_6_5, List.forall_mem_cons.2 ⟨subd5_6_6, List.forall_mem_cons.2 ⟨subd5_6_7, List.forall_mem_cons.2 ⟨subd5_6_8, List.forall_mem_cons.2 ⟨subd5_6_9, List.forall_mem_cons.2 ⟨subd5_6_10, List.forall_mem_cons.2 ⟨subd5_6_11, List.forall_mem_cons.2 ⟨subd5_6_12, List.forall_mem_cons.2 ⟨subd5_6_13, List.forall_mem_cons.2 ⟨subd5_6_14, List.forall_mem_cons.2 ⟨subd5_6_15, List.forall_mem_cons.2 ⟨subd5_6_16, List.forall_mem_cons.2 ⟨subd5_6_17, List.forall_mem_cons.2 ⟨subd5_6_18, List.forall_mem_cons.2 ⟨subd5_6_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_7 : ldCheck G d5_7.U d5_7.ms ldd5_7 = true := by decide +kernel
theorem pre_okd5_7 : subPre G cell5 d5_7 = true := by decide +kernel
theorem subd5_7_0 : subd5_7 [-3] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-2, -2] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [-2, -1] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [-2, 0] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [-2, 1] = true := by decide +kernel
theorem subd5_7_5 : subd5_7 [-2, 2] = true := by decide +kernel
theorem subd5_7_6 : subd5_7 [-2, 3] = true := by decide +kernel
theorem subd5_7_7 : subd5_7 [-1, -3] = true := by decide +kernel
theorem subd5_7_8 : subd5_7 [-1, -2] = true := by decide +kernel
theorem subd5_7_9 : subd5_7 [-1, -1] = true := by decide +kernel
theorem subd5_7_10 : subd5_7 [-1, 0] = true := by decide +kernel
theorem subd5_7_11 : subd5_7 [-1, 1] = true := by decide +kernel
theorem subd5_7_12 : subd5_7 [-1, 2] = true := by decide +kernel
theorem subd5_7_13 : subd5_7 [-1, 3] = true := by decide +kernel
theorem subd5_7_14 : subd5_7 [0, -4] = true := by decide +kernel
theorem subd5_7_15 : subd5_7 [0, -3] = true := by decide +kernel
theorem subd5_7_16 : subd5_7 [0, -2] = true := by decide +kernel
theorem subd5_7_17 : subd5_7 [0, -1] = true := by decide +kernel
theorem subd5_7_18 : subd5_7 [0, 0] = true := by decide +kernel
theorem subd5_7_19 : subd5_7 [0, 1] = true := by decide +kernel
theorem subd5_7_20 : subd5_7 [0, 2] = true := by decide +kernel
theorem subd5_7_21 : subd5_7 [0, 3] = true := by decide +kernel
theorem subd5_7_22 : subd5_7 [1, -4] = true := by decide +kernel
theorem subd5_7_23 : subd5_7 [1, -3] = true := by decide +kernel
theorem subd5_7_24 : subd5_7 [1, -2] = true := by decide +kernel
theorem subd5_7_25 : subd5_7 [1, -1] = true := by decide +kernel
theorem subd5_7_26 : subd5_7 [1, 0] = true := by decide +kernel
theorem subd5_7_27 : subd5_7 [1, 1] = true := by decide +kernel
theorem subd5_7_28 : subd5_7 [1, 2] = true := by decide +kernel
theorem subd5_7_29 : subd5_7 [2, -4] = true := by decide +kernel
theorem subd5_7_30 : subd5_7 [2, -3] = true := by decide +kernel
theorem subd5_7_31 : subd5_7 [2, -2] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_cons.2 ⟨subd5_7_5, List.forall_mem_cons.2 ⟨subd5_7_6, List.forall_mem_cons.2 ⟨subd5_7_7, List.forall_mem_cons.2 ⟨subd5_7_8, List.forall_mem_cons.2 ⟨subd5_7_9, List.forall_mem_cons.2 ⟨subd5_7_10, List.forall_mem_cons.2 ⟨subd5_7_11, List.forall_mem_cons.2 ⟨subd5_7_12, List.forall_mem_cons.2 ⟨subd5_7_13, List.forall_mem_cons.2 ⟨subd5_7_14, List.forall_mem_cons.2 ⟨subd5_7_15, List.forall_mem_cons.2 ⟨subd5_7_16, List.forall_mem_cons.2 ⟨subd5_7_17, List.forall_mem_cons.2 ⟨subd5_7_18, List.forall_mem_cons.2 ⟨subd5_7_19, List.forall_mem_cons.2 ⟨subd5_7_20, List.forall_mem_cons.2 ⟨subd5_7_21, List.forall_mem_cons.2 ⟨subd5_7_22, List.forall_mem_cons.2 ⟨subd5_7_23, List.forall_mem_cons.2 ⟨subd5_7_24, List.forall_mem_cons.2 ⟨subd5_7_25, List.forall_mem_cons.2 ⟨subd5_7_26, List.forall_mem_cons.2 ⟨subd5_7_27, List.forall_mem_cons.2 ⟨subd5_7_28, List.forall_mem_cons.2 ⟨subd5_7_29, List.forall_mem_cons.2 ⟨subd5_7_30, List.forall_mem_cons.2 ⟨subd5_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_32 : subd5_7 [2, -1] = true := by decide +kernel
theorem subd5_7_33 : subd5_7 [2, 0] = true := by decide +kernel
theorem subd5_7_34 : subd5_7 [2, 1] = true := by decide +kernel
theorem subd5_7_35 : subd5_7 [3] = true := by decide +kernel
theorem sbd5_7_1 : ∀ q ∈ blkd5_7_1, subd5_7 q = true := by
  unfold blkd5_7_1
  exact List.forall_mem_cons.2 ⟨subd5_7_32, List.forall_mem_cons.2 ⟨subd5_7_33, List.forall_mem_cons.2 ⟨subd5_7_34, List.forall_mem_cons.2 ⟨subd5_7_35, List.forall_mem_nil _⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C134
