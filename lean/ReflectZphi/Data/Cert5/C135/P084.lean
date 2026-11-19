import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd14_2_0 : subd14_2 [-3] = true := by decide +kernel
theorem subd14_2_1 : subd14_2 [-2, -2] = true := by decide +kernel
theorem subd14_2_2 : subd14_2 [-2, -1] = true := by decide +kernel
theorem subd14_2_3 : subd14_2 [-2, 0] = true := by decide +kernel
theorem subd14_2_4 : subd14_2 [-2, 1] = true := by decide +kernel
theorem subd14_2_5 : subd14_2 [-2, 2] = true := by decide +kernel
theorem subd14_2_6 : subd14_2 [-2, 3] = true := by decide +kernel
theorem subd14_2_7 : subd14_2 [-1, -3] = true := by decide +kernel
theorem subd14_2_8 : subd14_2 [-1, -2] = true := by decide +kernel
theorem subd14_2_9 : subd14_2 [-1, -1] = true := by decide +kernel
theorem subd14_2_10 : subd14_2 [-1, 0] = true := by decide +kernel
theorem subd14_2_11 : subd14_2 [-1, 1] = true := by decide +kernel
theorem subd14_2_12 : subd14_2 [-1, 2] = true := by decide +kernel
theorem subd14_2_13 : subd14_2 [-1, 3] = true := by decide +kernel
theorem subd14_2_14 : subd14_2 [0, -4] = true := by decide +kernel
theorem subd14_2_15 : subd14_2 [0, -3] = true := by decide +kernel
theorem subd14_2_16 : subd14_2 [0, -2] = true := by decide +kernel
theorem subd14_2_17 : subd14_2 [0, -1] = true := by decide +kernel
theorem subd14_2_18 : subd14_2 [0, 0] = true := by decide +kernel
theorem subd14_2_19 : subd14_2 [0, 1] = true := by decide +kernel
theorem subd14_2_20 : subd14_2 [0, 2] = true := by decide +kernel
theorem subd14_2_21 : subd14_2 [0, 3] = true := by decide +kernel
theorem subd14_2_22 : subd14_2 [1, -4] = true := by decide +kernel
theorem subd14_2_23 : subd14_2 [1, -3] = true := by decide +kernel
theorem subd14_2_24 : subd14_2 [1, -2] = true := by decide +kernel
theorem subd14_2_25 : subd14_2 [1, -1] = true := by decide +kernel
theorem subd14_2_26 : subd14_2 [1, 0] = true := by decide +kernel
theorem subd14_2_27 : subd14_2 [1, 1] = true := by decide +kernel
theorem subd14_2_28 : subd14_2 [1, 2] = true := by decide +kernel
theorem subd14_2_29 : subd14_2 [2, -4] = true := by decide +kernel
theorem subd14_2_30 : subd14_2 [2, -3] = true := by decide +kernel
theorem subd14_2_31 : subd14_2 [2, -2] = true := by decide +kernel
theorem sbd14_2_0 : ∀ q ∈ blkd14_2_0, subd14_2 q = true := by
  unfold blkd14_2_0
  exact List.forall_mem_cons.2 ⟨subd14_2_0, List.forall_mem_cons.2 ⟨subd14_2_1, List.forall_mem_cons.2 ⟨subd14_2_2, List.forall_mem_cons.2 ⟨subd14_2_3, List.forall_mem_cons.2 ⟨subd14_2_4, List.forall_mem_cons.2 ⟨subd14_2_5, List.forall_mem_cons.2 ⟨subd14_2_6, List.forall_mem_cons.2 ⟨subd14_2_7, List.forall_mem_cons.2 ⟨subd14_2_8, List.forall_mem_cons.2 ⟨subd14_2_9, List.forall_mem_cons.2 ⟨subd14_2_10, List.forall_mem_cons.2 ⟨subd14_2_11, List.forall_mem_cons.2 ⟨subd14_2_12, List.forall_mem_cons.2 ⟨subd14_2_13, List.forall_mem_cons.2 ⟨subd14_2_14, List.forall_mem_cons.2 ⟨subd14_2_15, List.forall_mem_cons.2 ⟨subd14_2_16, List.forall_mem_cons.2 ⟨subd14_2_17, List.forall_mem_cons.2 ⟨subd14_2_18, List.forall_mem_cons.2 ⟨subd14_2_19, List.forall_mem_cons.2 ⟨subd14_2_20, List.forall_mem_cons.2 ⟨subd14_2_21, List.forall_mem_cons.2 ⟨subd14_2_22, List.forall_mem_cons.2 ⟨subd14_2_23, List.forall_mem_cons.2 ⟨subd14_2_24, List.forall_mem_cons.2 ⟨subd14_2_25, List.forall_mem_cons.2 ⟨subd14_2_26, List.forall_mem_cons.2 ⟨subd14_2_27, List.forall_mem_cons.2 ⟨subd14_2_28, List.forall_mem_cons.2 ⟨subd14_2_29, List.forall_mem_cons.2 ⟨subd14_2_30, List.forall_mem_cons.2 ⟨subd14_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_2_32 : subd14_2 [2, -1] = true := by decide +kernel
theorem subd14_2_33 : subd14_2 [2, 0] = true := by decide +kernel
theorem subd14_2_34 : subd14_2 [2, 1] = true := by decide +kernel
theorem subd14_2_35 : subd14_2 [3] = true := by decide +kernel
theorem sbd14_2_1 : ∀ q ∈ blkd14_2_1, subd14_2 q = true := by
  unfold blkd14_2_1
  exact List.forall_mem_cons.2 ⟨subd14_2_32, List.forall_mem_cons.2 ⟨subd14_2_33, List.forall_mem_cons.2 ⟨subd14_2_34, List.forall_mem_cons.2 ⟨subd14_2_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [-3] = true := by decide +kernel
theorem subd14_3_1 : subd14_3 [-2, -2] = true := by decide +kernel
theorem subd14_3_2 : subd14_3 [-2, -1] = true := by decide +kernel
theorem subd14_3_3 : subd14_3 [-2, 0] = true := by decide +kernel
theorem subd14_3_4 : subd14_3 [-2, 1] = true := by decide +kernel
theorem subd14_3_5 : subd14_3 [-2, 2] = true := by decide +kernel
theorem subd14_3_6 : subd14_3 [-1, -3] = true := by decide +kernel
theorem subd14_3_7 : subd14_3 [-1, -2] = true := by decide +kernel
theorem subd14_3_8 : subd14_3 [-1, -1] = true := by decide +kernel
theorem subd14_3_9 : subd14_3 [-1, 0] = true := by decide +kernel
theorem subd14_3_10 : subd14_3 [-1, 1] = true := by decide +kernel
theorem subd14_3_11 : subd14_3 [-1, 2] = true := by decide +kernel
theorem subd14_3_12 : subd14_3 [-1, 3] = true := by decide +kernel
theorem subd14_3_13 : subd14_3 [0, -3] = true := by decide +kernel
theorem subd14_3_14 : subd14_3 [0, -2] = true := by decide +kernel
theorem subd14_3_15 : subd14_3 [0, -1] = true := by decide +kernel
theorem subd14_3_16 : subd14_3 [0, 0] = true := by decide +kernel
theorem subd14_3_17 : subd14_3 [0, 1] = true := by decide +kernel
theorem subd14_3_18 : subd14_3 [0, 2] = true := by decide +kernel
theorem subd14_3_19 : subd14_3 [1, -4] = true := by decide +kernel
theorem subd14_3_20 : subd14_3 [1, -3] = true := by decide +kernel
theorem subd14_3_21 : subd14_3 [1, -2] = true := by decide +kernel
theorem subd14_3_22 : subd14_3 [1, -1] = true := by decide +kernel
theorem subd14_3_23 : subd14_3 [1, 0] = true := by decide +kernel
theorem subd14_3_24 : subd14_3 [1, 1] = true := by decide +kernel
theorem subd14_3_25 : subd14_3 [1, 2] = true := by decide +kernel
theorem subd14_3_26 : subd14_3 [2, -3] = true := by decide +kernel
theorem subd14_3_27 : subd14_3 [2, -2] = true := by decide +kernel
theorem subd14_3_28 : subd14_3 [2, -1] = true := by decide +kernel
theorem subd14_3_29 : subd14_3 [2, 0] = true := by decide +kernel
theorem subd14_3_30 : subd14_3 [2, 1] = true := by decide +kernel
theorem subd14_3_31 : subd14_3 [3] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_cons.2 ⟨subd14_3_1, List.forall_mem_cons.2 ⟨subd14_3_2, List.forall_mem_cons.2 ⟨subd14_3_3, List.forall_mem_cons.2 ⟨subd14_3_4, List.forall_mem_cons.2 ⟨subd14_3_5, List.forall_mem_cons.2 ⟨subd14_3_6, List.forall_mem_cons.2 ⟨subd14_3_7, List.forall_mem_cons.2 ⟨subd14_3_8, List.forall_mem_cons.2 ⟨subd14_3_9, List.forall_mem_cons.2 ⟨subd14_3_10, List.forall_mem_cons.2 ⟨subd14_3_11, List.forall_mem_cons.2 ⟨subd14_3_12, List.forall_mem_cons.2 ⟨subd14_3_13, List.forall_mem_cons.2 ⟨subd14_3_14, List.forall_mem_cons.2 ⟨subd14_3_15, List.forall_mem_cons.2 ⟨subd14_3_16, List.forall_mem_cons.2 ⟨subd14_3_17, List.forall_mem_cons.2 ⟨subd14_3_18, List.forall_mem_cons.2 ⟨subd14_3_19, List.forall_mem_cons.2 ⟨subd14_3_20, List.forall_mem_cons.2 ⟨subd14_3_21, List.forall_mem_cons.2 ⟨subd14_3_22, List.forall_mem_cons.2 ⟨subd14_3_23, List.forall_mem_cons.2 ⟨subd14_3_24, List.forall_mem_cons.2 ⟨subd14_3_25, List.forall_mem_cons.2 ⟨subd14_3_26, List.forall_mem_cons.2 ⟨subd14_3_27, List.forall_mem_cons.2 ⟨subd14_3_28, List.forall_mem_cons.2 ⟨subd14_3_29, List.forall_mem_cons.2 ⟨subd14_3_30, List.forall_mem_cons.2 ⟨subd14_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_4 : ldCheck G d14_4.U d14_4.ms ldd14_4 = true := by decide +kernel
theorem pre_okd14_4 : subPre G cell14 d14_4 = true := by decide +kernel
theorem subd14_4_0 : subd14_4 [-3] = true := by decide +kernel
theorem subd14_4_1 : subd14_4 [-2, -3] = true := by decide +kernel
theorem subd14_4_2 : subd14_4 [-2, -2] = true := by decide +kernel
theorem subd14_4_3 : subd14_4 [-2, -1] = true := by decide +kernel
theorem subd14_4_4 : subd14_4 [-2, 0] = true := by decide +kernel
theorem subd14_4_5 : subd14_4 [-2, 1] = true := by decide +kernel
theorem subd14_4_6 : subd14_4 [-2, 2] = true := by decide +kernel
theorem subd14_4_7 : subd14_4 [-2, 3] = true := by decide +kernel
theorem subd14_4_8 : subd14_4 [-1, -4] = true := by decide +kernel
theorem subd14_4_9 : subd14_4 [-1, -3] = true := by decide +kernel
theorem subd14_4_10 : subd14_4 [-1, -2] = true := by decide +kernel
theorem subd14_4_11 : subd14_4 [-1, -1] = true := by decide +kernel
theorem subd14_4_12 : subd14_4 [-1, 0] = true := by decide +kernel
theorem subd14_4_13 : subd14_4 [-1, 1] = true := by decide +kernel
theorem subd14_4_14 : subd14_4 [-1, 2] = true := by decide +kernel
theorem subd14_4_15 : subd14_4 [-1, 3] = true := by decide +kernel
theorem subd14_4_16 : subd14_4 [0, -4] = true := by decide +kernel
theorem subd14_4_17 : subd14_4 [0, -3] = true := by decide +kernel
theorem subd14_4_18 : subd14_4 [0, -2] = true := by decide +kernel
theorem subd14_4_19 : subd14_4 [0, -1] = true := by decide +kernel
theorem subd14_4_20 : subd14_4 [0, 0] = true := by decide +kernel
theorem subd14_4_21 : subd14_4 [0, 1] = true := by decide +kernel
theorem subd14_4_22 : subd14_4 [0, 2] = true := by decide +kernel
theorem subd14_4_23 : subd14_4 [0, 3] = true := by decide +kernel
theorem subd14_4_24 : subd14_4 [1, -4] = true := by decide +kernel
theorem subd14_4_25 : subd14_4 [1, -3] = true := by decide +kernel
theorem subd14_4_26 : subd14_4 [1, -2] = true := by decide +kernel
theorem subd14_4_27 : subd14_4 [1, -1] = true := by decide +kernel
theorem subd14_4_28 : subd14_4 [1, 0] = true := by decide +kernel
theorem subd14_4_29 : subd14_4 [1, 1] = true := by decide +kernel
theorem subd14_4_30 : subd14_4 [1, 2] = true := by decide +kernel
theorem subd14_4_31 : subd14_4 [1, 3] = true := by decide +kernel
theorem sbd14_4_0 : ∀ q ∈ blkd14_4_0, subd14_4 q = true := by
  unfold blkd14_4_0
  exact List.forall_mem_cons.2 ⟨subd14_4_0, List.forall_mem_cons.2 ⟨subd14_4_1, List.forall_mem_cons.2 ⟨subd14_4_2, List.forall_mem_cons.2 ⟨subd14_4_3, List.forall_mem_cons.2 ⟨subd14_4_4, List.forall_mem_cons.2 ⟨subd14_4_5, List.forall_mem_cons.2 ⟨subd14_4_6, List.forall_mem_cons.2 ⟨subd14_4_7, List.forall_mem_cons.2 ⟨subd14_4_8, List.forall_mem_cons.2 ⟨subd14_4_9, List.forall_mem_cons.2 ⟨subd14_4_10, List.forall_mem_cons.2 ⟨subd14_4_11, List.forall_mem_cons.2 ⟨subd14_4_12, List.forall_mem_cons.2 ⟨subd14_4_13, List.forall_mem_cons.2 ⟨subd14_4_14, List.forall_mem_cons.2 ⟨subd14_4_15, List.forall_mem_cons.2 ⟨subd14_4_16, List.forall_mem_cons.2 ⟨subd14_4_17, List.forall_mem_cons.2 ⟨subd14_4_18, List.forall_mem_cons.2 ⟨subd14_4_19, List.forall_mem_cons.2 ⟨subd14_4_20, List.forall_mem_cons.2 ⟨subd14_4_21, List.forall_mem_cons.2 ⟨subd14_4_22, List.forall_mem_cons.2 ⟨subd14_4_23, List.forall_mem_cons.2 ⟨subd14_4_24, List.forall_mem_cons.2 ⟨subd14_4_25, List.forall_mem_cons.2 ⟨subd14_4_26, List.forall_mem_cons.2 ⟨subd14_4_27, List.forall_mem_cons.2 ⟨subd14_4_28, List.forall_mem_cons.2 ⟨subd14_4_29, List.forall_mem_cons.2 ⟨subd14_4_30, List.forall_mem_cons.2 ⟨subd14_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd14_4_32 : subd14_4 [2, -4] = true := by decide +kernel
theorem subd14_4_33 : subd14_4 [2, -3] = true := by decide +kernel
theorem subd14_4_34 : subd14_4 [2, -2] = true := by decide +kernel
theorem subd14_4_35 : subd14_4 [2, -1] = true := by decide +kernel
theorem subd14_4_36 : subd14_4 [2, 0] = true := by decide +kernel
theorem subd14_4_37 : subd14_4 [2, 1] = true := by decide +kernel
theorem subd14_4_38 : subd14_4 [2, 2] = true := by decide +kernel
theorem subd14_4_39 : subd14_4 [3] = true := by decide +kernel
theorem sbd14_4_1 : ∀ q ∈ blkd14_4_1, subd14_4 q = true := by
  unfold blkd14_4_1
  exact List.forall_mem_cons.2 ⟨subd14_4_32, List.forall_mem_cons.2 ⟨subd14_4_33, List.forall_mem_cons.2 ⟨subd14_4_34, List.forall_mem_cons.2 ⟨subd14_4_35, List.forall_mem_cons.2 ⟨subd14_4_36, List.forall_mem_cons.2 ⟨subd14_4_37, List.forall_mem_cons.2 ⟨subd14_4_38, List.forall_mem_cons.2 ⟨subd14_4_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd14_5 : ldCheck G d14_5.U d14_5.ms ldd14_5 = true := by decide +kernel
theorem pre_okd14_5 : subPre G cell14 d14_5 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C135
