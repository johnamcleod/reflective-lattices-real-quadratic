import ReflectZphi.Data.Cert5.C130.Base

namespace ReflectZphi.Data.Cert5.C130

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_0_0 : subd11_0 [-3] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-2, -3] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-2, -2] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-2, -1] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-2, 0] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-2, 1] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-2, 2] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-2, 3] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-2, 4] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-1, -4] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-1, -3] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-1, -1] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-1, 0] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [-1, 1] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [-1, 2] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [-1, 3] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [-1, 4] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [0, -5] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [0, -4] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [0, -2] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [0, -1] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [0, 0] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [0, 1] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [0, 3] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [0, 4] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [1, -5] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [1, -4] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [1, -2] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_32 : subd11_0 [1, -1] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [1, 0] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [1, 1] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [1, 2] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [1, 3] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [2, -5] = true := by decide +kernel
theorem subd11_0_38 : subd11_0 [2, -4] = true := by decide +kernel
theorem subd11_0_39 : subd11_0 [2, -3] = true := by decide +kernel
theorem subd11_0_40 : subd11_0 [2, -2] = true := by decide +kernel
theorem subd11_0_41 : subd11_0 [2, -1] = true := by decide +kernel
theorem subd11_0_42 : subd11_0 [2, 0] = true := by decide +kernel
theorem subd11_0_43 : subd11_0 [2, 1] = true := by decide +kernel
theorem subd11_0_44 : subd11_0 [2, 2] = true := by decide +kernel
theorem subd11_0_45 : subd11_0 [3] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_cons.2 ⟨subd11_0_38, List.forall_mem_cons.2 ⟨subd11_0_39, List.forall_mem_cons.2 ⟨subd11_0_40, List.forall_mem_cons.2 ⟨subd11_0_41, List.forall_mem_cons.2 ⟨subd11_0_42, List.forall_mem_cons.2 ⟨subd11_0_43, List.forall_mem_cons.2 ⟨subd11_0_44, List.forall_mem_cons.2 ⟨subd11_0_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-3] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-2, -3] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [-2, -2] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [-2, -1] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [-2, 0] = true := by decide +kernel
theorem subd11_1_5 : subd11_1 [-2, 1] = true := by decide +kernel
theorem subd11_1_6 : subd11_1 [-2, 2] = true := by decide +kernel
theorem subd11_1_7 : subd11_1 [-2, 3] = true := by decide +kernel
theorem subd11_1_8 : subd11_1 [-1, -4] = true := by decide +kernel
theorem subd11_1_9 : subd11_1 [-1, -3] = true := by decide +kernel
theorem subd11_1_10 : subd11_1 [-1, -2] = true := by decide +kernel
theorem subd11_1_11 : subd11_1 [-1, -1] = true := by decide +kernel
theorem subd11_1_12 : subd11_1 [-1, 0] = true := by decide +kernel
theorem subd11_1_13 : subd11_1 [-1, 1] = true := by decide +kernel
theorem subd11_1_14 : subd11_1 [-1, 2] = true := by decide +kernel
theorem subd11_1_15 : subd11_1 [-1, 3] = true := by decide +kernel
theorem subd11_1_16 : subd11_1 [0, -4] = true := by decide +kernel
theorem subd11_1_17 : subd11_1 [0, -3] = true := by decide +kernel
theorem subd11_1_18 : subd11_1 [0, -2] = true := by decide +kernel
theorem subd11_1_19 : subd11_1 [0, -1] = true := by decide +kernel
theorem subd11_1_20 : subd11_1 [0, 0] = true := by decide +kernel
theorem subd11_1_21 : subd11_1 [0, 1] = true := by decide +kernel
theorem subd11_1_22 : subd11_1 [0, 2] = true := by decide +kernel
theorem subd11_1_23 : subd11_1 [0, 3] = true := by decide +kernel
theorem subd11_1_24 : subd11_1 [1, -4] = true := by decide +kernel
theorem subd11_1_25 : subd11_1 [1, -3] = true := by decide +kernel
theorem subd11_1_26 : subd11_1 [1, -2] = true := by decide +kernel
theorem subd11_1_27 : subd11_1 [1, -1] = true := by decide +kernel
theorem subd11_1_28 : subd11_1 [1, 0] = true := by decide +kernel
theorem subd11_1_29 : subd11_1 [1, 1] = true := by decide +kernel
theorem subd11_1_30 : subd11_1 [1, 2] = true := by decide +kernel
theorem subd11_1_31 : subd11_1 [1, 3] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_cons.2 ⟨subd11_1_5, List.forall_mem_cons.2 ⟨subd11_1_6, List.forall_mem_cons.2 ⟨subd11_1_7, List.forall_mem_cons.2 ⟨subd11_1_8, List.forall_mem_cons.2 ⟨subd11_1_9, List.forall_mem_cons.2 ⟨subd11_1_10, List.forall_mem_cons.2 ⟨subd11_1_11, List.forall_mem_cons.2 ⟨subd11_1_12, List.forall_mem_cons.2 ⟨subd11_1_13, List.forall_mem_cons.2 ⟨subd11_1_14, List.forall_mem_cons.2 ⟨subd11_1_15, List.forall_mem_cons.2 ⟨subd11_1_16, List.forall_mem_cons.2 ⟨subd11_1_17, List.forall_mem_cons.2 ⟨subd11_1_18, List.forall_mem_cons.2 ⟨subd11_1_19, List.forall_mem_cons.2 ⟨subd11_1_20, List.forall_mem_cons.2 ⟨subd11_1_21, List.forall_mem_cons.2 ⟨subd11_1_22, List.forall_mem_cons.2 ⟨subd11_1_23, List.forall_mem_cons.2 ⟨subd11_1_24, List.forall_mem_cons.2 ⟨subd11_1_25, List.forall_mem_cons.2 ⟨subd11_1_26, List.forall_mem_cons.2 ⟨subd11_1_27, List.forall_mem_cons.2 ⟨subd11_1_28, List.forall_mem_cons.2 ⟨subd11_1_29, List.forall_mem_cons.2 ⟨subd11_1_30, List.forall_mem_cons.2 ⟨subd11_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_1_32 : subd11_1 [2, -4] = true := by decide +kernel
theorem subd11_1_33 : subd11_1 [2, -3] = true := by decide +kernel
theorem subd11_1_34 : subd11_1 [2, -2] = true := by decide +kernel
theorem subd11_1_35 : subd11_1 [2, -1] = true := by decide +kernel
theorem subd11_1_36 : subd11_1 [2, 0] = true := by decide +kernel
theorem subd11_1_37 : subd11_1 [2, 1] = true := by decide +kernel
theorem subd11_1_38 : subd11_1 [2, 2] = true := by decide +kernel
theorem subd11_1_39 : subd11_1 [3] = true := by decide +kernel
theorem sbd11_1_1 : ∀ q ∈ blkd11_1_1, subd11_1 q = true := by
  unfold blkd11_1_1
  exact List.forall_mem_cons.2 ⟨subd11_1_32, List.forall_mem_cons.2 ⟨subd11_1_33, List.forall_mem_cons.2 ⟨subd11_1_34, List.forall_mem_cons.2 ⟨subd11_1_35, List.forall_mem_cons.2 ⟨subd11_1_36, List.forall_mem_cons.2 ⟨subd11_1_37, List.forall_mem_cons.2 ⟨subd11_1_38, List.forall_mem_cons.2 ⟨subd11_1_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-2] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-1, -3] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-1, -2] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-1, -1] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-1, 0] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-1, 1] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [-1, 2] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [-1, 3] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [0, -4] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [0, 3] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [1, -4] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [1, -3] = true := by decide +kernel
theorem subd11_2_18 : subd11_2 [1, -2] = true := by decide +kernel
theorem subd11_2_19 : subd11_2 [1, -1] = true := by decide +kernel
theorem subd11_2_20 : subd11_2 [1, 0] = true := by decide +kernel
theorem subd11_2_21 : subd11_2 [1, 1] = true := by decide +kernel
theorem subd11_2_22 : subd11_2 [1, 2] = true := by decide +kernel
theorem subd11_2_23 : subd11_2 [2] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_cons.2 ⟨subd11_2_18, List.forall_mem_cons.2 ⟨subd11_2_19, List.forall_mem_cons.2 ⟨subd11_2_20, List.forall_mem_cons.2 ⟨subd11_2_21, List.forall_mem_cons.2 ⟨subd11_2_22, List.forall_mem_cons.2 ⟨subd11_2_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C130
