import ReflectZphi.Data.Cert5.C100.Base

namespace ReflectZphi.Data.Cert5.C100

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_0_32 : subd7_0 [0, 1] = true := by decide +kernel
theorem subd7_0_33 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_34 : subd7_0 [0, 3] = true := by decide +kernel
theorem subd7_0_35 : subd7_0 [0, 4] = true := by decide +kernel
theorem subd7_0_36 : subd7_0 [1, -5] = true := by decide +kernel
theorem subd7_0_37 : subd7_0 [1, -4] = true := by decide +kernel
theorem subd7_0_38 : subd7_0 [1, -3] = true := by decide +kernel
theorem subd7_0_39 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_40 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_41 : subd7_0 [1, 0] = true := by decide +kernel
theorem subd7_0_42 : subd7_0 [1, 1] = true := by decide +kernel
theorem subd7_0_43 : subd7_0 [1, 2] = true := by decide +kernel
theorem subd7_0_44 : subd7_0 [1, 3] = true := by decide +kernel
theorem subd7_0_45 : subd7_0 [1, 4] = true := by decide +kernel
theorem subd7_0_46 : subd7_0 [2, -4] = true := by decide +kernel
theorem subd7_0_47 : subd7_0 [2, -3] = true := by decide +kernel
theorem subd7_0_48 : subd7_0 [2, -2] = true := by decide +kernel
theorem subd7_0_49 : subd7_0 [2, -1] = true := by decide +kernel
theorem subd7_0_50 : subd7_0 [2, 0] = true := by decide +kernel
theorem subd7_0_51 : subd7_0 [2, 1] = true := by decide +kernel
theorem subd7_0_52 : subd7_0 [2, 2] = true := by decide +kernel
theorem subd7_0_53 : subd7_0 [2, 3] = true := by decide +kernel
theorem subd7_0_54 : subd7_0 [3, -4] = true := by decide +kernel
theorem subd7_0_55 : subd7_0 [3, -3] = true := by decide +kernel
theorem subd7_0_56 : subd7_0 [3, -2] = true := by decide +kernel
theorem subd7_0_57 : subd7_0 [3, -1] = true := by decide +kernel
theorem subd7_0_58 : subd7_0 [3, 0] = true := by decide +kernel
theorem subd7_0_59 : subd7_0 [3, 1] = true := by decide +kernel
theorem subd7_0_60 : subd7_0 [3, 2] = true := by decide +kernel
theorem subd7_0_61 : subd7_0 [4] = true := by decide +kernel
theorem sbd7_0_1 : ∀ q ∈ blkd7_0_1, subd7_0 q = true := by
  unfold blkd7_0_1
  exact List.forall_mem_cons.2 ⟨subd7_0_32, List.forall_mem_cons.2 ⟨subd7_0_33, List.forall_mem_cons.2 ⟨subd7_0_34, List.forall_mem_cons.2 ⟨subd7_0_35, List.forall_mem_cons.2 ⟨subd7_0_36, List.forall_mem_cons.2 ⟨subd7_0_37, List.forall_mem_cons.2 ⟨subd7_0_38, List.forall_mem_cons.2 ⟨subd7_0_39, List.forall_mem_cons.2 ⟨subd7_0_40, List.forall_mem_cons.2 ⟨subd7_0_41, List.forall_mem_cons.2 ⟨subd7_0_42, List.forall_mem_cons.2 ⟨subd7_0_43, List.forall_mem_cons.2 ⟨subd7_0_44, List.forall_mem_cons.2 ⟨subd7_0_45, List.forall_mem_cons.2 ⟨subd7_0_46, List.forall_mem_cons.2 ⟨subd7_0_47, List.forall_mem_cons.2 ⟨subd7_0_48, List.forall_mem_cons.2 ⟨subd7_0_49, List.forall_mem_cons.2 ⟨subd7_0_50, List.forall_mem_cons.2 ⟨subd7_0_51, List.forall_mem_cons.2 ⟨subd7_0_52, List.forall_mem_cons.2 ⟨subd7_0_53, List.forall_mem_cons.2 ⟨subd7_0_54, List.forall_mem_cons.2 ⟨subd7_0_55, List.forall_mem_cons.2 ⟨subd7_0_56, List.forall_mem_cons.2 ⟨subd7_0_57, List.forall_mem_cons.2 ⟨subd7_0_58, List.forall_mem_cons.2 ⟨subd7_0_59, List.forall_mem_cons.2 ⟨subd7_0_60, List.forall_mem_cons.2 ⟨subd7_0_61, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_0 : subd7_1 [-1, -2] = true := by decide +kernel
theorem subd7_1_1 : subd7_1 [-1, -1] = true := by decide +kernel
theorem subd7_1_2 : subd7_1 [-1, 0] = true := by decide +kernel
theorem subd7_1_3 : subd7_1 [-1, 1] = true := by decide +kernel
theorem subd7_1_4 : subd7_1 [-1, 2] = true := by decide +kernel
theorem subd7_1_5 : subd7_1 [0, -3] = true := by decide +kernel
theorem subd7_1_6 : subd7_1 [0, -2] = true := by decide +kernel
theorem subd7_1_7 : subd7_1 [0, -1] = true := by decide +kernel
theorem subd7_1_8 : subd7_1 [0, 0] = true := by decide +kernel
theorem subd7_1_9 : subd7_1 [0, 1] = true := by decide +kernel
theorem subd7_1_10 : subd7_1 [0, 2] = true := by decide +kernel
theorem subd7_1_11 : subd7_1 [1, -3] = true := by decide +kernel
theorem subd7_1_12 : subd7_1 [1, -2] = true := by decide +kernel
theorem subd7_1_13 : subd7_1 [1, -1] = true := by decide +kernel
theorem subd7_1_14 : subd7_1 [1, 0] = true := by decide +kernel
theorem subd7_1_15 : subd7_1 [1, 1] = true := by decide +kernel
theorem sbd7_1_0 : ∀ q ∈ blkd7_1_0, subd7_1 q = true := by
  unfold blkd7_1_0
  exact List.forall_mem_cons.2 ⟨subd7_1_0, List.forall_mem_cons.2 ⟨subd7_1_1, List.forall_mem_cons.2 ⟨subd7_1_2, List.forall_mem_cons.2 ⟨subd7_1_3, List.forall_mem_cons.2 ⟨subd7_1_4, List.forall_mem_cons.2 ⟨subd7_1_5, List.forall_mem_cons.2 ⟨subd7_1_6, List.forall_mem_cons.2 ⟨subd7_1_7, List.forall_mem_cons.2 ⟨subd7_1_8, List.forall_mem_cons.2 ⟨subd7_1_9, List.forall_mem_cons.2 ⟨subd7_1_10, List.forall_mem_cons.2 ⟨subd7_1_11, List.forall_mem_cons.2 ⟨subd7_1_12, List.forall_mem_cons.2 ⟨subd7_1_13, List.forall_mem_cons.2 ⟨subd7_1_14, List.forall_mem_cons.2 ⟨subd7_1_15, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_0 : subd8_0 [-2] = true := by decide +kernel
theorem subd8_0_1 : subd8_0 [-1, -3] = true := by decide +kernel
theorem subd8_0_2 : subd8_0 [-1, -2] = true := by decide +kernel
theorem subd8_0_3 : subd8_0 [-1, -1] = true := by decide +kernel
theorem subd8_0_4 : subd8_0 [-1, 0] = true := by decide +kernel
theorem subd8_0_5 : subd8_0 [-1, 1] = true := by decide +kernel
theorem subd8_0_6 : subd8_0 [-1, 2] = true := by decide +kernel
theorem subd8_0_7 : subd8_0 [0, -3] = true := by decide +kernel
theorem subd8_0_8 : subd8_0 [0, -2] = true := by decide +kernel
theorem subd8_0_9 : subd8_0 [0, -1] = true := by decide +kernel
theorem subd8_0_10 : subd8_0 [0, 0] = true := by decide +kernel
theorem subd8_0_11 : subd8_0 [0, 1] = true := by decide +kernel
theorem subd8_0_12 : subd8_0 [0, 2] = true := by decide +kernel
theorem subd8_0_13 : subd8_0 [1, -3] = true := by decide +kernel
theorem subd8_0_14 : subd8_0 [1, -2] = true := by decide +kernel
theorem subd8_0_15 : subd8_0 [1, -1] = true := by decide +kernel
theorem subd8_0_16 : subd8_0 [1, 0] = true := by decide +kernel
theorem subd8_0_17 : subd8_0 [1, 1] = true := by decide +kernel
theorem subd8_0_18 : subd8_0 [1, 2] = true := by decide +kernel
theorem subd8_0_19 : subd8_0 [2] = true := by decide +kernel
theorem sbd8_0_0 : ∀ q ∈ blkd8_0_0, subd8_0 q = true := by
  unfold blkd8_0_0
  exact List.forall_mem_cons.2 ⟨subd8_0_0, List.forall_mem_cons.2 ⟨subd8_0_1, List.forall_mem_cons.2 ⟨subd8_0_2, List.forall_mem_cons.2 ⟨subd8_0_3, List.forall_mem_cons.2 ⟨subd8_0_4, List.forall_mem_cons.2 ⟨subd8_0_5, List.forall_mem_cons.2 ⟨subd8_0_6, List.forall_mem_cons.2 ⟨subd8_0_7, List.forall_mem_cons.2 ⟨subd8_0_8, List.forall_mem_cons.2 ⟨subd8_0_9, List.forall_mem_cons.2 ⟨subd8_0_10, List.forall_mem_cons.2 ⟨subd8_0_11, List.forall_mem_cons.2 ⟨subd8_0_12, List.forall_mem_cons.2 ⟨subd8_0_13, List.forall_mem_cons.2 ⟨subd8_0_14, List.forall_mem_cons.2 ⟨subd8_0_15, List.forall_mem_cons.2 ⟨subd8_0_16, List.forall_mem_cons.2 ⟨subd8_0_17, List.forall_mem_cons.2 ⟨subd8_0_18, List.forall_mem_cons.2 ⟨subd8_0_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_0 : subd8_1 [-2] = true := by decide +kernel
theorem subd8_1_1 : subd8_1 [-1] = true := by decide +kernel
theorem subd8_1_2 : subd8_1 [0, -3] = true := by decide +kernel
theorem subd8_1_3 : subd8_1 [0, -2] = true := by decide +kernel
theorem subd8_1_4 : subd8_1 [0, -1] = true := by decide +kernel
theorem subd8_1_5 : subd8_1 [0, 0] = true := by decide +kernel
theorem subd8_1_6 : subd8_1 [0, 1] = true := by decide +kernel
theorem subd8_1_7 : subd8_1 [0, 2] = true := by decide +kernel
theorem subd8_1_8 : subd8_1 [1] = true := by decide +kernel
theorem subd8_1_9 : subd8_1 [2] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_cons.2 ⟨subd8_1_1, List.forall_mem_cons.2 ⟨subd8_1_2, List.forall_mem_cons.2 ⟨subd8_1_3, List.forall_mem_cons.2 ⟨subd8_1_4, List.forall_mem_cons.2 ⟨subd8_1_5, List.forall_mem_cons.2 ⟨subd8_1_6, List.forall_mem_cons.2 ⟨subd8_1_7, List.forall_mem_cons.2 ⟨subd8_1_8, List.forall_mem_cons.2 ⟨subd8_1_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_0_0 : subd9_0 [-1] = true := by decide +kernel
theorem subd9_0_1 : subd9_0 [0, -3] = true := by decide +kernel
theorem subd9_0_2 : subd9_0 [0, -2] = true := by decide +kernel
theorem subd9_0_3 : subd9_0 [0, -1] = true := by decide +kernel
theorem subd9_0_4 : subd9_0 [0, 0] = true := by decide +kernel
theorem subd9_0_5 : subd9_0 [0, 1] = true := by decide +kernel
theorem subd9_0_6 : subd9_0 [0, 2] = true := by decide +kernel
theorem subd9_0_7 : subd9_0 [1] = true := by decide +kernel
theorem sbd9_0_0 : ∀ q ∈ blkd9_0_0, subd9_0 q = true := by
  unfold blkd9_0_0
  exact List.forall_mem_cons.2 ⟨subd9_0_0, List.forall_mem_cons.2 ⟨subd9_0_1, List.forall_mem_cons.2 ⟨subd9_0_2, List.forall_mem_cons.2 ⟨subd9_0_3, List.forall_mem_cons.2 ⟨subd9_0_4, List.forall_mem_cons.2 ⟨subd9_0_5, List.forall_mem_cons.2 ⟨subd9_0_6, List.forall_mem_cons.2 ⟨subd9_0_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_0 : subd9_1 [-2] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-1] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [0] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [1] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [2] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C100
