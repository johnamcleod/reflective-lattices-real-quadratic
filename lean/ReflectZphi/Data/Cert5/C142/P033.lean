import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd17_1 : ldCheck G d17_1.U d17_1.ms ldd17_1 = true := by decide +kernel
theorem pre_okd17_1 : subPre G cell17 d17_1 = true := by decide +kernel
theorem subd17_1_0 : subd17_1 [-2] = true := by decide +kernel
theorem subd17_1_1 : subd17_1 [-1] = true := by decide +kernel
theorem subd17_1_2 : subd17_1 [0] = true := by decide +kernel
theorem subd17_1_3 : subd17_1 [1] = true := by decide +kernel
theorem subd17_1_4 : subd17_1 [2] = true := by decide +kernel
theorem sbd17_1_0 : ∀ q ∈ blkd17_1_0, subd17_1 q = true := by
  unfold blkd17_1_0
  exact List.forall_mem_cons.2 ⟨subd17_1_0, List.forall_mem_cons.2 ⟨subd17_1_1, List.forall_mem_cons.2 ⟨subd17_1_2, List.forall_mem_cons.2 ⟨subd17_1_3, List.forall_mem_cons.2 ⟨subd17_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd17_2 : ldCheck G d17_2.U d17_2.ms ldd17_2 = true := by decide +kernel
theorem pre_okd17_2 : subPre G cell17 d17_2 = true := by decide +kernel
theorem subd17_2_0 : subd17_2 [-4] = true := by decide +kernel
theorem subd17_2_1 : subd17_2 [-3, -4] = true := by decide +kernel
theorem subd17_2_2 : subd17_2 [-3, -3] = true := by decide +kernel
theorem subd17_2_3 : subd17_2 [-3, -2] = true := by decide +kernel
theorem subd17_2_4 : subd17_2 [-3, -1] = true := by decide +kernel
theorem subd17_2_5 : subd17_2 [-3, 0] = true := by decide +kernel
theorem subd17_2_6 : subd17_2 [-3, 1] = true := by decide +kernel
theorem subd17_2_7 : subd17_2 [-3, 2] = true := by decide +kernel
theorem subd17_2_8 : subd17_2 [-2, -5] = true := by decide +kernel
theorem subd17_2_9 : subd17_2 [-2, -4] = true := by decide +kernel
theorem subd17_2_10 : subd17_2 [-2, -3] = true := by decide +kernel
theorem subd17_2_11 : subd17_2 [-2, -2] = true := by decide +kernel
theorem subd17_2_12 : subd17_2 [-2, -1] = true := by decide +kernel
theorem subd17_2_13 : subd17_2 [-2, 0] = true := by decide +kernel
theorem subd17_2_14 : subd17_2 [-2, 1] = true := by decide +kernel
theorem subd17_2_15 : subd17_2 [-2, 2] = true := by decide +kernel
theorem subd17_2_16 : subd17_2 [-2, 3] = true := by decide +kernel
theorem subd17_2_17 : subd17_2 [-1, -5] = true := by decide +kernel
theorem subd17_2_18 : subd17_2 [-1, -4] = true := by decide +kernel
theorem subd17_2_19 : subd17_2 [-1, -3] = true := by decide +kernel
theorem subd17_2_20 : subd17_2 [-1, -2] = true := by decide +kernel
theorem subd17_2_21 : subd17_2 [-1, -1] = true := by decide +kernel
theorem subd17_2_22 : subd17_2 [-1, 0] = true := by decide +kernel
theorem subd17_2_23 : subd17_2 [-1, 1] = true := by decide +kernel
theorem subd17_2_24 : subd17_2 [-1, 2] = true := by decide +kernel
theorem subd17_2_25 : subd17_2 [-1, 3] = true := by decide +kernel
theorem subd17_2_26 : subd17_2 [-1, 4] = true := by decide +kernel
theorem subd17_2_27 : subd17_2 [0, -5] = true := by decide +kernel
theorem subd17_2_28 : subd17_2 [0, -4] = true := by decide +kernel
theorem subd17_2_29 : subd17_2 [0, -3] = true := by decide +kernel
theorem subd17_2_30 : subd17_2 [0, -2] = true := by decide +kernel
theorem subd17_2_31 : subd17_2 [0, -1] = true := by decide +kernel
theorem sbd17_2_0 : ∀ q ∈ blkd17_2_0, subd17_2 q = true := by
  unfold blkd17_2_0
  exact List.forall_mem_cons.2 ⟨subd17_2_0, List.forall_mem_cons.2 ⟨subd17_2_1, List.forall_mem_cons.2 ⟨subd17_2_2, List.forall_mem_cons.2 ⟨subd17_2_3, List.forall_mem_cons.2 ⟨subd17_2_4, List.forall_mem_cons.2 ⟨subd17_2_5, List.forall_mem_cons.2 ⟨subd17_2_6, List.forall_mem_cons.2 ⟨subd17_2_7, List.forall_mem_cons.2 ⟨subd17_2_8, List.forall_mem_cons.2 ⟨subd17_2_9, List.forall_mem_cons.2 ⟨subd17_2_10, List.forall_mem_cons.2 ⟨subd17_2_11, List.forall_mem_cons.2 ⟨subd17_2_12, List.forall_mem_cons.2 ⟨subd17_2_13, List.forall_mem_cons.2 ⟨subd17_2_14, List.forall_mem_cons.2 ⟨subd17_2_15, List.forall_mem_cons.2 ⟨subd17_2_16, List.forall_mem_cons.2 ⟨subd17_2_17, List.forall_mem_cons.2 ⟨subd17_2_18, List.forall_mem_cons.2 ⟨subd17_2_19, List.forall_mem_cons.2 ⟨subd17_2_20, List.forall_mem_cons.2 ⟨subd17_2_21, List.forall_mem_cons.2 ⟨subd17_2_22, List.forall_mem_cons.2 ⟨subd17_2_23, List.forall_mem_cons.2 ⟨subd17_2_24, List.forall_mem_cons.2 ⟨subd17_2_25, List.forall_mem_cons.2 ⟨subd17_2_26, List.forall_mem_cons.2 ⟨subd17_2_27, List.forall_mem_cons.2 ⟨subd17_2_28, List.forall_mem_cons.2 ⟨subd17_2_29, List.forall_mem_cons.2 ⟨subd17_2_30, List.forall_mem_cons.2 ⟨subd17_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd17_2_32 : subd17_2 [0, 0] = true := by decide +kernel
theorem subd17_2_33 : subd17_2 [0, 1] = true := by decide +kernel
theorem subd17_2_34 : subd17_2 [0, 2] = true := by decide +kernel
theorem subd17_2_35 : subd17_2 [0, 3] = true := by decide +kernel
theorem subd17_2_36 : subd17_2 [0, 4] = true := by decide +kernel
theorem subd17_2_37 : subd17_2 [1, -5] = true := by decide +kernel
theorem subd17_2_38 : subd17_2 [1, -4] = true := by decide +kernel
theorem subd17_2_39 : subd17_2 [1, -3] = true := by decide +kernel
theorem subd17_2_40 : subd17_2 [1, -2] = true := by decide +kernel
theorem subd17_2_41 : subd17_2 [1, -1] = true := by decide +kernel
theorem subd17_2_42 : subd17_2 [1, 0] = true := by decide +kernel
theorem subd17_2_43 : subd17_2 [1, 1] = true := by decide +kernel
theorem subd17_2_44 : subd17_2 [1, 2] = true := by decide +kernel
theorem subd17_2_45 : subd17_2 [1, 3] = true := by decide +kernel
theorem subd17_2_46 : subd17_2 [1, 4] = true := by decide +kernel
theorem subd17_2_47 : subd17_2 [2, -4] = true := by decide +kernel
theorem subd17_2_48 : subd17_2 [2, -3] = true := by decide +kernel
theorem subd17_2_49 : subd17_2 [2, -2] = true := by decide +kernel
theorem subd17_2_50 : subd17_2 [2, -1] = true := by decide +kernel
theorem subd17_2_51 : subd17_2 [2, 0] = true := by decide +kernel
theorem subd17_2_52 : subd17_2 [2, 1] = true := by decide +kernel
theorem subd17_2_53 : subd17_2 [2, 2] = true := by decide +kernel
theorem subd17_2_54 : subd17_2 [2, 3] = true := by decide +kernel
theorem subd17_2_55 : subd17_2 [2, 4] = true := by decide +kernel
theorem subd17_2_56 : subd17_2 [3, -3] = true := by decide +kernel
theorem subd17_2_57 : subd17_2 [3, -2] = true := by decide +kernel
theorem subd17_2_58 : subd17_2 [3, -1] = true := by decide +kernel
theorem subd17_2_59 : subd17_2 [3, 0] = true := by decide +kernel
theorem subd17_2_60 : subd17_2 [3, 1] = true := by decide +kernel
theorem subd17_2_61 : subd17_2 [3, 2] = true := by decide +kernel
theorem subd17_2_62 : subd17_2 [3, 3] = true := by decide +kernel
theorem subd17_2_63 : subd17_2 [4] = true := by decide +kernel
theorem sbd17_2_1 : ∀ q ∈ blkd17_2_1, subd17_2 q = true := by
  unfold blkd17_2_1
  exact List.forall_mem_cons.2 ⟨subd17_2_32, List.forall_mem_cons.2 ⟨subd17_2_33, List.forall_mem_cons.2 ⟨subd17_2_34, List.forall_mem_cons.2 ⟨subd17_2_35, List.forall_mem_cons.2 ⟨subd17_2_36, List.forall_mem_cons.2 ⟨subd17_2_37, List.forall_mem_cons.2 ⟨subd17_2_38, List.forall_mem_cons.2 ⟨subd17_2_39, List.forall_mem_cons.2 ⟨subd17_2_40, List.forall_mem_cons.2 ⟨subd17_2_41, List.forall_mem_cons.2 ⟨subd17_2_42, List.forall_mem_cons.2 ⟨subd17_2_43, List.forall_mem_cons.2 ⟨subd17_2_44, List.forall_mem_cons.2 ⟨subd17_2_45, List.forall_mem_cons.2 ⟨subd17_2_46, List.forall_mem_cons.2 ⟨subd17_2_47, List.forall_mem_cons.2 ⟨subd17_2_48, List.forall_mem_cons.2 ⟨subd17_2_49, List.forall_mem_cons.2 ⟨subd17_2_50, List.forall_mem_cons.2 ⟨subd17_2_51, List.forall_mem_cons.2 ⟨subd17_2_52, List.forall_mem_cons.2 ⟨subd17_2_53, List.forall_mem_cons.2 ⟨subd17_2_54, List.forall_mem_cons.2 ⟨subd17_2_55, List.forall_mem_cons.2 ⟨subd17_2_56, List.forall_mem_cons.2 ⟨subd17_2_57, List.forall_mem_cons.2 ⟨subd17_2_58, List.forall_mem_cons.2 ⟨subd17_2_59, List.forall_mem_cons.2 ⟨subd17_2_60, List.forall_mem_cons.2 ⟨subd17_2_61, List.forall_mem_cons.2 ⟨subd17_2_62, List.forall_mem_cons.2 ⟨subd17_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_3 : ldCheck G d17_3.U d17_3.ms ldd17_3 = true := by decide +kernel
theorem pre_okd17_3 : subPre G cell17 d17_3 = true := by decide +kernel
theorem subd17_3_0 : subd17_3 [-1] = true := by decide +kernel
theorem subd17_3_1 : subd17_3 [0] = true := by decide +kernel
theorem subd17_3_2 : subd17_3 [1] = true := by decide +kernel
theorem sbd17_3_0 : ∀ q ∈ blkd17_3_0, subd17_3 q = true := by
  unfold blkd17_3_0
  exact List.forall_mem_cons.2 ⟨subd17_3_0, List.forall_mem_cons.2 ⟨subd17_3_1, List.forall_mem_cons.2 ⟨subd17_3_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
