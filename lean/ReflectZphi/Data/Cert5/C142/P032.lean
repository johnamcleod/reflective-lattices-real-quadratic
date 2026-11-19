import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd16_2_0 : subd16_2 [-4, -3] = true := by decide +kernel
theorem subd16_2_1 : subd16_2 [-4, -2] = true := by decide +kernel
theorem subd16_2_2 : subd16_2 [-4, -1] = true := by decide +kernel
theorem subd16_2_3 : subd16_2 [-4, 0] = true := by decide +kernel
theorem subd16_2_4 : subd16_2 [-4, 1] = true := by decide +kernel
theorem subd16_2_5 : subd16_2 [-4, 2] = true := by decide +kernel
theorem subd16_2_6 : subd16_2 [-4, 3] = true := by decide +kernel
theorem subd16_2_7 : subd16_2 [-3, -4] = true := by decide +kernel
theorem subd16_2_8 : subd16_2 [-3, -3] = true := by decide +kernel
theorem subd16_2_9 : subd16_2 [-3, -2] = true := by decide +kernel
theorem subd16_2_10 : subd16_2 [-3, -1] = true := by decide +kernel
theorem subd16_2_11 : subd16_2 [-3, 0] = true := by decide +kernel
theorem subd16_2_12 : subd16_2 [-3, 1] = true := by decide +kernel
theorem subd16_2_13 : subd16_2 [-3, 2] = true := by decide +kernel
theorem subd16_2_14 : subd16_2 [-3, 3] = true := by decide +kernel
theorem subd16_2_15 : subd16_2 [-3, 4] = true := by decide +kernel
theorem subd16_2_16 : subd16_2 [-2, -5] = true := by decide +kernel
theorem subd16_2_17 : subd16_2 [-2, -4] = true := by decide +kernel
theorem subd16_2_18 : subd16_2 [-2, -3] = true := by decide +kernel
theorem subd16_2_19 : subd16_2 [-2, -2] = true := by decide +kernel
theorem subd16_2_20 : subd16_2 [-2, -1] = true := by decide +kernel
theorem subd16_2_21 : subd16_2 [-2, 0] = true := by decide +kernel
theorem subd16_2_22 : subd16_2 [-2, 1] = true := by decide +kernel
theorem subd16_2_23 : subd16_2 [-2, 2] = true := by decide +kernel
theorem subd16_2_24 : subd16_2 [-2, 3] = true := by decide +kernel
theorem subd16_2_25 : subd16_2 [-2, 4] = true := by decide +kernel
theorem subd16_2_26 : subd16_2 [-1, -5] = true := by decide +kernel
theorem subd16_2_27 : subd16_2 [-1, -4] = true := by decide +kernel
theorem subd16_2_28 : subd16_2 [-1, -3] = true := by decide +kernel
theorem subd16_2_29 : subd16_2 [-1, -2] = true := by decide +kernel
theorem subd16_2_30 : subd16_2 [-1, -1] = true := by decide +kernel
theorem subd16_2_31 : subd16_2 [-1, 0] = true := by decide +kernel
theorem sbd16_2_0 : ∀ q ∈ blkd16_2_0, subd16_2 q = true := by
  unfold blkd16_2_0
  exact List.forall_mem_cons.2 ⟨subd16_2_0, List.forall_mem_cons.2 ⟨subd16_2_1, List.forall_mem_cons.2 ⟨subd16_2_2, List.forall_mem_cons.2 ⟨subd16_2_3, List.forall_mem_cons.2 ⟨subd16_2_4, List.forall_mem_cons.2 ⟨subd16_2_5, List.forall_mem_cons.2 ⟨subd16_2_6, List.forall_mem_cons.2 ⟨subd16_2_7, List.forall_mem_cons.2 ⟨subd16_2_8, List.forall_mem_cons.2 ⟨subd16_2_9, List.forall_mem_cons.2 ⟨subd16_2_10, List.forall_mem_cons.2 ⟨subd16_2_11, List.forall_mem_cons.2 ⟨subd16_2_12, List.forall_mem_cons.2 ⟨subd16_2_13, List.forall_mem_cons.2 ⟨subd16_2_14, List.forall_mem_cons.2 ⟨subd16_2_15, List.forall_mem_cons.2 ⟨subd16_2_16, List.forall_mem_cons.2 ⟨subd16_2_17, List.forall_mem_cons.2 ⟨subd16_2_18, List.forall_mem_cons.2 ⟨subd16_2_19, List.forall_mem_cons.2 ⟨subd16_2_20, List.forall_mem_cons.2 ⟨subd16_2_21, List.forall_mem_cons.2 ⟨subd16_2_22, List.forall_mem_cons.2 ⟨subd16_2_23, List.forall_mem_cons.2 ⟨subd16_2_24, List.forall_mem_cons.2 ⟨subd16_2_25, List.forall_mem_cons.2 ⟨subd16_2_26, List.forall_mem_cons.2 ⟨subd16_2_27, List.forall_mem_cons.2 ⟨subd16_2_28, List.forall_mem_cons.2 ⟨subd16_2_29, List.forall_mem_cons.2 ⟨subd16_2_30, List.forall_mem_cons.2 ⟨subd16_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_2_32 : subd16_2 [-1, 1] = true := by decide +kernel
theorem subd16_2_33 : subd16_2 [-1, 2] = true := by decide +kernel
theorem subd16_2_34 : subd16_2 [-1, 3] = true := by decide +kernel
theorem subd16_2_35 : subd16_2 [-1, 4] = true := by decide +kernel
theorem subd16_2_36 : subd16_2 [0, -5] = true := by decide +kernel
theorem subd16_2_37 : subd16_2 [0, -4] = true := by decide +kernel
theorem subd16_2_38 : subd16_2 [0, -3] = true := by decide +kernel
theorem subd16_2_39 : subd16_2 [0, -2] = true := by decide +kernel
theorem subd16_2_40 : subd16_2 [0, -1] = true := by decide +kernel
theorem subd16_2_41 : subd16_2 [0, 0] = true := by decide +kernel
theorem subd16_2_42 : subd16_2 [0, 1] = true := by decide +kernel
theorem subd16_2_43 : subd16_2 [0, 2] = true := by decide +kernel
theorem subd16_2_44 : subd16_2 [0, 3] = true := by decide +kernel
theorem subd16_2_45 : subd16_2 [0, 4] = true := by decide +kernel
theorem subd16_2_46 : subd16_2 [1, -5] = true := by decide +kernel
theorem subd16_2_47 : subd16_2 [1, -4] = true := by decide +kernel
theorem subd16_2_48 : subd16_2 [1, -3] = true := by decide +kernel
theorem subd16_2_49 : subd16_2 [1, -2] = true := by decide +kernel
theorem subd16_2_50 : subd16_2 [1, -1] = true := by decide +kernel
theorem subd16_2_51 : subd16_2 [1, 0] = true := by decide +kernel
theorem subd16_2_52 : subd16_2 [1, 1] = true := by decide +kernel
theorem subd16_2_53 : subd16_2 [1, 2] = true := by decide +kernel
theorem subd16_2_54 : subd16_2 [1, 3] = true := by decide +kernel
theorem subd16_2_55 : subd16_2 [1, 4] = true := by decide +kernel
theorem subd16_2_56 : subd16_2 [2, -5] = true := by decide +kernel
theorem subd16_2_57 : subd16_2 [2, -4] = true := by decide +kernel
theorem subd16_2_58 : subd16_2 [2, -3] = true := by decide +kernel
theorem subd16_2_59 : subd16_2 [2, -2] = true := by decide +kernel
theorem subd16_2_60 : subd16_2 [2, -1] = true := by decide +kernel
theorem subd16_2_61 : subd16_2 [2, 0] = true := by decide +kernel
theorem subd16_2_62 : subd16_2 [2, 1] = true := by decide +kernel
theorem subd16_2_63 : subd16_2 [2, 2] = true := by decide +kernel
theorem sbd16_2_1 : ∀ q ∈ blkd16_2_1, subd16_2 q = true := by
  unfold blkd16_2_1
  exact List.forall_mem_cons.2 ⟨subd16_2_32, List.forall_mem_cons.2 ⟨subd16_2_33, List.forall_mem_cons.2 ⟨subd16_2_34, List.forall_mem_cons.2 ⟨subd16_2_35, List.forall_mem_cons.2 ⟨subd16_2_36, List.forall_mem_cons.2 ⟨subd16_2_37, List.forall_mem_cons.2 ⟨subd16_2_38, List.forall_mem_cons.2 ⟨subd16_2_39, List.forall_mem_cons.2 ⟨subd16_2_40, List.forall_mem_cons.2 ⟨subd16_2_41, List.forall_mem_cons.2 ⟨subd16_2_42, List.forall_mem_cons.2 ⟨subd16_2_43, List.forall_mem_cons.2 ⟨subd16_2_44, List.forall_mem_cons.2 ⟨subd16_2_45, List.forall_mem_cons.2 ⟨subd16_2_46, List.forall_mem_cons.2 ⟨subd16_2_47, List.forall_mem_cons.2 ⟨subd16_2_48, List.forall_mem_cons.2 ⟨subd16_2_49, List.forall_mem_cons.2 ⟨subd16_2_50, List.forall_mem_cons.2 ⟨subd16_2_51, List.forall_mem_cons.2 ⟨subd16_2_52, List.forall_mem_cons.2 ⟨subd16_2_53, List.forall_mem_cons.2 ⟨subd16_2_54, List.forall_mem_cons.2 ⟨subd16_2_55, List.forall_mem_cons.2 ⟨subd16_2_56, List.forall_mem_cons.2 ⟨subd16_2_57, List.forall_mem_cons.2 ⟨subd16_2_58, List.forall_mem_cons.2 ⟨subd16_2_59, List.forall_mem_cons.2 ⟨subd16_2_60, List.forall_mem_cons.2 ⟨subd16_2_61, List.forall_mem_cons.2 ⟨subd16_2_62, List.forall_mem_cons.2 ⟨subd16_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd16_2_64 : subd16_2 [2, 3] = true := by decide +kernel
theorem subd16_2_65 : subd16_2 [2, 4] = true := by decide +kernel
theorem subd16_2_66 : subd16_2 [3, -5] = true := by decide +kernel
theorem subd16_2_67 : subd16_2 [3, -4] = true := by decide +kernel
theorem subd16_2_68 : subd16_2 [3, -3] = true := by decide +kernel
theorem subd16_2_69 : subd16_2 [3, -2] = true := by decide +kernel
theorem subd16_2_70 : subd16_2 [3, -1] = true := by decide +kernel
theorem subd16_2_71 : subd16_2 [3, 0] = true := by decide +kernel
theorem subd16_2_72 : subd16_2 [3, 1] = true := by decide +kernel
theorem subd16_2_73 : subd16_2 [3, 2] = true := by decide +kernel
theorem subd16_2_74 : subd16_2 [3, 3] = true := by decide +kernel
theorem subd16_2_75 : subd16_2 [4, -4] = true := by decide +kernel
theorem subd16_2_76 : subd16_2 [4, -3] = true := by decide +kernel
theorem subd16_2_77 : subd16_2 [4, -2] = true := by decide +kernel
theorem subd16_2_78 : subd16_2 [4, -1] = true := by decide +kernel
theorem subd16_2_79 : subd16_2 [4, 0] = true := by decide +kernel
theorem subd16_2_80 : subd16_2 [4, 1] = true := by decide +kernel
theorem subd16_2_81 : subd16_2 [4, 2] = true := by decide +kernel
theorem sbd16_2_2 : ∀ q ∈ blkd16_2_2, subd16_2 q = true := by
  unfold blkd16_2_2
  exact List.forall_mem_cons.2 ⟨subd16_2_64, List.forall_mem_cons.2 ⟨subd16_2_65, List.forall_mem_cons.2 ⟨subd16_2_66, List.forall_mem_cons.2 ⟨subd16_2_67, List.forall_mem_cons.2 ⟨subd16_2_68, List.forall_mem_cons.2 ⟨subd16_2_69, List.forall_mem_cons.2 ⟨subd16_2_70, List.forall_mem_cons.2 ⟨subd16_2_71, List.forall_mem_cons.2 ⟨subd16_2_72, List.forall_mem_cons.2 ⟨subd16_2_73, List.forall_mem_cons.2 ⟨subd16_2_74, List.forall_mem_cons.2 ⟨subd16_2_75, List.forall_mem_cons.2 ⟨subd16_2_76, List.forall_mem_cons.2 ⟨subd16_2_77, List.forall_mem_cons.2 ⟨subd16_2_78, List.forall_mem_cons.2 ⟨subd16_2_79, List.forall_mem_cons.2 ⟨subd16_2_80, List.forall_mem_cons.2 ⟨subd16_2_81, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd16_3 : ldCheck G d16_3.U d16_3.ms ldd16_3 = true := by decide +kernel
theorem pre_okd16_3 : subPre G cell16 d16_3 = true := by decide +kernel
theorem subd16_3_0 : subd16_3 [0, -2] = true := by decide +kernel
theorem subd16_3_1 : subd16_3 [0, -1] = true := by decide +kernel
theorem subd16_3_2 : subd16_3 [0, 0, -7] = true := by decide +kernel
theorem subd16_3_3 : subd16_3 [0, 0, -6] = true := by decide +kernel
theorem subd16_3_4 : subd16_3 [0, 0, -5] = true := by decide +kernel
theorem subd16_3_5 : subd16_3 [0, 0, -4] = true := by decide +kernel
theorem subd16_3_6 : subd16_3 [0, 0, -3] = true := by decide +kernel
theorem subd16_3_7 : subd16_3 [0, 0, -2] = true := by decide +kernel
theorem subd16_3_8 : subd16_3 [0, 0, -1] = true := by decide +kernel
theorem subd16_3_9 : subd16_3 [0, 0, 0] = true := by decide +kernel
theorem subd16_3_10 : subd16_3 [0, 0, 1] = true := by decide +kernel
theorem subd16_3_11 : subd16_3 [0, 0, 2] = true := by decide +kernel
theorem subd16_3_12 : subd16_3 [0, 0, 3] = true := by decide +kernel
theorem subd16_3_13 : subd16_3 [0, 0, 4] = true := by decide +kernel
theorem subd16_3_14 : subd16_3 [0, 0, 5] = true := by decide +kernel
theorem subd16_3_15 : subd16_3 [0, 0, 6] = true := by decide +kernel
theorem subd16_3_16 : subd16_3 [0, 1] = true := by decide +kernel
theorem sbd16_3_0 : ∀ q ∈ blkd16_3_0, subd16_3 q = true := by
  unfold blkd16_3_0
  exact List.forall_mem_cons.2 ⟨subd16_3_0, List.forall_mem_cons.2 ⟨subd16_3_1, List.forall_mem_cons.2 ⟨subd16_3_2, List.forall_mem_cons.2 ⟨subd16_3_3, List.forall_mem_cons.2 ⟨subd16_3_4, List.forall_mem_cons.2 ⟨subd16_3_5, List.forall_mem_cons.2 ⟨subd16_3_6, List.forall_mem_cons.2 ⟨subd16_3_7, List.forall_mem_cons.2 ⟨subd16_3_8, List.forall_mem_cons.2 ⟨subd16_3_9, List.forall_mem_cons.2 ⟨subd16_3_10, List.forall_mem_cons.2 ⟨subd16_3_11, List.forall_mem_cons.2 ⟨subd16_3_12, List.forall_mem_cons.2 ⟨subd16_3_13, List.forall_mem_cons.2 ⟨subd16_3_14, List.forall_mem_cons.2 ⟨subd16_3_15, List.forall_mem_cons.2 ⟨subd16_3_16, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd17_0 : ldCheck G d17_0.U d17_0.ms ldd17_0 = true := by decide +kernel
theorem pre_okd17_0 : subPre G cell17 d17_0 = true := by decide +kernel
theorem subd17_0_0 : subd17_0 [-2] = true := by decide +kernel
theorem subd17_0_1 : subd17_0 [-1] = true := by decide +kernel
theorem subd17_0_2 : subd17_0 [0, -3] = true := by decide +kernel
theorem subd17_0_3 : subd17_0 [0, -2] = true := by decide +kernel
theorem subd17_0_4 : subd17_0 [0, -1] = true := by decide +kernel
theorem subd17_0_5 : subd17_0 [0, 0] = true := by decide +kernel
theorem subd17_0_6 : subd17_0 [0, 1] = true := by decide +kernel
theorem subd17_0_7 : subd17_0 [0, 2] = true := by decide +kernel
theorem subd17_0_8 : subd17_0 [1] = true := by decide +kernel
theorem subd17_0_9 : subd17_0 [2] = true := by decide +kernel
theorem sbd17_0_0 : ∀ q ∈ blkd17_0_0, subd17_0 q = true := by
  unfold blkd17_0_0
  exact List.forall_mem_cons.2 ⟨subd17_0_0, List.forall_mem_cons.2 ⟨subd17_0_1, List.forall_mem_cons.2 ⟨subd17_0_2, List.forall_mem_cons.2 ⟨subd17_0_3, List.forall_mem_cons.2 ⟨subd17_0_4, List.forall_mem_cons.2 ⟨subd17_0_5, List.forall_mem_cons.2 ⟨subd17_0_6, List.forall_mem_cons.2 ⟨subd17_0_7, List.forall_mem_cons.2 ⟨subd17_0_8, List.forall_mem_cons.2 ⟨subd17_0_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
