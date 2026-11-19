import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_4_768 : subd9_4 [4, 0, -2] = true := by decide +kernel
theorem subd9_4_769 : subd9_4 [4, 0, -1] = true := by decide +kernel
theorem subd9_4_770 : subd9_4 [4, 0, 0] = true := by decide +kernel
theorem subd9_4_771 : subd9_4 [4, 0, 1] = true := by decide +kernel
theorem subd9_4_772 : subd9_4 [4, 0, 2] = true := by decide +kernel
theorem subd9_4_773 : subd9_4 [4, 0, 3] = true := by decide +kernel
theorem subd9_4_774 : subd9_4 [4, 0, 4] = true := by decide +kernel
theorem subd9_4_775 : subd9_4 [4, 0, 5] = true := by decide +kernel
theorem subd9_4_776 : subd9_4 [4, 0, 6] = true := by decide +kernel
theorem subd9_4_777 : subd9_4 [4, 0, 7] = true := by decide +kernel
theorem subd9_4_778 : subd9_4 [4, 0, 8] = true := by decide +kernel
theorem subd9_4_779 : subd9_4 [4, 1] = true := by decide +kernel
theorem subd9_4_780 : subd9_4 [4, 2] = true := by decide +kernel
theorem subd9_4_781 : subd9_4 [4, 3] = true := by decide +kernel
theorem subd9_4_782 : subd9_4 [4, 4] = true := by decide +kernel
theorem subd9_4_783 : subd9_4 [4, 5] = true := by decide +kernel
theorem subd9_4_784 : subd9_4 [5, -5] = true := by decide +kernel
theorem subd9_4_785 : subd9_4 [5, -4] = true := by decide +kernel
theorem subd9_4_786 : subd9_4 [5, -3] = true := by decide +kernel
theorem subd9_4_787 : subd9_4 [5, -2] = true := by decide +kernel
theorem subd9_4_788 : subd9_4 [5, -1] = true := by decide +kernel
theorem subd9_4_789 : subd9_4 [5, 0] = true := by decide +kernel
theorem subd9_4_790 : subd9_4 [5, 1] = true := by decide +kernel
theorem subd9_4_791 : subd9_4 [5, 2] = true := by decide +kernel
theorem subd9_4_792 : subd9_4 [5, 3] = true := by decide +kernel
theorem subd9_4_793 : subd9_4 [5, 4] = true := by decide +kernel
theorem subd9_4_794 : subd9_4 [5, 5] = true := by decide +kernel
theorem subd9_4_795 : subd9_4 [6, -4] = true := by decide +kernel
theorem subd9_4_796 : subd9_4 [6, -3] = true := by decide +kernel
theorem subd9_4_797 : subd9_4 [6, -2] = true := by decide +kernel
theorem subd9_4_798 : subd9_4 [6, -1] = true := by decide +kernel
theorem subd9_4_799 : subd9_4 [6, 0] = true := by decide +kernel
theorem sbd9_4_24 : ∀ q ∈ blkd9_4_24, subd9_4 q = true := by
  unfold blkd9_4_24
  exact List.forall_mem_cons.2 ⟨subd9_4_768, List.forall_mem_cons.2 ⟨subd9_4_769, List.forall_mem_cons.2 ⟨subd9_4_770, List.forall_mem_cons.2 ⟨subd9_4_771, List.forall_mem_cons.2 ⟨subd9_4_772, List.forall_mem_cons.2 ⟨subd9_4_773, List.forall_mem_cons.2 ⟨subd9_4_774, List.forall_mem_cons.2 ⟨subd9_4_775, List.forall_mem_cons.2 ⟨subd9_4_776, List.forall_mem_cons.2 ⟨subd9_4_777, List.forall_mem_cons.2 ⟨subd9_4_778, List.forall_mem_cons.2 ⟨subd9_4_779, List.forall_mem_cons.2 ⟨subd9_4_780, List.forall_mem_cons.2 ⟨subd9_4_781, List.forall_mem_cons.2 ⟨subd9_4_782, List.forall_mem_cons.2 ⟨subd9_4_783, List.forall_mem_cons.2 ⟨subd9_4_784, List.forall_mem_cons.2 ⟨subd9_4_785, List.forall_mem_cons.2 ⟨subd9_4_786, List.forall_mem_cons.2 ⟨subd9_4_787, List.forall_mem_cons.2 ⟨subd9_4_788, List.forall_mem_cons.2 ⟨subd9_4_789, List.forall_mem_cons.2 ⟨subd9_4_790, List.forall_mem_cons.2 ⟨subd9_4_791, List.forall_mem_cons.2 ⟨subd9_4_792, List.forall_mem_cons.2 ⟨subd9_4_793, List.forall_mem_cons.2 ⟨subd9_4_794, List.forall_mem_cons.2 ⟨subd9_4_795, List.forall_mem_cons.2 ⟨subd9_4_796, List.forall_mem_cons.2 ⟨subd9_4_797, List.forall_mem_cons.2 ⟨subd9_4_798, List.forall_mem_cons.2 ⟨subd9_4_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_4_800 : subd9_4 [6, 1] = true := by decide +kernel
theorem subd9_4_801 : subd9_4 [6, 2] = true := by decide +kernel
theorem subd9_4_802 : subd9_4 [6, 3] = true := by decide +kernel
theorem subd9_4_803 : subd9_4 [6, 4] = true := by decide +kernel
theorem subd9_4_804 : subd9_4 [7] = true := by decide +kernel
theorem sbd9_4_25 : ∀ q ∈ blkd9_4_25, subd9_4 q = true := by
  unfold blkd9_4_25
  exact List.forall_mem_cons.2 ⟨subd9_4_800, List.forall_mem_cons.2 ⟨subd9_4_801, List.forall_mem_cons.2 ⟨subd9_4_802, List.forall_mem_cons.2 ⟨subd9_4_803, List.forall_mem_cons.2 ⟨subd9_4_804, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd9_5 : ldCheck G d9_5.U d9_5.ms ldd9_5 = true := by decide +kernel
theorem pre_okd9_5 : subPre G cell9 d9_5 = true := by decide +kernel
theorem subd9_5_0 : subd9_5 [-3, -3] = true := by decide +kernel
theorem subd9_5_1 : subd9_5 [-3, -2] = true := by decide +kernel
theorem subd9_5_2 : subd9_5 [-3, -1] = true := by decide +kernel
theorem subd9_5_3 : subd9_5 [-3, 0, -6] = true := by decide +kernel
theorem subd9_5_4 : subd9_5 [-3, 0, -5] = true := by decide +kernel
theorem subd9_5_5 : subd9_5 [-3, 0, -4] = true := by decide +kernel
theorem subd9_5_6 : subd9_5 [-3, 0, -3] = true := by decide +kernel
theorem subd9_5_7 : subd9_5 [-3, 0, -2] = true := by decide +kernel
theorem subd9_5_8 : subd9_5 [-3, 0, -1] = true := by decide +kernel
theorem subd9_5_9 : subd9_5 [-3, 0, 0] = true := by decide +kernel
theorem subd9_5_10 : subd9_5 [-3, 0, 1] = true := by decide +kernel
theorem subd9_5_11 : subd9_5 [-3, 0, 2] = true := by decide +kernel
theorem subd9_5_12 : subd9_5 [-3, 0, 3] = true := by decide +kernel
theorem subd9_5_13 : subd9_5 [-3, 0, 4] = true := by decide +kernel
theorem subd9_5_14 : subd9_5 [-3, 0, 5] = true := by decide +kernel
theorem subd9_5_15 : subd9_5 [-3, 0, 6] = true := by decide +kernel
theorem subd9_5_16 : subd9_5 [-3, 0, 7] = true := by decide +kernel
theorem subd9_5_17 : subd9_5 [-3, 1] = true := by decide +kernel
theorem subd9_5_18 : subd9_5 [-3, 2] = true := by decide +kernel
theorem subd9_5_19 : subd9_5 [-2, -4] = true := by decide +kernel
theorem subd9_5_20 : subd9_5 [-2, -3] = true := by decide +kernel
theorem subd9_5_21 : subd9_5 [-2, -2, -7] = true := by decide +kernel
theorem subd9_5_22 : subd9_5 [-2, -2, -6] = true := by decide +kernel
theorem subd9_5_23 : subd9_5 [-2, -2, -5] = true := by decide +kernel
theorem subd9_5_24 : subd9_5 [-2, -2, -4] = true := by decide +kernel
theorem subd9_5_25 : subd9_5 [-2, -2, -3] = true := by decide +kernel
theorem subd9_5_26 : subd9_5 [-2, -2, -2] = true := by decide +kernel
theorem subd9_5_27 : subd9_5 [-2, -2, -1] = true := by decide +kernel
theorem subd9_5_28 : subd9_5 [-2, -2, 0] = true := by decide +kernel
theorem subd9_5_29 : subd9_5 [-2, -2, 1] = true := by decide +kernel
theorem subd9_5_30 : subd9_5 [-2, -2, 2] = true := by decide +kernel
theorem subd9_5_31 : subd9_5 [-2, -2, 3] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_cons.2 ⟨subd9_5_1, List.forall_mem_cons.2 ⟨subd9_5_2, List.forall_mem_cons.2 ⟨subd9_5_3, List.forall_mem_cons.2 ⟨subd9_5_4, List.forall_mem_cons.2 ⟨subd9_5_5, List.forall_mem_cons.2 ⟨subd9_5_6, List.forall_mem_cons.2 ⟨subd9_5_7, List.forall_mem_cons.2 ⟨subd9_5_8, List.forall_mem_cons.2 ⟨subd9_5_9, List.forall_mem_cons.2 ⟨subd9_5_10, List.forall_mem_cons.2 ⟨subd9_5_11, List.forall_mem_cons.2 ⟨subd9_5_12, List.forall_mem_cons.2 ⟨subd9_5_13, List.forall_mem_cons.2 ⟨subd9_5_14, List.forall_mem_cons.2 ⟨subd9_5_15, List.forall_mem_cons.2 ⟨subd9_5_16, List.forall_mem_cons.2 ⟨subd9_5_17, List.forall_mem_cons.2 ⟨subd9_5_18, List.forall_mem_cons.2 ⟨subd9_5_19, List.forall_mem_cons.2 ⟨subd9_5_20, List.forall_mem_cons.2 ⟨subd9_5_21, List.forall_mem_cons.2 ⟨subd9_5_22, List.forall_mem_cons.2 ⟨subd9_5_23, List.forall_mem_cons.2 ⟨subd9_5_24, List.forall_mem_cons.2 ⟨subd9_5_25, List.forall_mem_cons.2 ⟨subd9_5_26, List.forall_mem_cons.2 ⟨subd9_5_27, List.forall_mem_cons.2 ⟨subd9_5_28, List.forall_mem_cons.2 ⟨subd9_5_29, List.forall_mem_cons.2 ⟨subd9_5_30, List.forall_mem_cons.2 ⟨subd9_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_32 : subd9_5 [-2, -2, 4] = true := by decide +kernel
theorem subd9_5_33 : subd9_5 [-2, -2, 5] = true := by decide +kernel
theorem subd9_5_34 : subd9_5 [-2, -2, 6] = true := by decide +kernel
theorem subd9_5_35 : subd9_5 [-2, -2, 7] = true := by decide +kernel
theorem subd9_5_36 : subd9_5 [-2, -2, 8] = true := by decide +kernel
theorem subd9_5_37 : subd9_5 [-2, -1, -9] = true := by decide +kernel
theorem subd9_5_38 : subd9_5 [-2, -1, -8] = true := by decide +kernel
theorem subd9_5_39 : subd9_5 [-2, -1, -7] = true := by decide +kernel
theorem subd9_5_40 : subd9_5 [-2, -1, -6] = true := by decide +kernel
theorem subd9_5_41 : subd9_5 [-2, -1, -5] = true := by decide +kernel
theorem subd9_5_42 : subd9_5 [-2, -1, -4] = true := by decide +kernel
theorem subd9_5_43 : subd9_5 [-2, -1, -3] = true := by decide +kernel
theorem subd9_5_44 : subd9_5 [-2, -1, -2] = true := by decide +kernel
theorem subd9_5_45 : subd9_5 [-2, -1, -1] = true := by decide +kernel
theorem subd9_5_46 : subd9_5 [-2, -1, 0] = true := by decide +kernel
theorem subd9_5_47 : subd9_5 [-2, -1, 1] = true := by decide +kernel
theorem subd9_5_48 : subd9_5 [-2, -1, 2] = true := by decide +kernel
theorem subd9_5_49 : subd9_5 [-2, -1, 3] = true := by decide +kernel
theorem subd9_5_50 : subd9_5 [-2, -1, 4] = true := by decide +kernel
theorem subd9_5_51 : subd9_5 [-2, -1, 5] = true := by decide +kernel
theorem subd9_5_52 : subd9_5 [-2, -1, 6] = true := by decide +kernel
theorem subd9_5_53 : subd9_5 [-2, -1, 7] = true := by decide +kernel
theorem subd9_5_54 : subd9_5 [-2, -1, 8] = true := by decide +kernel
theorem subd9_5_55 : subd9_5 [-2, -1, 9] = true := by decide +kernel
theorem subd9_5_56 : subd9_5 [-2, 0, -9] = true := by decide +kernel
theorem subd9_5_57 : subd9_5 [-2, 0, -8] = true := by decide +kernel
theorem subd9_5_58 : subd9_5 [-2, 0, -7] = true := by decide +kernel
theorem subd9_5_59 : subd9_5 [-2, 0, -6] = true := by decide +kernel
theorem subd9_5_60 : subd9_5 [-2, 0, -5] = true := by decide +kernel
theorem subd9_5_61 : subd9_5 [-2, 0, -4] = true := by decide +kernel
theorem subd9_5_62 : subd9_5 [-2, 0, -3] = true := by decide +kernel
theorem subd9_5_63 : subd9_5 [-2, 0, -2] = true := by decide +kernel
theorem sbd9_5_1 : ∀ q ∈ blkd9_5_1, subd9_5 q = true := by
  unfold blkd9_5_1
  exact List.forall_mem_cons.2 ⟨subd9_5_32, List.forall_mem_cons.2 ⟨subd9_5_33, List.forall_mem_cons.2 ⟨subd9_5_34, List.forall_mem_cons.2 ⟨subd9_5_35, List.forall_mem_cons.2 ⟨subd9_5_36, List.forall_mem_cons.2 ⟨subd9_5_37, List.forall_mem_cons.2 ⟨subd9_5_38, List.forall_mem_cons.2 ⟨subd9_5_39, List.forall_mem_cons.2 ⟨subd9_5_40, List.forall_mem_cons.2 ⟨subd9_5_41, List.forall_mem_cons.2 ⟨subd9_5_42, List.forall_mem_cons.2 ⟨subd9_5_43, List.forall_mem_cons.2 ⟨subd9_5_44, List.forall_mem_cons.2 ⟨subd9_5_45, List.forall_mem_cons.2 ⟨subd9_5_46, List.forall_mem_cons.2 ⟨subd9_5_47, List.forall_mem_cons.2 ⟨subd9_5_48, List.forall_mem_cons.2 ⟨subd9_5_49, List.forall_mem_cons.2 ⟨subd9_5_50, List.forall_mem_cons.2 ⟨subd9_5_51, List.forall_mem_cons.2 ⟨subd9_5_52, List.forall_mem_cons.2 ⟨subd9_5_53, List.forall_mem_cons.2 ⟨subd9_5_54, List.forall_mem_cons.2 ⟨subd9_5_55, List.forall_mem_cons.2 ⟨subd9_5_56, List.forall_mem_cons.2 ⟨subd9_5_57, List.forall_mem_cons.2 ⟨subd9_5_58, List.forall_mem_cons.2 ⟨subd9_5_59, List.forall_mem_cons.2 ⟨subd9_5_60, List.forall_mem_cons.2 ⟨subd9_5_61, List.forall_mem_cons.2 ⟨subd9_5_62, List.forall_mem_cons.2 ⟨subd9_5_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_64 : subd9_5 [-2, 0, -1] = true := by decide +kernel
theorem subd9_5_65 : subd9_5 [-2, 0, 0] = true := by decide +kernel
theorem subd9_5_66 : subd9_5 [-2, 0, 1] = true := by decide +kernel
theorem subd9_5_67 : subd9_5 [-2, 0, 2] = true := by decide +kernel
theorem subd9_5_68 : subd9_5 [-2, 0, 3] = true := by decide +kernel
theorem subd9_5_69 : subd9_5 [-2, 0, 4] = true := by decide +kernel
theorem subd9_5_70 : subd9_5 [-2, 0, 5] = true := by decide +kernel
theorem subd9_5_71 : subd9_5 [-2, 0, 6] = true := by decide +kernel
theorem subd9_5_72 : subd9_5 [-2, 0, 7] = true := by decide +kernel
theorem subd9_5_73 : subd9_5 [-2, 0, 8] = true := by decide +kernel
theorem subd9_5_74 : subd9_5 [-2, 0, 9] = true := by decide +kernel
theorem subd9_5_75 : subd9_5 [-2, 0, 10] = true := by decide +kernel
theorem subd9_5_76 : subd9_5 [-2, 1, -9] = true := by decide +kernel
theorem subd9_5_77 : subd9_5 [-2, 1, -8] = true := by decide +kernel
theorem subd9_5_78 : subd9_5 [-2, 1, -7] = true := by decide +kernel
theorem subd9_5_79 : subd9_5 [-2, 1, -6] = true := by decide +kernel
theorem subd9_5_80 : subd9_5 [-2, 1, -5] = true := by decide +kernel
theorem subd9_5_81 : subd9_5 [-2, 1, -4] = true := by decide +kernel
theorem subd9_5_82 : subd9_5 [-2, 1, -3] = true := by decide +kernel
theorem subd9_5_83 : subd9_5 [-2, 1, -2] = true := by decide +kernel
theorem subd9_5_84 : subd9_5 [-2, 1, -1] = true := by decide +kernel
theorem subd9_5_85 : subd9_5 [-2, 1, 0] = true := by decide +kernel
theorem subd9_5_86 : subd9_5 [-2, 1, 1] = true := by decide +kernel
theorem subd9_5_87 : subd9_5 [-2, 1, 2] = true := by decide +kernel
theorem subd9_5_88 : subd9_5 [-2, 1, 3] = true := by decide +kernel
theorem subd9_5_89 : subd9_5 [-2, 1, 4] = true := by decide +kernel
theorem subd9_5_90 : subd9_5 [-2, 1, 5] = true := by decide +kernel
theorem subd9_5_91 : subd9_5 [-2, 1, 6] = true := by decide +kernel
theorem subd9_5_92 : subd9_5 [-2, 1, 7] = true := by decide +kernel
theorem subd9_5_93 : subd9_5 [-2, 1, 8] = true := by decide +kernel
theorem subd9_5_94 : subd9_5 [-2, 1, 9] = true := by decide +kernel
theorem subd9_5_95 : subd9_5 [-2, 2, -8] = true := by decide +kernel
theorem sbd9_5_2 : ∀ q ∈ blkd9_5_2, subd9_5 q = true := by
  unfold blkd9_5_2
  exact List.forall_mem_cons.2 ⟨subd9_5_64, List.forall_mem_cons.2 ⟨subd9_5_65, List.forall_mem_cons.2 ⟨subd9_5_66, List.forall_mem_cons.2 ⟨subd9_5_67, List.forall_mem_cons.2 ⟨subd9_5_68, List.forall_mem_cons.2 ⟨subd9_5_69, List.forall_mem_cons.2 ⟨subd9_5_70, List.forall_mem_cons.2 ⟨subd9_5_71, List.forall_mem_cons.2 ⟨subd9_5_72, List.forall_mem_cons.2 ⟨subd9_5_73, List.forall_mem_cons.2 ⟨subd9_5_74, List.forall_mem_cons.2 ⟨subd9_5_75, List.forall_mem_cons.2 ⟨subd9_5_76, List.forall_mem_cons.2 ⟨subd9_5_77, List.forall_mem_cons.2 ⟨subd9_5_78, List.forall_mem_cons.2 ⟨subd9_5_79, List.forall_mem_cons.2 ⟨subd9_5_80, List.forall_mem_cons.2 ⟨subd9_5_81, List.forall_mem_cons.2 ⟨subd9_5_82, List.forall_mem_cons.2 ⟨subd9_5_83, List.forall_mem_cons.2 ⟨subd9_5_84, List.forall_mem_cons.2 ⟨subd9_5_85, List.forall_mem_cons.2 ⟨subd9_5_86, List.forall_mem_cons.2 ⟨subd9_5_87, List.forall_mem_cons.2 ⟨subd9_5_88, List.forall_mem_cons.2 ⟨subd9_5_89, List.forall_mem_cons.2 ⟨subd9_5_90, List.forall_mem_cons.2 ⟨subd9_5_91, List.forall_mem_cons.2 ⟨subd9_5_92, List.forall_mem_cons.2 ⟨subd9_5_93, List.forall_mem_cons.2 ⟨subd9_5_94, List.forall_mem_cons.2 ⟨subd9_5_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_96 : subd9_5 [-2, 2, -7] = true := by decide +kernel
theorem subd9_5_97 : subd9_5 [-2, 2, -6] = true := by decide +kernel
theorem subd9_5_98 : subd9_5 [-2, 2, -5] = true := by decide +kernel
theorem subd9_5_99 : subd9_5 [-2, 2, -4] = true := by decide +kernel
theorem subd9_5_100 : subd9_5 [-2, 2, -3] = true := by decide +kernel
theorem subd9_5_101 : subd9_5 [-2, 2, -2] = true := by decide +kernel
theorem subd9_5_102 : subd9_5 [-2, 2, -1] = true := by decide +kernel
theorem subd9_5_103 : subd9_5 [-2, 2, 0] = true := by decide +kernel
theorem subd9_5_104 : subd9_5 [-2, 2, 1] = true := by decide +kernel
theorem subd9_5_105 : subd9_5 [-2, 2, 2] = true := by decide +kernel
theorem subd9_5_106 : subd9_5 [-2, 2, 3] = true := by decide +kernel
theorem subd9_5_107 : subd9_5 [-2, 2, 4] = true := by decide +kernel
theorem subd9_5_108 : subd9_5 [-2, 2, 5] = true := by decide +kernel
theorem subd9_5_109 : subd9_5 [-2, 2, 6] = true := by decide +kernel
theorem subd9_5_110 : subd9_5 [-2, 2, 7] = true := by decide +kernel
theorem subd9_5_111 : subd9_5 [-2, 3] = true := by decide +kernel
theorem subd9_5_112 : subd9_5 [-1, -4] = true := by decide +kernel
theorem subd9_5_113 : subd9_5 [-1, -3] = true := by decide +kernel
theorem subd9_5_114 : subd9_5 [-1, -2, -9] = true := by decide +kernel
theorem subd9_5_115 : subd9_5 [-1, -2, -8] = true := by decide +kernel
theorem subd9_5_116 : subd9_5 [-1, -2, -7] = true := by decide +kernel
theorem subd9_5_117 : subd9_5 [-1, -2, -6] = true := by decide +kernel
theorem subd9_5_118 : subd9_5 [-1, -2, -5] = true := by decide +kernel
theorem subd9_5_119 : subd9_5 [-1, -2, -4] = true := by decide +kernel
theorem subd9_5_120 : subd9_5 [-1, -2, -3] = true := by decide +kernel
theorem subd9_5_121 : subd9_5 [-1, -2, -2] = true := by decide +kernel
theorem subd9_5_122 : subd9_5 [-1, -2, -1] = true := by decide +kernel
theorem subd9_5_123 : subd9_5 [-1, -2, 0] = true := by decide +kernel
theorem subd9_5_124 : subd9_5 [-1, -2, 1] = true := by decide +kernel
theorem subd9_5_125 : subd9_5 [-1, -2, 2] = true := by decide +kernel
theorem subd9_5_126 : subd9_5 [-1, -2, 3] = true := by decide +kernel
theorem subd9_5_127 : subd9_5 [-1, -2, 4] = true := by decide +kernel
theorem sbd9_5_3 : ∀ q ∈ blkd9_5_3, subd9_5 q = true := by
  unfold blkd9_5_3
  exact List.forall_mem_cons.2 ⟨subd9_5_96, List.forall_mem_cons.2 ⟨subd9_5_97, List.forall_mem_cons.2 ⟨subd9_5_98, List.forall_mem_cons.2 ⟨subd9_5_99, List.forall_mem_cons.2 ⟨subd9_5_100, List.forall_mem_cons.2 ⟨subd9_5_101, List.forall_mem_cons.2 ⟨subd9_5_102, List.forall_mem_cons.2 ⟨subd9_5_103, List.forall_mem_cons.2 ⟨subd9_5_104, List.forall_mem_cons.2 ⟨subd9_5_105, List.forall_mem_cons.2 ⟨subd9_5_106, List.forall_mem_cons.2 ⟨subd9_5_107, List.forall_mem_cons.2 ⟨subd9_5_108, List.forall_mem_cons.2 ⟨subd9_5_109, List.forall_mem_cons.2 ⟨subd9_5_110, List.forall_mem_cons.2 ⟨subd9_5_111, List.forall_mem_cons.2 ⟨subd9_5_112, List.forall_mem_cons.2 ⟨subd9_5_113, List.forall_mem_cons.2 ⟨subd9_5_114, List.forall_mem_cons.2 ⟨subd9_5_115, List.forall_mem_cons.2 ⟨subd9_5_116, List.forall_mem_cons.2 ⟨subd9_5_117, List.forall_mem_cons.2 ⟨subd9_5_118, List.forall_mem_cons.2 ⟨subd9_5_119, List.forall_mem_cons.2 ⟨subd9_5_120, List.forall_mem_cons.2 ⟨subd9_5_121, List.forall_mem_cons.2 ⟨subd9_5_122, List.forall_mem_cons.2 ⟨subd9_5_123, List.forall_mem_cons.2 ⟨subd9_5_124, List.forall_mem_cons.2 ⟨subd9_5_125, List.forall_mem_cons.2 ⟨subd9_5_126, List.forall_mem_cons.2 ⟨subd9_5_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_128 : subd9_5 [-1, -2, 5] = true := by decide +kernel
theorem subd9_5_129 : subd9_5 [-1, -2, 6] = true := by decide +kernel
theorem subd9_5_130 : subd9_5 [-1, -2, 7] = true := by decide +kernel
theorem subd9_5_131 : subd9_5 [-1, -2, 8] = true := by decide +kernel
theorem subd9_5_132 : subd9_5 [-1, -2, 9] = true := by decide +kernel
theorem subd9_5_133 : subd9_5 [-1, -1, -11] = true := by decide +kernel
theorem subd9_5_134 : subd9_5 [-1, -1, -10] = true := by decide +kernel
theorem subd9_5_135 : subd9_5 [-1, -1, -9] = true := by decide +kernel
theorem subd9_5_136 : subd9_5 [-1, -1, -8] = true := by decide +kernel
theorem subd9_5_137 : subd9_5 [-1, -1, -7] = true := by decide +kernel
theorem subd9_5_138 : subd9_5 [-1, -1, -6] = true := by decide +kernel
theorem subd9_5_139 : subd9_5 [-1, -1, -5] = true := by decide +kernel
theorem subd9_5_140 : subd9_5 [-1, -1, -4] = true := by decide +kernel
theorem subd9_5_141 : subd9_5 [-1, -1, -3] = true := by decide +kernel
theorem subd9_5_142 : subd9_5 [-1, -1, -2] = true := by decide +kernel
theorem subd9_5_143 : subd9_5 [-1, -1, -1] = true := by decide +kernel
theorem subd9_5_144 : subd9_5 [-1, -1, 0] = true := by decide +kernel
theorem subd9_5_145 : subd9_5 [-1, -1, 1] = true := by decide +kernel
theorem subd9_5_146 : subd9_5 [-1, -1, 2] = true := by decide +kernel
theorem subd9_5_147 : subd9_5 [-1, -1, 3] = true := by decide +kernel
theorem subd9_5_148 : subd9_5 [-1, -1, 4] = true := by decide +kernel
theorem subd9_5_149 : subd9_5 [-1, -1, 5] = true := by decide +kernel
theorem subd9_5_150 : subd9_5 [-1, -1, 6] = true := by decide +kernel
theorem subd9_5_151 : subd9_5 [-1, -1, 7] = true := by decide +kernel
theorem subd9_5_152 : subd9_5 [-1, -1, 8] = true := by decide +kernel
theorem subd9_5_153 : subd9_5 [-1, -1, 9] = true := by decide +kernel
theorem subd9_5_154 : subd9_5 [-1, -1, 10] = true := by decide +kernel
theorem subd9_5_155 : subd9_5 [-1, -1, 11] = true := by decide +kernel
theorem subd9_5_156 : subd9_5 [-1, 0, -11] = true := by decide +kernel
theorem subd9_5_157 : subd9_5 [-1, 0, -10] = true := by decide +kernel
theorem subd9_5_158 : subd9_5 [-1, 0, -9] = true := by decide +kernel
theorem subd9_5_159 : subd9_5 [-1, 0, -8] = true := by decide +kernel
theorem sbd9_5_4 : ∀ q ∈ blkd9_5_4, subd9_5 q = true := by
  unfold blkd9_5_4
  exact List.forall_mem_cons.2 ⟨subd9_5_128, List.forall_mem_cons.2 ⟨subd9_5_129, List.forall_mem_cons.2 ⟨subd9_5_130, List.forall_mem_cons.2 ⟨subd9_5_131, List.forall_mem_cons.2 ⟨subd9_5_132, List.forall_mem_cons.2 ⟨subd9_5_133, List.forall_mem_cons.2 ⟨subd9_5_134, List.forall_mem_cons.2 ⟨subd9_5_135, List.forall_mem_cons.2 ⟨subd9_5_136, List.forall_mem_cons.2 ⟨subd9_5_137, List.forall_mem_cons.2 ⟨subd9_5_138, List.forall_mem_cons.2 ⟨subd9_5_139, List.forall_mem_cons.2 ⟨subd9_5_140, List.forall_mem_cons.2 ⟨subd9_5_141, List.forall_mem_cons.2 ⟨subd9_5_142, List.forall_mem_cons.2 ⟨subd9_5_143, List.forall_mem_cons.2 ⟨subd9_5_144, List.forall_mem_cons.2 ⟨subd9_5_145, List.forall_mem_cons.2 ⟨subd9_5_146, List.forall_mem_cons.2 ⟨subd9_5_147, List.forall_mem_cons.2 ⟨subd9_5_148, List.forall_mem_cons.2 ⟨subd9_5_149, List.forall_mem_cons.2 ⟨subd9_5_150, List.forall_mem_cons.2 ⟨subd9_5_151, List.forall_mem_cons.2 ⟨subd9_5_152, List.forall_mem_cons.2 ⟨subd9_5_153, List.forall_mem_cons.2 ⟨subd9_5_154, List.forall_mem_cons.2 ⟨subd9_5_155, List.forall_mem_cons.2 ⟨subd9_5_156, List.forall_mem_cons.2 ⟨subd9_5_157, List.forall_mem_cons.2 ⟨subd9_5_158, List.forall_mem_cons.2 ⟨subd9_5_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_160 : subd9_5 [-1, 0, -7] = true := by decide +kernel
theorem subd9_5_161 : subd9_5 [-1, 0, -6] = true := by decide +kernel
theorem subd9_5_162 : subd9_5 [-1, 0, -5] = true := by decide +kernel
theorem subd9_5_163 : subd9_5 [-1, 0, -4] = true := by decide +kernel
theorem subd9_5_164 : subd9_5 [-1, 0, -3] = true := by decide +kernel
theorem subd9_5_165 : subd9_5 [-1, 0, -2] = true := by decide +kernel
theorem subd9_5_166 : subd9_5 [-1, 0, -1] = true := by decide +kernel
theorem subd9_5_167 : subd9_5 [-1, 0, 0] = true := by decide +kernel
theorem subd9_5_168 : subd9_5 [-1, 0, 1] = true := by decide +kernel
theorem subd9_5_169 : subd9_5 [-1, 0, 2] = true := by decide +kernel
theorem subd9_5_170 : subd9_5 [-1, 0, 3] = true := by decide +kernel
theorem subd9_5_171 : subd9_5 [-1, 0, 4] = true := by decide +kernel
theorem subd9_5_172 : subd9_5 [-1, 0, 5] = true := by decide +kernel
theorem subd9_5_173 : subd9_5 [-1, 0, 6] = true := by decide +kernel
theorem subd9_5_174 : subd9_5 [-1, 0, 7] = true := by decide +kernel
theorem subd9_5_175 : subd9_5 [-1, 0, 8] = true := by decide +kernel
theorem subd9_5_176 : subd9_5 [-1, 0, 9] = true := by decide +kernel
theorem subd9_5_177 : subd9_5 [-1, 0, 10] = true := by decide +kernel
theorem subd9_5_178 : subd9_5 [-1, 0, 11] = true := by decide +kernel
theorem subd9_5_179 : subd9_5 [-1, 1, -11] = true := by decide +kernel
theorem subd9_5_180 : subd9_5 [-1, 1, -10] = true := by decide +kernel
theorem subd9_5_181 : subd9_5 [-1, 1, -9] = true := by decide +kernel
theorem subd9_5_182 : subd9_5 [-1, 1, -8] = true := by decide +kernel
theorem subd9_5_183 : subd9_5 [-1, 1, -7] = true := by decide +kernel
theorem subd9_5_184 : subd9_5 [-1, 1, -6] = true := by decide +kernel
theorem subd9_5_185 : subd9_5 [-1, 1, -5] = true := by decide +kernel
theorem subd9_5_186 : subd9_5 [-1, 1, -4] = true := by decide +kernel
theorem subd9_5_187 : subd9_5 [-1, 1, -3] = true := by decide +kernel
theorem subd9_5_188 : subd9_5 [-1, 1, -2] = true := by decide +kernel
theorem subd9_5_189 : subd9_5 [-1, 1, -1] = true := by decide +kernel
theorem subd9_5_190 : subd9_5 [-1, 1, 0] = true := by decide +kernel
theorem subd9_5_191 : subd9_5 [-1, 1, 1] = true := by decide +kernel
theorem sbd9_5_5 : ∀ q ∈ blkd9_5_5, subd9_5 q = true := by
  unfold blkd9_5_5
  exact List.forall_mem_cons.2 ⟨subd9_5_160, List.forall_mem_cons.2 ⟨subd9_5_161, List.forall_mem_cons.2 ⟨subd9_5_162, List.forall_mem_cons.2 ⟨subd9_5_163, List.forall_mem_cons.2 ⟨subd9_5_164, List.forall_mem_cons.2 ⟨subd9_5_165, List.forall_mem_cons.2 ⟨subd9_5_166, List.forall_mem_cons.2 ⟨subd9_5_167, List.forall_mem_cons.2 ⟨subd9_5_168, List.forall_mem_cons.2 ⟨subd9_5_169, List.forall_mem_cons.2 ⟨subd9_5_170, List.forall_mem_cons.2 ⟨subd9_5_171, List.forall_mem_cons.2 ⟨subd9_5_172, List.forall_mem_cons.2 ⟨subd9_5_173, List.forall_mem_cons.2 ⟨subd9_5_174, List.forall_mem_cons.2 ⟨subd9_5_175, List.forall_mem_cons.2 ⟨subd9_5_176, List.forall_mem_cons.2 ⟨subd9_5_177, List.forall_mem_cons.2 ⟨subd9_5_178, List.forall_mem_cons.2 ⟨subd9_5_179, List.forall_mem_cons.2 ⟨subd9_5_180, List.forall_mem_cons.2 ⟨subd9_5_181, List.forall_mem_cons.2 ⟨subd9_5_182, List.forall_mem_cons.2 ⟨subd9_5_183, List.forall_mem_cons.2 ⟨subd9_5_184, List.forall_mem_cons.2 ⟨subd9_5_185, List.forall_mem_cons.2 ⟨subd9_5_186, List.forall_mem_cons.2 ⟨subd9_5_187, List.forall_mem_cons.2 ⟨subd9_5_188, List.forall_mem_cons.2 ⟨subd9_5_189, List.forall_mem_cons.2 ⟨subd9_5_190, List.forall_mem_cons.2 ⟨subd9_5_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_192 : subd9_5 [-1, 1, 2] = true := by decide +kernel
theorem subd9_5_193 : subd9_5 [-1, 1, 3] = true := by decide +kernel
theorem subd9_5_194 : subd9_5 [-1, 1, 4] = true := by decide +kernel
theorem subd9_5_195 : subd9_5 [-1, 1, 5] = true := by decide +kernel
theorem subd9_5_196 : subd9_5 [-1, 1, 6] = true := by decide +kernel
theorem subd9_5_197 : subd9_5 [-1, 1, 7] = true := by decide +kernel
theorem subd9_5_198 : subd9_5 [-1, 1, 8] = true := by decide +kernel
theorem subd9_5_199 : subd9_5 [-1, 1, 9] = true := by decide +kernel
theorem subd9_5_200 : subd9_5 [-1, 1, 10] = true := by decide +kernel
theorem subd9_5_201 : subd9_5 [-1, 2, -10] = true := by decide +kernel
theorem subd9_5_202 : subd9_5 [-1, 2, -9] = true := by decide +kernel
theorem subd9_5_203 : subd9_5 [-1, 2, -8] = true := by decide +kernel
theorem subd9_5_204 : subd9_5 [-1, 2, -7] = true := by decide +kernel
theorem subd9_5_205 : subd9_5 [-1, 2, -6] = true := by decide +kernel
theorem subd9_5_206 : subd9_5 [-1, 2, -5] = true := by decide +kernel
theorem subd9_5_207 : subd9_5 [-1, 2, -4] = true := by decide +kernel
theorem subd9_5_208 : subd9_5 [-1, 2, -3] = true := by decide +kernel
theorem subd9_5_209 : subd9_5 [-1, 2, -2] = true := by decide +kernel
theorem subd9_5_210 : subd9_5 [-1, 2, -1] = true := by decide +kernel
theorem subd9_5_211 : subd9_5 [-1, 2, 0] = true := by decide +kernel
theorem subd9_5_212 : subd9_5 [-1, 2, 1] = true := by decide +kernel
theorem subd9_5_213 : subd9_5 [-1, 2, 2] = true := by decide +kernel
theorem subd9_5_214 : subd9_5 [-1, 2, 3] = true := by decide +kernel
theorem subd9_5_215 : subd9_5 [-1, 2, 4] = true := by decide +kernel
theorem subd9_5_216 : subd9_5 [-1, 2, 5] = true := by decide +kernel
theorem subd9_5_217 : subd9_5 [-1, 2, 6] = true := by decide +kernel
theorem subd9_5_218 : subd9_5 [-1, 2, 7] = true := by decide +kernel
theorem subd9_5_219 : subd9_5 [-1, 2, 8] = true := by decide +kernel
theorem subd9_5_220 : subd9_5 [-1, 3] = true := by decide +kernel
theorem subd9_5_221 : subd9_5 [0, -4] = true := by decide +kernel
theorem subd9_5_222 : subd9_5 [0, -3, -6] = true := by decide +kernel
theorem subd9_5_223 : subd9_5 [0, -3, -5] = true := by decide +kernel
theorem sbd9_5_6 : ∀ q ∈ blkd9_5_6, subd9_5 q = true := by
  unfold blkd9_5_6
  exact List.forall_mem_cons.2 ⟨subd9_5_192, List.forall_mem_cons.2 ⟨subd9_5_193, List.forall_mem_cons.2 ⟨subd9_5_194, List.forall_mem_cons.2 ⟨subd9_5_195, List.forall_mem_cons.2 ⟨subd9_5_196, List.forall_mem_cons.2 ⟨subd9_5_197, List.forall_mem_cons.2 ⟨subd9_5_198, List.forall_mem_cons.2 ⟨subd9_5_199, List.forall_mem_cons.2 ⟨subd9_5_200, List.forall_mem_cons.2 ⟨subd9_5_201, List.forall_mem_cons.2 ⟨subd9_5_202, List.forall_mem_cons.2 ⟨subd9_5_203, List.forall_mem_cons.2 ⟨subd9_5_204, List.forall_mem_cons.2 ⟨subd9_5_205, List.forall_mem_cons.2 ⟨subd9_5_206, List.forall_mem_cons.2 ⟨subd9_5_207, List.forall_mem_cons.2 ⟨subd9_5_208, List.forall_mem_cons.2 ⟨subd9_5_209, List.forall_mem_cons.2 ⟨subd9_5_210, List.forall_mem_cons.2 ⟨subd9_5_211, List.forall_mem_cons.2 ⟨subd9_5_212, List.forall_mem_cons.2 ⟨subd9_5_213, List.forall_mem_cons.2 ⟨subd9_5_214, List.forall_mem_cons.2 ⟨subd9_5_215, List.forall_mem_cons.2 ⟨subd9_5_216, List.forall_mem_cons.2 ⟨subd9_5_217, List.forall_mem_cons.2 ⟨subd9_5_218, List.forall_mem_cons.2 ⟨subd9_5_219, List.forall_mem_cons.2 ⟨subd9_5_220, List.forall_mem_cons.2 ⟨subd9_5_221, List.forall_mem_cons.2 ⟨subd9_5_222, List.forall_mem_cons.2 ⟨subd9_5_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_5_224 : subd9_5 [0, -3, -4] = true := by decide +kernel
theorem subd9_5_225 : subd9_5 [0, -3, -3] = true := by decide +kernel
theorem subd9_5_226 : subd9_5 [0, -3, -2] = true := by decide +kernel
theorem subd9_5_227 : subd9_5 [0, -3, -1] = true := by decide +kernel
theorem subd9_5_228 : subd9_5 [0, -3, 0] = true := by decide +kernel
theorem subd9_5_229 : subd9_5 [0, -3, 1] = true := by decide +kernel
theorem subd9_5_230 : subd9_5 [0, -3, 2] = true := by decide +kernel
theorem subd9_5_231 : subd9_5 [0, -3, 3] = true := by decide +kernel
theorem subd9_5_232 : subd9_5 [0, -3, 4] = true := by decide +kernel
theorem subd9_5_233 : subd9_5 [0, -3, 5] = true := by decide +kernel
theorem subd9_5_234 : subd9_5 [0, -3, 6] = true := by decide +kernel
theorem subd9_5_235 : subd9_5 [0, -3, 7] = true := by decide +kernel
theorem subd9_5_236 : subd9_5 [0, -2, -10] = true := by decide +kernel
theorem subd9_5_237 : subd9_5 [0, -2, -9] = true := by decide +kernel
theorem subd9_5_238 : subd9_5 [0, -2, -8] = true := by decide +kernel
theorem subd9_5_239 : subd9_5 [0, -2, -7] = true := by decide +kernel
theorem subd9_5_240 : subd9_5 [0, -2, -6] = true := by decide +kernel
theorem subd9_5_241 : subd9_5 [0, -2, -5] = true := by decide +kernel
theorem subd9_5_242 : subd9_5 [0, -2, -4] = true := by decide +kernel
theorem subd9_5_243 : subd9_5 [0, -2, -3] = true := by decide +kernel
theorem subd9_5_244 : subd9_5 [0, -2, -2] = true := by decide +kernel
theorem subd9_5_245 : subd9_5 [0, -2, -1] = true := by decide +kernel
theorem subd9_5_246 : subd9_5 [0, -2, 0] = true := by decide +kernel
theorem subd9_5_247 : subd9_5 [0, -2, 1] = true := by decide +kernel
theorem subd9_5_248 : subd9_5 [0, -2, 2] = true := by decide +kernel
theorem subd9_5_249 : subd9_5 [0, -2, 3] = true := by decide +kernel
theorem subd9_5_250 : subd9_5 [0, -2, 4] = true := by decide +kernel
theorem subd9_5_251 : subd9_5 [0, -2, 5] = true := by decide +kernel
theorem subd9_5_252 : subd9_5 [0, -2, 6] = true := by decide +kernel
theorem subd9_5_253 : subd9_5 [0, -2, 7] = true := by decide +kernel
theorem subd9_5_254 : subd9_5 [0, -2, 8] = true := by decide +kernel
theorem subd9_5_255 : subd9_5 [0, -2, 9] = true := by decide +kernel
theorem sbd9_5_7 : ∀ q ∈ blkd9_5_7, subd9_5 q = true := by
  unfold blkd9_5_7
  exact List.forall_mem_cons.2 ⟨subd9_5_224, List.forall_mem_cons.2 ⟨subd9_5_225, List.forall_mem_cons.2 ⟨subd9_5_226, List.forall_mem_cons.2 ⟨subd9_5_227, List.forall_mem_cons.2 ⟨subd9_5_228, List.forall_mem_cons.2 ⟨subd9_5_229, List.forall_mem_cons.2 ⟨subd9_5_230, List.forall_mem_cons.2 ⟨subd9_5_231, List.forall_mem_cons.2 ⟨subd9_5_232, List.forall_mem_cons.2 ⟨subd9_5_233, List.forall_mem_cons.2 ⟨subd9_5_234, List.forall_mem_cons.2 ⟨subd9_5_235, List.forall_mem_cons.2 ⟨subd9_5_236, List.forall_mem_cons.2 ⟨subd9_5_237, List.forall_mem_cons.2 ⟨subd9_5_238, List.forall_mem_cons.2 ⟨subd9_5_239, List.forall_mem_cons.2 ⟨subd9_5_240, List.forall_mem_cons.2 ⟨subd9_5_241, List.forall_mem_cons.2 ⟨subd9_5_242, List.forall_mem_cons.2 ⟨subd9_5_243, List.forall_mem_cons.2 ⟨subd9_5_244, List.forall_mem_cons.2 ⟨subd9_5_245, List.forall_mem_cons.2 ⟨subd9_5_246, List.forall_mem_cons.2 ⟨subd9_5_247, List.forall_mem_cons.2 ⟨subd9_5_248, List.forall_mem_cons.2 ⟨subd9_5_249, List.forall_mem_cons.2 ⟨subd9_5_250, List.forall_mem_cons.2 ⟨subd9_5_251, List.forall_mem_cons.2 ⟨subd9_5_252, List.forall_mem_cons.2 ⟨subd9_5_253, List.forall_mem_cons.2 ⟨subd9_5_254, List.forall_mem_cons.2 ⟨subd9_5_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
