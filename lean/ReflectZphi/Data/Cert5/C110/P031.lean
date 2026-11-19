import ReflectZphi.Data.Cert5.C110.Base

namespace ReflectZphi.Data.Cert5.C110

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [-2] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-1] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [0, -1] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [0, 0] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [0, 1] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [1] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [2] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_4 : ldCheck G d11_4.U d11_4.ms ldd11_4 = true := by decide +kernel
theorem pre_okd11_4 : subPre G cell11 d11_4 = true := by decide +kernel
theorem subd11_4_0 : subd11_4 [-2] = true := by decide +kernel
theorem subd11_4_1 : subd11_4 [-1, -2] = true := by decide +kernel
theorem subd11_4_2 : subd11_4 [-1, -1] = true := by decide +kernel
theorem subd11_4_3 : subd11_4 [-1, 0, -8] = true := by decide +kernel
theorem subd11_4_4 : subd11_4 [-1, 0, -7] = true := by decide +kernel
theorem subd11_4_5 : subd11_4 [-1, 0, -6] = true := by decide +kernel
theorem subd11_4_6 : subd11_4 [-1, 0, -5] = true := by decide +kernel
theorem subd11_4_7 : subd11_4 [-1, 0, -4] = true := by decide +kernel
theorem subd11_4_8 : subd11_4 [-1, 0, -3] = true := by decide +kernel
theorem subd11_4_9 : subd11_4 [-1, 0, -2] = true := by decide +kernel
theorem subd11_4_10 : subd11_4 [-1, 0, -1] = true := by decide +kernel
theorem subd11_4_11 : subd11_4 [-1, 0, 0] = true := by decide +kernel
theorem subd11_4_12 : subd11_4 [-1, 0, 1] = true := by decide +kernel
theorem subd11_4_13 : subd11_4 [-1, 0, 2] = true := by decide +kernel
theorem subd11_4_14 : subd11_4 [-1, 0, 3] = true := by decide +kernel
theorem subd11_4_15 : subd11_4 [-1, 0, 4] = true := by decide +kernel
theorem subd11_4_16 : subd11_4 [-1, 0, 5] = true := by decide +kernel
theorem subd11_4_17 : subd11_4 [-1, 0, 6] = true := by decide +kernel
theorem subd11_4_18 : subd11_4 [-1, 1] = true := by decide +kernel
theorem subd11_4_19 : subd11_4 [-1, 2] = true := by decide +kernel
theorem subd11_4_20 : subd11_4 [0, -3] = true := by decide +kernel
theorem subd11_4_21 : subd11_4 [0, -2] = true := by decide +kernel
theorem subd11_4_22 : subd11_4 [0, -1, -7] = true := by decide +kernel
theorem subd11_4_23 : subd11_4 [0, -1, -6] = true := by decide +kernel
theorem subd11_4_24 : subd11_4 [0, -1, -5] = true := by decide +kernel
theorem subd11_4_25 : subd11_4 [0, -1, -4] = true := by decide +kernel
theorem subd11_4_26 : subd11_4 [0, -1, -3] = true := by decide +kernel
theorem subd11_4_27 : subd11_4 [0, -1, -2] = true := by decide +kernel
theorem subd11_4_28 : subd11_4 [0, -1, -1] = true := by decide +kernel
theorem subd11_4_29 : subd11_4 [0, -1, 0] = true := by decide +kernel
theorem subd11_4_30 : subd11_4 [0, -1, 1] = true := by decide +kernel
theorem subd11_4_31 : subd11_4 [0, -1, 2] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_cons.2 ⟨subd11_4_1, List.forall_mem_cons.2 ⟨subd11_4_2, List.forall_mem_cons.2 ⟨subd11_4_3, List.forall_mem_cons.2 ⟨subd11_4_4, List.forall_mem_cons.2 ⟨subd11_4_5, List.forall_mem_cons.2 ⟨subd11_4_6, List.forall_mem_cons.2 ⟨subd11_4_7, List.forall_mem_cons.2 ⟨subd11_4_8, List.forall_mem_cons.2 ⟨subd11_4_9, List.forall_mem_cons.2 ⟨subd11_4_10, List.forall_mem_cons.2 ⟨subd11_4_11, List.forall_mem_cons.2 ⟨subd11_4_12, List.forall_mem_cons.2 ⟨subd11_4_13, List.forall_mem_cons.2 ⟨subd11_4_14, List.forall_mem_cons.2 ⟨subd11_4_15, List.forall_mem_cons.2 ⟨subd11_4_16, List.forall_mem_cons.2 ⟨subd11_4_17, List.forall_mem_cons.2 ⟨subd11_4_18, List.forall_mem_cons.2 ⟨subd11_4_19, List.forall_mem_cons.2 ⟨subd11_4_20, List.forall_mem_cons.2 ⟨subd11_4_21, List.forall_mem_cons.2 ⟨subd11_4_22, List.forall_mem_cons.2 ⟨subd11_4_23, List.forall_mem_cons.2 ⟨subd11_4_24, List.forall_mem_cons.2 ⟨subd11_4_25, List.forall_mem_cons.2 ⟨subd11_4_26, List.forall_mem_cons.2 ⟨subd11_4_27, List.forall_mem_cons.2 ⟨subd11_4_28, List.forall_mem_cons.2 ⟨subd11_4_29, List.forall_mem_cons.2 ⟨subd11_4_30, List.forall_mem_cons.2 ⟨subd11_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_4_32 : subd11_4 [0, -1, 3] = true := by decide +kernel
theorem subd11_4_33 : subd11_4 [0, -1, 4] = true := by decide +kernel
theorem subd11_4_34 : subd11_4 [0, -1, 5] = true := by decide +kernel
theorem subd11_4_35 : subd11_4 [0, -1, 6] = true := by decide +kernel
theorem subd11_4_36 : subd11_4 [0, 0, -8] = true := by decide +kernel
theorem subd11_4_37 : subd11_4 [0, 0, -7] = true := by decide +kernel
theorem subd11_4_38 : subd11_4 [0, 0, -6] = true := by decide +kernel
theorem subd11_4_39 : subd11_4 [0, 0, -5] = true := by decide +kernel
theorem subd11_4_40 : subd11_4 [0, 0, -4] = true := by decide +kernel
theorem subd11_4_41 : subd11_4 [0, 0, -3] = true := by decide +kernel
theorem subd11_4_42 : subd11_4 [0, 0, -2] = true := by decide +kernel
theorem subd11_4_43 : subd11_4 [0, 0, -1] = true := by decide +kernel
theorem subd11_4_44 : subd11_4 [0, 0, 0] = true := by decide +kernel
theorem subd11_4_45 : subd11_4 [0, 0, 1] = true := by decide +kernel
theorem subd11_4_46 : subd11_4 [0, 0, 2] = true := by decide +kernel
theorem subd11_4_47 : subd11_4 [0, 0, 3] = true := by decide +kernel
theorem subd11_4_48 : subd11_4 [0, 0, 4] = true := by decide +kernel
theorem subd11_4_49 : subd11_4 [0, 0, 5] = true := by decide +kernel
theorem subd11_4_50 : subd11_4 [0, 0, 6] = true := by decide +kernel
theorem subd11_4_51 : subd11_4 [0, 0, 7] = true := by decide +kernel
theorem subd11_4_52 : subd11_4 [0, 1, -7] = true := by decide +kernel
theorem subd11_4_53 : subd11_4 [0, 1, -6] = true := by decide +kernel
theorem subd11_4_54 : subd11_4 [0, 1, -5] = true := by decide +kernel
theorem subd11_4_55 : subd11_4 [0, 1, -4] = true := by decide +kernel
theorem subd11_4_56 : subd11_4 [0, 1, -3] = true := by decide +kernel
theorem subd11_4_57 : subd11_4 [0, 1, -2] = true := by decide +kernel
theorem subd11_4_58 : subd11_4 [0, 1, -1] = true := by decide +kernel
theorem subd11_4_59 : subd11_4 [0, 1, 0] = true := by decide +kernel
theorem subd11_4_60 : subd11_4 [0, 1, 1] = true := by decide +kernel
theorem subd11_4_61 : subd11_4 [0, 1, 2] = true := by decide +kernel
theorem subd11_4_62 : subd11_4 [0, 1, 3] = true := by decide +kernel
theorem subd11_4_63 : subd11_4 [0, 1, 4] = true := by decide +kernel
theorem sbd11_4_1 : ∀ q ∈ blkd11_4_1, subd11_4 q = true := by
  unfold blkd11_4_1
  exact List.forall_mem_cons.2 ⟨subd11_4_32, List.forall_mem_cons.2 ⟨subd11_4_33, List.forall_mem_cons.2 ⟨subd11_4_34, List.forall_mem_cons.2 ⟨subd11_4_35, List.forall_mem_cons.2 ⟨subd11_4_36, List.forall_mem_cons.2 ⟨subd11_4_37, List.forall_mem_cons.2 ⟨subd11_4_38, List.forall_mem_cons.2 ⟨subd11_4_39, List.forall_mem_cons.2 ⟨subd11_4_40, List.forall_mem_cons.2 ⟨subd11_4_41, List.forall_mem_cons.2 ⟨subd11_4_42, List.forall_mem_cons.2 ⟨subd11_4_43, List.forall_mem_cons.2 ⟨subd11_4_44, List.forall_mem_cons.2 ⟨subd11_4_45, List.forall_mem_cons.2 ⟨subd11_4_46, List.forall_mem_cons.2 ⟨subd11_4_47, List.forall_mem_cons.2 ⟨subd11_4_48, List.forall_mem_cons.2 ⟨subd11_4_49, List.forall_mem_cons.2 ⟨subd11_4_50, List.forall_mem_cons.2 ⟨subd11_4_51, List.forall_mem_cons.2 ⟨subd11_4_52, List.forall_mem_cons.2 ⟨subd11_4_53, List.forall_mem_cons.2 ⟨subd11_4_54, List.forall_mem_cons.2 ⟨subd11_4_55, List.forall_mem_cons.2 ⟨subd11_4_56, List.forall_mem_cons.2 ⟨subd11_4_57, List.forall_mem_cons.2 ⟨subd11_4_58, List.forall_mem_cons.2 ⟨subd11_4_59, List.forall_mem_cons.2 ⟨subd11_4_60, List.forall_mem_cons.2 ⟨subd11_4_61, List.forall_mem_cons.2 ⟨subd11_4_62, List.forall_mem_cons.2 ⟨subd11_4_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_4_64 : subd11_4 [0, 1, 5] = true := by decide +kernel
theorem subd11_4_65 : subd11_4 [0, 1, 6] = true := by decide +kernel
theorem subd11_4_66 : subd11_4 [0, 2] = true := by decide +kernel
theorem subd11_4_67 : subd11_4 [1, -3] = true := by decide +kernel
theorem subd11_4_68 : subd11_4 [1, -2] = true := by decide +kernel
theorem subd11_4_69 : subd11_4 [1, -1] = true := by decide +kernel
theorem subd11_4_70 : subd11_4 [1, 0, -7] = true := by decide +kernel
theorem subd11_4_71 : subd11_4 [1, 0, -6] = true := by decide +kernel
theorem subd11_4_72 : subd11_4 [1, 0, -5] = true := by decide +kernel
theorem subd11_4_73 : subd11_4 [1, 0, -4] = true := by decide +kernel
theorem subd11_4_74 : subd11_4 [1, 0, -3] = true := by decide +kernel
theorem subd11_4_75 : subd11_4 [1, 0, -2] = true := by decide +kernel
theorem subd11_4_76 : subd11_4 [1, 0, -1] = true := by decide +kernel
theorem subd11_4_77 : subd11_4 [1, 0, 0] = true := by decide +kernel
theorem subd11_4_78 : subd11_4 [1, 0, 1] = true := by decide +kernel
theorem subd11_4_79 : subd11_4 [1, 0, 2] = true := by decide +kernel
theorem subd11_4_80 : subd11_4 [1, 0, 3] = true := by decide +kernel
theorem subd11_4_81 : subd11_4 [1, 0, 4] = true := by decide +kernel
theorem subd11_4_82 : subd11_4 [1, 0, 5] = true := by decide +kernel
theorem subd11_4_83 : subd11_4 [1, 0, 6] = true := by decide +kernel
theorem subd11_4_84 : subd11_4 [1, 0, 7] = true := by decide +kernel
theorem subd11_4_85 : subd11_4 [1, 1] = true := by decide +kernel
theorem subd11_4_86 : subd11_4 [2] = true := by decide +kernel
theorem sbd11_4_2 : ∀ q ∈ blkd11_4_2, subd11_4 q = true := by
  unfold blkd11_4_2
  exact List.forall_mem_cons.2 ⟨subd11_4_64, List.forall_mem_cons.2 ⟨subd11_4_65, List.forall_mem_cons.2 ⟨subd11_4_66, List.forall_mem_cons.2 ⟨subd11_4_67, List.forall_mem_cons.2 ⟨subd11_4_68, List.forall_mem_cons.2 ⟨subd11_4_69, List.forall_mem_cons.2 ⟨subd11_4_70, List.forall_mem_cons.2 ⟨subd11_4_71, List.forall_mem_cons.2 ⟨subd11_4_72, List.forall_mem_cons.2 ⟨subd11_4_73, List.forall_mem_cons.2 ⟨subd11_4_74, List.forall_mem_cons.2 ⟨subd11_4_75, List.forall_mem_cons.2 ⟨subd11_4_76, List.forall_mem_cons.2 ⟨subd11_4_77, List.forall_mem_cons.2 ⟨subd11_4_78, List.forall_mem_cons.2 ⟨subd11_4_79, List.forall_mem_cons.2 ⟨subd11_4_80, List.forall_mem_cons.2 ⟨subd11_4_81, List.forall_mem_cons.2 ⟨subd11_4_82, List.forall_mem_cons.2 ⟨subd11_4_83, List.forall_mem_cons.2 ⟨subd11_4_84, List.forall_mem_cons.2 ⟨subd11_4_85, List.forall_mem_cons.2 ⟨subd11_4_86, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-2] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [-1] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [0] = true := by decide +kernel
theorem subd12_0_3 : subd12_0 [1] = true := by decide +kernel
theorem subd12_0_4 : subd12_0 [2] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_cons.2 ⟨subd12_0_3, List.forall_mem_cons.2 ⟨subd12_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-1] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [0] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [1] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C110
