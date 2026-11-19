import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_2_32 : subd11_2 [0, -5] = true := by decide +kernel
theorem subd11_2_33 : subd11_2 [0, -4] = true := by decide +kernel
theorem subd11_2_34 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_35 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_36 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_37 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_38 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_39 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_40 : subd11_2 [0, 3] = true := by decide +kernel
theorem subd11_2_41 : subd11_2 [0, 4] = true := by decide +kernel
theorem subd11_2_42 : subd11_2 [0, 5] = true := by decide +kernel
theorem subd11_2_43 : subd11_2 [1, -6] = true := by decide +kernel
theorem subd11_2_44 : subd11_2 [1, -5] = true := by decide +kernel
theorem subd11_2_45 : subd11_2 [1, -4] = true := by decide +kernel
theorem subd11_2_46 : subd11_2 [1, -3] = true := by decide +kernel
theorem subd11_2_47 : subd11_2 [1, -2] = true := by decide +kernel
theorem subd11_2_48 : subd11_2 [1, -1] = true := by decide +kernel
theorem subd11_2_49 : subd11_2 [1, 0] = true := by decide +kernel
theorem subd11_2_50 : subd11_2 [1, 1] = true := by decide +kernel
theorem subd11_2_51 : subd11_2 [1, 2] = true := by decide +kernel
theorem subd11_2_52 : subd11_2 [1, 3] = true := by decide +kernel
theorem subd11_2_53 : subd11_2 [1, 4] = true := by decide +kernel
theorem subd11_2_54 : subd11_2 [2, -5] = true := by decide +kernel
theorem subd11_2_55 : subd11_2 [2, -4] = true := by decide +kernel
theorem subd11_2_56 : subd11_2 [2, -3] = true := by decide +kernel
theorem subd11_2_57 : subd11_2 [2, -2] = true := by decide +kernel
theorem subd11_2_58 : subd11_2 [2, -1] = true := by decide +kernel
theorem subd11_2_59 : subd11_2 [2, 0] = true := by decide +kernel
theorem subd11_2_60 : subd11_2 [2, 1] = true := by decide +kernel
theorem subd11_2_61 : subd11_2 [2, 2] = true := by decide +kernel
theorem subd11_2_62 : subd11_2 [2, 3] = true := by decide +kernel
theorem subd11_2_63 : subd11_2 [2, 4] = true := by decide +kernel
theorem sbd11_2_1 : ∀ q ∈ blkd11_2_1, subd11_2 q = true := by
  unfold blkd11_2_1
  exact List.forall_mem_cons.2 ⟨subd11_2_32, List.forall_mem_cons.2 ⟨subd11_2_33, List.forall_mem_cons.2 ⟨subd11_2_34, List.forall_mem_cons.2 ⟨subd11_2_35, List.forall_mem_cons.2 ⟨subd11_2_36, List.forall_mem_cons.2 ⟨subd11_2_37, List.forall_mem_cons.2 ⟨subd11_2_38, List.forall_mem_cons.2 ⟨subd11_2_39, List.forall_mem_cons.2 ⟨subd11_2_40, List.forall_mem_cons.2 ⟨subd11_2_41, List.forall_mem_cons.2 ⟨subd11_2_42, List.forall_mem_cons.2 ⟨subd11_2_43, List.forall_mem_cons.2 ⟨subd11_2_44, List.forall_mem_cons.2 ⟨subd11_2_45, List.forall_mem_cons.2 ⟨subd11_2_46, List.forall_mem_cons.2 ⟨subd11_2_47, List.forall_mem_cons.2 ⟨subd11_2_48, List.forall_mem_cons.2 ⟨subd11_2_49, List.forall_mem_cons.2 ⟨subd11_2_50, List.forall_mem_cons.2 ⟨subd11_2_51, List.forall_mem_cons.2 ⟨subd11_2_52, List.forall_mem_cons.2 ⟨subd11_2_53, List.forall_mem_cons.2 ⟨subd11_2_54, List.forall_mem_cons.2 ⟨subd11_2_55, List.forall_mem_cons.2 ⟨subd11_2_56, List.forall_mem_cons.2 ⟨subd11_2_57, List.forall_mem_cons.2 ⟨subd11_2_58, List.forall_mem_cons.2 ⟨subd11_2_59, List.forall_mem_cons.2 ⟨subd11_2_60, List.forall_mem_cons.2 ⟨subd11_2_61, List.forall_mem_cons.2 ⟨subd11_2_62, List.forall_mem_cons.2 ⟨subd11_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_64 : subd11_2 [3, -5] = true := by decide +kernel
theorem subd11_2_65 : subd11_2 [3, -4] = true := by decide +kernel
theorem subd11_2_66 : subd11_2 [3, -3] = true := by decide +kernel
theorem subd11_2_67 : subd11_2 [3, -2] = true := by decide +kernel
theorem subd11_2_68 : subd11_2 [3, -1] = true := by decide +kernel
theorem subd11_2_69 : subd11_2 [3, 0] = true := by decide +kernel
theorem subd11_2_70 : subd11_2 [3, 1] = true := by decide +kernel
theorem subd11_2_71 : subd11_2 [3, 2] = true := by decide +kernel
theorem subd11_2_72 : subd11_2 [3, 3] = true := by decide +kernel
theorem subd11_2_73 : subd11_2 [4] = true := by decide +kernel
theorem sbd11_2_2 : ∀ q ∈ blkd11_2_2, subd11_2 q = true := by
  unfold blkd11_2_2
  exact List.forall_mem_cons.2 ⟨subd11_2_64, List.forall_mem_cons.2 ⟨subd11_2_65, List.forall_mem_cons.2 ⟨subd11_2_66, List.forall_mem_cons.2 ⟨subd11_2_67, List.forall_mem_cons.2 ⟨subd11_2_68, List.forall_mem_cons.2 ⟨subd11_2_69, List.forall_mem_cons.2 ⟨subd11_2_70, List.forall_mem_cons.2 ⟨subd11_2_71, List.forall_mem_cons.2 ⟨subd11_2_72, List.forall_mem_cons.2 ⟨subd11_2_73, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [-4] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-3, -4] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-3, -3] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-3, -2] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-3, -1] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-3, 0] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [-3, 1] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [-3, 2] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [-3, 3] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [-3, 4] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [-2, -5] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [-2, -4] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [-2, -3] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [-2, -2] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [-2, -1] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [-2, 0] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [-2, 1] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [-2, 2] = true := by decide +kernel
theorem subd11_3_18 : subd11_3 [-2, 3] = true := by decide +kernel
theorem subd11_3_19 : subd11_3 [-2, 4] = true := by decide +kernel
theorem subd11_3_20 : subd11_3 [-2, 5] = true := by decide +kernel
theorem subd11_3_21 : subd11_3 [-1, -6] = true := by decide +kernel
theorem subd11_3_22 : subd11_3 [-1, -5] = true := by decide +kernel
theorem subd11_3_23 : subd11_3 [-1, -4] = true := by decide +kernel
theorem subd11_3_24 : subd11_3 [-1, -3] = true := by decide +kernel
theorem subd11_3_25 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_26 : subd11_3 [-1, -1] = true := by decide +kernel
theorem subd11_3_27 : subd11_3 [-1, 0] = true := by decide +kernel
theorem subd11_3_28 : subd11_3 [-1, 1] = true := by decide +kernel
theorem subd11_3_29 : subd11_3 [-1, 2] = true := by decide +kernel
theorem subd11_3_30 : subd11_3 [-1, 3] = true := by decide +kernel
theorem subd11_3_31 : subd11_3 [-1, 4] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_cons.2 ⟨subd11_3_18, List.forall_mem_cons.2 ⟨subd11_3_19, List.forall_mem_cons.2 ⟨subd11_3_20, List.forall_mem_cons.2 ⟨subd11_3_21, List.forall_mem_cons.2 ⟨subd11_3_22, List.forall_mem_cons.2 ⟨subd11_3_23, List.forall_mem_cons.2 ⟨subd11_3_24, List.forall_mem_cons.2 ⟨subd11_3_25, List.forall_mem_cons.2 ⟨subd11_3_26, List.forall_mem_cons.2 ⟨subd11_3_27, List.forall_mem_cons.2 ⟨subd11_3_28, List.forall_mem_cons.2 ⟨subd11_3_29, List.forall_mem_cons.2 ⟨subd11_3_30, List.forall_mem_cons.2 ⟨subd11_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_32 : subd11_3 [-1, 5] = true := by decide +kernel
theorem subd11_3_33 : subd11_3 [0, -6] = true := by decide +kernel
theorem subd11_3_34 : subd11_3 [0, -5] = true := by decide +kernel
theorem subd11_3_35 : subd11_3 [0, -4] = true := by decide +kernel
theorem subd11_3_36 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_37 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_38 : subd11_3 [0, -1] = true := by decide +kernel
theorem subd11_3_39 : subd11_3 [0, 0] = true := by decide +kernel
theorem subd11_3_40 : subd11_3 [0, 1] = true := by decide +kernel
theorem subd11_3_41 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_42 : subd11_3 [0, 3] = true := by decide +kernel
theorem subd11_3_43 : subd11_3 [0, 4] = true := by decide +kernel
theorem subd11_3_44 : subd11_3 [0, 5] = true := by decide +kernel
theorem subd11_3_45 : subd11_3 [1, -6] = true := by decide +kernel
theorem subd11_3_46 : subd11_3 [1, -5] = true := by decide +kernel
theorem subd11_3_47 : subd11_3 [1, -4] = true := by decide +kernel
theorem subd11_3_48 : subd11_3 [1, -3] = true := by decide +kernel
theorem subd11_3_49 : subd11_3 [1, -2] = true := by decide +kernel
theorem subd11_3_50 : subd11_3 [1, -1] = true := by decide +kernel
theorem subd11_3_51 : subd11_3 [1, 0] = true := by decide +kernel
theorem subd11_3_52 : subd11_3 [1, 1] = true := by decide +kernel
theorem subd11_3_53 : subd11_3 [1, 2] = true := by decide +kernel
theorem subd11_3_54 : subd11_3 [1, 3] = true := by decide +kernel
theorem subd11_3_55 : subd11_3 [1, 4] = true := by decide +kernel
theorem subd11_3_56 : subd11_3 [1, 5] = true := by decide +kernel
theorem subd11_3_57 : subd11_3 [2, -6] = true := by decide +kernel
theorem subd11_3_58 : subd11_3 [2, -5] = true := by decide +kernel
theorem subd11_3_59 : subd11_3 [2, -4] = true := by decide +kernel
theorem subd11_3_60 : subd11_3 [2, -3] = true := by decide +kernel
theorem subd11_3_61 : subd11_3 [2, -2] = true := by decide +kernel
theorem subd11_3_62 : subd11_3 [2, -1] = true := by decide +kernel
theorem subd11_3_63 : subd11_3 [2, 0] = true := by decide +kernel
theorem sbd11_3_1 : ∀ q ∈ blkd11_3_1, subd11_3 q = true := by
  unfold blkd11_3_1
  exact List.forall_mem_cons.2 ⟨subd11_3_32, List.forall_mem_cons.2 ⟨subd11_3_33, List.forall_mem_cons.2 ⟨subd11_3_34, List.forall_mem_cons.2 ⟨subd11_3_35, List.forall_mem_cons.2 ⟨subd11_3_36, List.forall_mem_cons.2 ⟨subd11_3_37, List.forall_mem_cons.2 ⟨subd11_3_38, List.forall_mem_cons.2 ⟨subd11_3_39, List.forall_mem_cons.2 ⟨subd11_3_40, List.forall_mem_cons.2 ⟨subd11_3_41, List.forall_mem_cons.2 ⟨subd11_3_42, List.forall_mem_cons.2 ⟨subd11_3_43, List.forall_mem_cons.2 ⟨subd11_3_44, List.forall_mem_cons.2 ⟨subd11_3_45, List.forall_mem_cons.2 ⟨subd11_3_46, List.forall_mem_cons.2 ⟨subd11_3_47, List.forall_mem_cons.2 ⟨subd11_3_48, List.forall_mem_cons.2 ⟨subd11_3_49, List.forall_mem_cons.2 ⟨subd11_3_50, List.forall_mem_cons.2 ⟨subd11_3_51, List.forall_mem_cons.2 ⟨subd11_3_52, List.forall_mem_cons.2 ⟨subd11_3_53, List.forall_mem_cons.2 ⟨subd11_3_54, List.forall_mem_cons.2 ⟨subd11_3_55, List.forall_mem_cons.2 ⟨subd11_3_56, List.forall_mem_cons.2 ⟨subd11_3_57, List.forall_mem_cons.2 ⟨subd11_3_58, List.forall_mem_cons.2 ⟨subd11_3_59, List.forall_mem_cons.2 ⟨subd11_3_60, List.forall_mem_cons.2 ⟨subd11_3_61, List.forall_mem_cons.2 ⟨subd11_3_62, List.forall_mem_cons.2 ⟨subd11_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_64 : subd11_3 [2, 1] = true := by decide +kernel
theorem subd11_3_65 : subd11_3 [2, 2] = true := by decide +kernel
theorem subd11_3_66 : subd11_3 [2, 3] = true := by decide +kernel
theorem subd11_3_67 : subd11_3 [2, 4] = true := by decide +kernel
theorem subd11_3_68 : subd11_3 [3, -5] = true := by decide +kernel
theorem subd11_3_69 : subd11_3 [3, -4] = true := by decide +kernel
theorem subd11_3_70 : subd11_3 [3, -3] = true := by decide +kernel
theorem subd11_3_71 : subd11_3 [3, -2] = true := by decide +kernel
theorem subd11_3_72 : subd11_3 [3, -1] = true := by decide +kernel
theorem subd11_3_73 : subd11_3 [3, 0] = true := by decide +kernel
theorem subd11_3_74 : subd11_3 [3, 1] = true := by decide +kernel
theorem subd11_3_75 : subd11_3 [3, 2] = true := by decide +kernel
theorem subd11_3_76 : subd11_3 [3, 3] = true := by decide +kernel
theorem subd11_3_77 : subd11_3 [4] = true := by decide +kernel
theorem sbd11_3_2 : ∀ q ∈ blkd11_3_2, subd11_3 q = true := by
  unfold blkd11_3_2
  exact List.forall_mem_cons.2 ⟨subd11_3_64, List.forall_mem_cons.2 ⟨subd11_3_65, List.forall_mem_cons.2 ⟨subd11_3_66, List.forall_mem_cons.2 ⟨subd11_3_67, List.forall_mem_cons.2 ⟨subd11_3_68, List.forall_mem_cons.2 ⟨subd11_3_69, List.forall_mem_cons.2 ⟨subd11_3_70, List.forall_mem_cons.2 ⟨subd11_3_71, List.forall_mem_cons.2 ⟨subd11_3_72, List.forall_mem_cons.2 ⟨subd11_3_73, List.forall_mem_cons.2 ⟨subd11_3_74, List.forall_mem_cons.2 ⟨subd11_3_75, List.forall_mem_cons.2 ⟨subd11_3_76, List.forall_mem_cons.2 ⟨subd11_3_77, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C129
