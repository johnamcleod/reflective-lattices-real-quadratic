import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd12_0_32 : subd12_0 [0, -1] = true := by decide +kernel
theorem subd12_0_33 : subd12_0 [0, 0] = true := by decide +kernel
theorem subd12_0_34 : subd12_0 [0, 1] = true := by decide +kernel
theorem subd12_0_35 : subd12_0 [0, 2] = true := by decide +kernel
theorem subd12_0_36 : subd12_0 [0, 3] = true := by decide +kernel
theorem subd12_0_37 : subd12_0 [0, 4] = true := by decide +kernel
theorem subd12_0_38 : subd12_0 [1, -5] = true := by decide +kernel
theorem subd12_0_39 : subd12_0 [1, -4] = true := by decide +kernel
theorem subd12_0_40 : subd12_0 [1, -3] = true := by decide +kernel
theorem subd12_0_41 : subd12_0 [1, -2] = true := by decide +kernel
theorem subd12_0_42 : subd12_0 [1, -1] = true := by decide +kernel
theorem subd12_0_43 : subd12_0 [1, 0] = true := by decide +kernel
theorem subd12_0_44 : subd12_0 [1, 1] = true := by decide +kernel
theorem subd12_0_45 : subd12_0 [1, 2] = true := by decide +kernel
theorem subd12_0_46 : subd12_0 [1, 3] = true := by decide +kernel
theorem subd12_0_47 : subd12_0 [1, 4] = true := by decide +kernel
theorem subd12_0_48 : subd12_0 [2, -5] = true := by decide +kernel
theorem subd12_0_49 : subd12_0 [2, -4] = true := by decide +kernel
theorem subd12_0_50 : subd12_0 [2, -3] = true := by decide +kernel
theorem subd12_0_51 : subd12_0 [2, -2] = true := by decide +kernel
theorem subd12_0_52 : subd12_0 [2, -1] = true := by decide +kernel
theorem subd12_0_53 : subd12_0 [2, 0] = true := by decide +kernel
theorem subd12_0_54 : subd12_0 [2, 1] = true := by decide +kernel
theorem subd12_0_55 : subd12_0 [2, 2] = true := by decide +kernel
theorem subd12_0_56 : subd12_0 [2, 3] = true := by decide +kernel
theorem subd12_0_57 : subd12_0 [3, -5] = true := by decide +kernel
theorem subd12_0_58 : subd12_0 [3, -4] = true := by decide +kernel
theorem subd12_0_59 : subd12_0 [3, -3] = true := by decide +kernel
theorem subd12_0_60 : subd12_0 [3, -2] = true := by decide +kernel
theorem subd12_0_61 : subd12_0 [3, -1] = true := by decide +kernel
theorem subd12_0_62 : subd12_0 [3, 0] = true := by decide +kernel
theorem subd12_0_63 : subd12_0 [3, 1] = true := by decide +kernel
theorem sbd12_0_1 : ∀ q ∈ blkd12_0_1, subd12_0 q = true := by
  unfold blkd12_0_1
  exact List.forall_mem_cons.2 ⟨subd12_0_32, List.forall_mem_cons.2 ⟨subd12_0_33, List.forall_mem_cons.2 ⟨subd12_0_34, List.forall_mem_cons.2 ⟨subd12_0_35, List.forall_mem_cons.2 ⟨subd12_0_36, List.forall_mem_cons.2 ⟨subd12_0_37, List.forall_mem_cons.2 ⟨subd12_0_38, List.forall_mem_cons.2 ⟨subd12_0_39, List.forall_mem_cons.2 ⟨subd12_0_40, List.forall_mem_cons.2 ⟨subd12_0_41, List.forall_mem_cons.2 ⟨subd12_0_42, List.forall_mem_cons.2 ⟨subd12_0_43, List.forall_mem_cons.2 ⟨subd12_0_44, List.forall_mem_cons.2 ⟨subd12_0_45, List.forall_mem_cons.2 ⟨subd12_0_46, List.forall_mem_cons.2 ⟨subd12_0_47, List.forall_mem_cons.2 ⟨subd12_0_48, List.forall_mem_cons.2 ⟨subd12_0_49, List.forall_mem_cons.2 ⟨subd12_0_50, List.forall_mem_cons.2 ⟨subd12_0_51, List.forall_mem_cons.2 ⟨subd12_0_52, List.forall_mem_cons.2 ⟨subd12_0_53, List.forall_mem_cons.2 ⟨subd12_0_54, List.forall_mem_cons.2 ⟨subd12_0_55, List.forall_mem_cons.2 ⟨subd12_0_56, List.forall_mem_cons.2 ⟨subd12_0_57, List.forall_mem_cons.2 ⟨subd12_0_58, List.forall_mem_cons.2 ⟨subd12_0_59, List.forall_mem_cons.2 ⟨subd12_0_60, List.forall_mem_cons.2 ⟨subd12_0_61, List.forall_mem_cons.2 ⟨subd12_0_62, List.forall_mem_cons.2 ⟨subd12_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_0_64 : subd12_0 [3, 2] = true := by decide +kernel
theorem subd12_0_65 : subd12_0 [4] = true := by decide +kernel
theorem sbd12_0_2 : ∀ q ∈ blkd12_0_2, subd12_0 q = true := by
  unfold blkd12_0_2
  exact List.forall_mem_cons.2 ⟨subd12_0_64, List.forall_mem_cons.2 ⟨subd12_0_65, List.forall_mem_nil _⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-8] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-7, -3] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [-7, -2] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [-7, -1] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [-7, 0] = true := by decide +kernel
theorem subd12_1_5 : subd12_1 [-7, 1] = true := by decide +kernel
theorem subd12_1_6 : subd12_1 [-7, 2] = true := by decide +kernel
theorem subd12_1_7 : subd12_1 [-7, 3] = true := by decide +kernel
theorem subd12_1_8 : subd12_1 [-7, 4] = true := by decide +kernel
theorem subd12_1_9 : subd12_1 [-7, 5] = true := by decide +kernel
theorem subd12_1_10 : subd12_1 [-7, 6] = true := by decide +kernel
theorem subd12_1_11 : subd12_1 [-7, 7] = true := by decide +kernel
theorem subd12_1_12 : subd12_1 [-6, -4] = true := by decide +kernel
theorem subd12_1_13 : subd12_1 [-6, -3] = true := by decide +kernel
theorem subd12_1_14 : subd12_1 [-6, -2] = true := by decide +kernel
theorem subd12_1_15 : subd12_1 [-6, -1] = true := by decide +kernel
theorem subd12_1_16 : subd12_1 [-6, 0] = true := by decide +kernel
theorem subd12_1_17 : subd12_1 [-6, 1] = true := by decide +kernel
theorem subd12_1_18 : subd12_1 [-6, 2] = true := by decide +kernel
theorem subd12_1_19 : subd12_1 [-6, 3] = true := by decide +kernel
theorem subd12_1_20 : subd12_1 [-6, 4] = true := by decide +kernel
theorem subd12_1_21 : subd12_1 [-6, 5] = true := by decide +kernel
theorem subd12_1_22 : subd12_1 [-6, 6] = true := by decide +kernel
theorem subd12_1_23 : subd12_1 [-6, 7] = true := by decide +kernel
theorem subd12_1_24 : subd12_1 [-6, 8] = true := by decide +kernel
theorem subd12_1_25 : subd12_1 [-5, -6] = true := by decide +kernel
theorem subd12_1_26 : subd12_1 [-5, -5] = true := by decide +kernel
theorem subd12_1_27 : subd12_1 [-5, -4] = true := by decide +kernel
theorem subd12_1_28 : subd12_1 [-5, -3] = true := by decide +kernel
theorem subd12_1_29 : subd12_1 [-5, -2] = true := by decide +kernel
theorem subd12_1_30 : subd12_1 [-5, -1] = true := by decide +kernel
theorem subd12_1_31 : subd12_1 [-5, 0] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_cons.2 ⟨subd12_1_5, List.forall_mem_cons.2 ⟨subd12_1_6, List.forall_mem_cons.2 ⟨subd12_1_7, List.forall_mem_cons.2 ⟨subd12_1_8, List.forall_mem_cons.2 ⟨subd12_1_9, List.forall_mem_cons.2 ⟨subd12_1_10, List.forall_mem_cons.2 ⟨subd12_1_11, List.forall_mem_cons.2 ⟨subd12_1_12, List.forall_mem_cons.2 ⟨subd12_1_13, List.forall_mem_cons.2 ⟨subd12_1_14, List.forall_mem_cons.2 ⟨subd12_1_15, List.forall_mem_cons.2 ⟨subd12_1_16, List.forall_mem_cons.2 ⟨subd12_1_17, List.forall_mem_cons.2 ⟨subd12_1_18, List.forall_mem_cons.2 ⟨subd12_1_19, List.forall_mem_cons.2 ⟨subd12_1_20, List.forall_mem_cons.2 ⟨subd12_1_21, List.forall_mem_cons.2 ⟨subd12_1_22, List.forall_mem_cons.2 ⟨subd12_1_23, List.forall_mem_cons.2 ⟨subd12_1_24, List.forall_mem_cons.2 ⟨subd12_1_25, List.forall_mem_cons.2 ⟨subd12_1_26, List.forall_mem_cons.2 ⟨subd12_1_27, List.forall_mem_cons.2 ⟨subd12_1_28, List.forall_mem_cons.2 ⟨subd12_1_29, List.forall_mem_cons.2 ⟨subd12_1_30, List.forall_mem_cons.2 ⟨subd12_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd12_1_32 : subd12_1 [-5, 1] = true := by decide +kernel
theorem subd12_1_33 : subd12_1 [-5, 2] = true := by decide +kernel
theorem subd12_1_34 : subd12_1 [-5, 3] = true := by decide +kernel
theorem subd12_1_35 : subd12_1 [-5, 4] = true := by decide +kernel
theorem subd12_1_36 : subd12_1 [-5, 5] = true := by decide +kernel
theorem subd12_1_37 : subd12_1 [-5, 6] = true := by decide +kernel
theorem subd12_1_38 : subd12_1 [-5, 7] = true := by decide +kernel
theorem subd12_1_39 : subd12_1 [-5, 8] = true := by decide +kernel
theorem subd12_1_40 : subd12_1 [-4, -7] = true := by decide +kernel
theorem subd12_1_41 : subd12_1 [-4, -6] = true := by decide +kernel
theorem subd12_1_42 : subd12_1 [-4, -5] = true := by decide +kernel
theorem subd12_1_43 : subd12_1 [-4, -4] = true := by decide +kernel
theorem subd12_1_44 : subd12_1 [-4, -3] = true := by decide +kernel
theorem subd12_1_45 : subd12_1 [-4, -2] = true := by decide +kernel
theorem subd12_1_46 : subd12_1 [-4, -1] = true := by decide +kernel
theorem subd12_1_47 : subd12_1 [-4, 0] = true := by decide +kernel
theorem subd12_1_48 : subd12_1 [-4, 1] = true := by decide +kernel
theorem subd12_1_49 : subd12_1 [-4, 2] = true := by decide +kernel
theorem subd12_1_50 : subd12_1 [-4, 3] = true := by decide +kernel
theorem subd12_1_51 : subd12_1 [-4, 4] = true := by decide +kernel
theorem subd12_1_52 : subd12_1 [-4, 5] = true := by decide +kernel
theorem subd12_1_53 : subd12_1 [-4, 6] = true := by decide +kernel
theorem subd12_1_54 : subd12_1 [-4, 7] = true := by decide +kernel
theorem subd12_1_55 : subd12_1 [-4, 8] = true := by decide +kernel
theorem subd12_1_56 : subd12_1 [-3, -7] = true := by decide +kernel
theorem subd12_1_57 : subd12_1 [-3, -6] = true := by decide +kernel
theorem subd12_1_58 : subd12_1 [-3, -5] = true := by decide +kernel
theorem subd12_1_59 : subd12_1 [-3, -4] = true := by decide +kernel
theorem subd12_1_60 : subd12_1 [-3, -3] = true := by decide +kernel
theorem subd12_1_61 : subd12_1 [-3, -2] = true := by decide +kernel
theorem subd12_1_62 : subd12_1 [-3, -1] = true := by decide +kernel
theorem subd12_1_63 : subd12_1 [-3, 0] = true := by decide +kernel
theorem sbd12_1_1 : ∀ q ∈ blkd12_1_1, subd12_1 q = true := by
  unfold blkd12_1_1
  exact List.forall_mem_cons.2 ⟨subd12_1_32, List.forall_mem_cons.2 ⟨subd12_1_33, List.forall_mem_cons.2 ⟨subd12_1_34, List.forall_mem_cons.2 ⟨subd12_1_35, List.forall_mem_cons.2 ⟨subd12_1_36, List.forall_mem_cons.2 ⟨subd12_1_37, List.forall_mem_cons.2 ⟨subd12_1_38, List.forall_mem_cons.2 ⟨subd12_1_39, List.forall_mem_cons.2 ⟨subd12_1_40, List.forall_mem_cons.2 ⟨subd12_1_41, List.forall_mem_cons.2 ⟨subd12_1_42, List.forall_mem_cons.2 ⟨subd12_1_43, List.forall_mem_cons.2 ⟨subd12_1_44, List.forall_mem_cons.2 ⟨subd12_1_45, List.forall_mem_cons.2 ⟨subd12_1_46, List.forall_mem_cons.2 ⟨subd12_1_47, List.forall_mem_cons.2 ⟨subd12_1_48, List.forall_mem_cons.2 ⟨subd12_1_49, List.forall_mem_cons.2 ⟨subd12_1_50, List.forall_mem_cons.2 ⟨subd12_1_51, List.forall_mem_cons.2 ⟨subd12_1_52, List.forall_mem_cons.2 ⟨subd12_1_53, List.forall_mem_cons.2 ⟨subd12_1_54, List.forall_mem_cons.2 ⟨subd12_1_55, List.forall_mem_cons.2 ⟨subd12_1_56, List.forall_mem_cons.2 ⟨subd12_1_57, List.forall_mem_cons.2 ⟨subd12_1_58, List.forall_mem_cons.2 ⟨subd12_1_59, List.forall_mem_cons.2 ⟨subd12_1_60, List.forall_mem_cons.2 ⟨subd12_1_61, List.forall_mem_cons.2 ⟨subd12_1_62, List.forall_mem_cons.2 ⟨subd12_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C077
