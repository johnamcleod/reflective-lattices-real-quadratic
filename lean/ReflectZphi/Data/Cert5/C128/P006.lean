import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_3_0 : subd3_3 [-4] = true := by decide +kernel
theorem subd3_3_1 : subd3_3 [-3, -6] = true := by decide +kernel
theorem subd3_3_2 : subd3_3 [-3, -5] = true := by decide +kernel
theorem subd3_3_3 : subd3_3 [-3, -4] = true := by decide +kernel
theorem subd3_3_4 : subd3_3 [-3, -3] = true := by decide +kernel
theorem subd3_3_5 : subd3_3 [-3, -2] = true := by decide +kernel
theorem subd3_3_6 : subd3_3 [-3, -1] = true := by decide +kernel
theorem subd3_3_7 : subd3_3 [-3, 0] = true := by decide +kernel
theorem subd3_3_8 : subd3_3 [-3, 1] = true := by decide +kernel
theorem subd3_3_9 : subd3_3 [-3, 2] = true := by decide +kernel
theorem subd3_3_10 : subd3_3 [-2, -6] = true := by decide +kernel
theorem subd3_3_11 : subd3_3 [-2, -5] = true := by decide +kernel
theorem subd3_3_12 : subd3_3 [-2, -4] = true := by decide +kernel
theorem subd3_3_13 : subd3_3 [-2, -3] = true := by decide +kernel
theorem subd3_3_14 : subd3_3 [-2, -2] = true := by decide +kernel
theorem subd3_3_15 : subd3_3 [-2, -1] = true := by decide +kernel
theorem subd3_3_16 : subd3_3 [-2, 0] = true := by decide +kernel
theorem subd3_3_17 : subd3_3 [-2, 1] = true := by decide +kernel
theorem subd3_3_18 : subd3_3 [-2, 2] = true := by decide +kernel
theorem subd3_3_19 : subd3_3 [-2, 3] = true := by decide +kernel
theorem subd3_3_20 : subd3_3 [-1, -6] = true := by decide +kernel
theorem subd3_3_21 : subd3_3 [-1, -5] = true := by decide +kernel
theorem subd3_3_22 : subd3_3 [-1, -4] = true := by decide +kernel
theorem subd3_3_23 : subd3_3 [-1, -3] = true := by decide +kernel
theorem subd3_3_24 : subd3_3 [-1, -2] = true := by decide +kernel
theorem subd3_3_25 : subd3_3 [-1, -1] = true := by decide +kernel
theorem subd3_3_26 : subd3_3 [-1, 0] = true := by decide +kernel
theorem subd3_3_27 : subd3_3 [-1, 1] = true := by decide +kernel
theorem subd3_3_28 : subd3_3 [-1, 2] = true := by decide +kernel
theorem subd3_3_29 : subd3_3 [-1, 3] = true := by decide +kernel
theorem subd3_3_30 : subd3_3 [-1, 4] = true := by decide +kernel
theorem subd3_3_31 : subd3_3 [0, -5] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_cons.2 ⟨subd3_3_1, List.forall_mem_cons.2 ⟨subd3_3_2, List.forall_mem_cons.2 ⟨subd3_3_3, List.forall_mem_cons.2 ⟨subd3_3_4, List.forall_mem_cons.2 ⟨subd3_3_5, List.forall_mem_cons.2 ⟨subd3_3_6, List.forall_mem_cons.2 ⟨subd3_3_7, List.forall_mem_cons.2 ⟨subd3_3_8, List.forall_mem_cons.2 ⟨subd3_3_9, List.forall_mem_cons.2 ⟨subd3_3_10, List.forall_mem_cons.2 ⟨subd3_3_11, List.forall_mem_cons.2 ⟨subd3_3_12, List.forall_mem_cons.2 ⟨subd3_3_13, List.forall_mem_cons.2 ⟨subd3_3_14, List.forall_mem_cons.2 ⟨subd3_3_15, List.forall_mem_cons.2 ⟨subd3_3_16, List.forall_mem_cons.2 ⟨subd3_3_17, List.forall_mem_cons.2 ⟨subd3_3_18, List.forall_mem_cons.2 ⟨subd3_3_19, List.forall_mem_cons.2 ⟨subd3_3_20, List.forall_mem_cons.2 ⟨subd3_3_21, List.forall_mem_cons.2 ⟨subd3_3_22, List.forall_mem_cons.2 ⟨subd3_3_23, List.forall_mem_cons.2 ⟨subd3_3_24, List.forall_mem_cons.2 ⟨subd3_3_25, List.forall_mem_cons.2 ⟨subd3_3_26, List.forall_mem_cons.2 ⟨subd3_3_27, List.forall_mem_cons.2 ⟨subd3_3_28, List.forall_mem_cons.2 ⟨subd3_3_29, List.forall_mem_cons.2 ⟨subd3_3_30, List.forall_mem_cons.2 ⟨subd3_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_3_32 : subd3_3 [0, -4] = true := by decide +kernel
theorem subd3_3_33 : subd3_3 [0, -3] = true := by decide +kernel
theorem subd3_3_34 : subd3_3 [0, -2] = true := by decide +kernel
theorem subd3_3_35 : subd3_3 [0, -1] = true := by decide +kernel
theorem subd3_3_36 : subd3_3 [0, 0] = true := by decide +kernel
theorem subd3_3_37 : subd3_3 [0, 1] = true := by decide +kernel
theorem subd3_3_38 : subd3_3 [0, 2] = true := by decide +kernel
theorem subd3_3_39 : subd3_3 [0, 3] = true := by decide +kernel
theorem subd3_3_40 : subd3_3 [0, 4] = true := by decide +kernel
theorem subd3_3_41 : subd3_3 [1, -5] = true := by decide +kernel
theorem subd3_3_42 : subd3_3 [1, -4] = true := by decide +kernel
theorem subd3_3_43 : subd3_3 [1, -3] = true := by decide +kernel
theorem subd3_3_44 : subd3_3 [1, -2] = true := by decide +kernel
theorem subd3_3_45 : subd3_3 [1, -1] = true := by decide +kernel
theorem subd3_3_46 : subd3_3 [1, 0] = true := by decide +kernel
theorem subd3_3_47 : subd3_3 [1, 1] = true := by decide +kernel
theorem subd3_3_48 : subd3_3 [1, 2] = true := by decide +kernel
theorem subd3_3_49 : subd3_3 [1, 3] = true := by decide +kernel
theorem subd3_3_50 : subd3_3 [1, 4] = true := by decide +kernel
theorem subd3_3_51 : subd3_3 [1, 5] = true := by decide +kernel
theorem subd3_3_52 : subd3_3 [2, -4] = true := by decide +kernel
theorem subd3_3_53 : subd3_3 [2, -3] = true := by decide +kernel
theorem subd3_3_54 : subd3_3 [2, -2] = true := by decide +kernel
theorem subd3_3_55 : subd3_3 [2, -1] = true := by decide +kernel
theorem subd3_3_56 : subd3_3 [2, 0] = true := by decide +kernel
theorem subd3_3_57 : subd3_3 [2, 1] = true := by decide +kernel
theorem subd3_3_58 : subd3_3 [2, 2] = true := by decide +kernel
theorem subd3_3_59 : subd3_3 [2, 3] = true := by decide +kernel
theorem subd3_3_60 : subd3_3 [2, 4] = true := by decide +kernel
theorem subd3_3_61 : subd3_3 [2, 5] = true := by decide +kernel
theorem subd3_3_62 : subd3_3 [3, -3] = true := by decide +kernel
theorem subd3_3_63 : subd3_3 [3, -2] = true := by decide +kernel
theorem sbd3_3_1 : ∀ q ∈ blkd3_3_1, subd3_3 q = true := by
  unfold blkd3_3_1
  exact List.forall_mem_cons.2 ⟨subd3_3_32, List.forall_mem_cons.2 ⟨subd3_3_33, List.forall_mem_cons.2 ⟨subd3_3_34, List.forall_mem_cons.2 ⟨subd3_3_35, List.forall_mem_cons.2 ⟨subd3_3_36, List.forall_mem_cons.2 ⟨subd3_3_37, List.forall_mem_cons.2 ⟨subd3_3_38, List.forall_mem_cons.2 ⟨subd3_3_39, List.forall_mem_cons.2 ⟨subd3_3_40, List.forall_mem_cons.2 ⟨subd3_3_41, List.forall_mem_cons.2 ⟨subd3_3_42, List.forall_mem_cons.2 ⟨subd3_3_43, List.forall_mem_cons.2 ⟨subd3_3_44, List.forall_mem_cons.2 ⟨subd3_3_45, List.forall_mem_cons.2 ⟨subd3_3_46, List.forall_mem_cons.2 ⟨subd3_3_47, List.forall_mem_cons.2 ⟨subd3_3_48, List.forall_mem_cons.2 ⟨subd3_3_49, List.forall_mem_cons.2 ⟨subd3_3_50, List.forall_mem_cons.2 ⟨subd3_3_51, List.forall_mem_cons.2 ⟨subd3_3_52, List.forall_mem_cons.2 ⟨subd3_3_53, List.forall_mem_cons.2 ⟨subd3_3_54, List.forall_mem_cons.2 ⟨subd3_3_55, List.forall_mem_cons.2 ⟨subd3_3_56, List.forall_mem_cons.2 ⟨subd3_3_57, List.forall_mem_cons.2 ⟨subd3_3_58, List.forall_mem_cons.2 ⟨subd3_3_59, List.forall_mem_cons.2 ⟨subd3_3_60, List.forall_mem_cons.2 ⟨subd3_3_61, List.forall_mem_cons.2 ⟨subd3_3_62, List.forall_mem_cons.2 ⟨subd3_3_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd3_3_64 : subd3_3 [3, -1] = true := by decide +kernel
theorem subd3_3_65 : subd3_3 [3, 0] = true := by decide +kernel
theorem subd3_3_66 : subd3_3 [3, 1] = true := by decide +kernel
theorem subd3_3_67 : subd3_3 [3, 2] = true := by decide +kernel
theorem subd3_3_68 : subd3_3 [3, 3] = true := by decide +kernel
theorem subd3_3_69 : subd3_3 [3, 4] = true := by decide +kernel
theorem subd3_3_70 : subd3_3 [3, 5] = true := by decide +kernel
theorem subd3_3_71 : subd3_3 [4] = true := by decide +kernel
theorem sbd3_3_2 : ∀ q ∈ blkd3_3_2, subd3_3 q = true := by
  unfold blkd3_3_2
  exact List.forall_mem_cons.2 ⟨subd3_3_64, List.forall_mem_cons.2 ⟨subd3_3_65, List.forall_mem_cons.2 ⟨subd3_3_66, List.forall_mem_cons.2 ⟨subd3_3_67, List.forall_mem_cons.2 ⟨subd3_3_68, List.forall_mem_cons.2 ⟨subd3_3_69, List.forall_mem_cons.2 ⟨subd3_3_70, List.forall_mem_cons.2 ⟨subd3_3_71, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd3_4 : ldCheck G d3_4.U d3_4.ms ldd3_4 = true := by decide +kernel
theorem pre_okd3_4 : subPre G cell3 d3_4 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
