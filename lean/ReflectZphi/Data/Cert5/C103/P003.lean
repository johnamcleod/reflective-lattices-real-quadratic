import ReflectZphi.Data.Cert5.C103.Base

namespace ReflectZphi.Data.Cert5.C103

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd4_0_32 : subd4_0 [0, -2] = true := by decide +kernel
theorem subd4_0_33 : subd4_0 [0, -1] = true := by decide +kernel
theorem subd4_0_34 : subd4_0 [0, 0] = true := by decide +kernel
theorem subd4_0_35 : subd4_0 [0, 1] = true := by decide +kernel
theorem subd4_0_36 : subd4_0 [0, 2] = true := by decide +kernel
theorem subd4_0_37 : subd4_0 [0, 3] = true := by decide +kernel
theorem subd4_0_38 : subd4_0 [0, 4] = true := by decide +kernel
theorem subd4_0_39 : subd4_0 [1, -5] = true := by decide +kernel
theorem subd4_0_40 : subd4_0 [1, -4] = true := by decide +kernel
theorem subd4_0_41 : subd4_0 [1, -3] = true := by decide +kernel
theorem subd4_0_42 : subd4_0 [1, -2] = true := by decide +kernel
theorem subd4_0_43 : subd4_0 [1, -1] = true := by decide +kernel
theorem subd4_0_44 : subd4_0 [1, 0] = true := by decide +kernel
theorem subd4_0_45 : subd4_0 [1, 1] = true := by decide +kernel
theorem subd4_0_46 : subd4_0 [1, 2] = true := by decide +kernel
theorem subd4_0_47 : subd4_0 [1, 3] = true := by decide +kernel
theorem subd4_0_48 : subd4_0 [1, 4] = true := by decide +kernel
theorem subd4_0_49 : subd4_0 [2, -4] = true := by decide +kernel
theorem subd4_0_50 : subd4_0 [2, -3] = true := by decide +kernel
theorem subd4_0_51 : subd4_0 [2, -2] = true := by decide +kernel
theorem subd4_0_52 : subd4_0 [2, -1] = true := by decide +kernel
theorem subd4_0_53 : subd4_0 [2, 0] = true := by decide +kernel
theorem subd4_0_54 : subd4_0 [2, 1] = true := by decide +kernel
theorem subd4_0_55 : subd4_0 [2, 2] = true := by decide +kernel
theorem subd4_0_56 : subd4_0 [2, 3] = true := by decide +kernel
theorem subd4_0_57 : subd4_0 [2, 4] = true := by decide +kernel
theorem subd4_0_58 : subd4_0 [3, -4] = true := by decide +kernel
theorem subd4_0_59 : subd4_0 [3, -3] = true := by decide +kernel
theorem subd4_0_60 : subd4_0 [3, -2] = true := by decide +kernel
theorem subd4_0_61 : subd4_0 [3, -1] = true := by decide +kernel
theorem subd4_0_62 : subd4_0 [3, 0] = true := by decide +kernel
theorem subd4_0_63 : subd4_0 [3, 1] = true := by decide +kernel
theorem sbd4_0_1 : ∀ q ∈ blkd4_0_1, subd4_0 q = true := by
  unfold blkd4_0_1
  exact List.forall_mem_cons.2 ⟨subd4_0_32, List.forall_mem_cons.2 ⟨subd4_0_33, List.forall_mem_cons.2 ⟨subd4_0_34, List.forall_mem_cons.2 ⟨subd4_0_35, List.forall_mem_cons.2 ⟨subd4_0_36, List.forall_mem_cons.2 ⟨subd4_0_37, List.forall_mem_cons.2 ⟨subd4_0_38, List.forall_mem_cons.2 ⟨subd4_0_39, List.forall_mem_cons.2 ⟨subd4_0_40, List.forall_mem_cons.2 ⟨subd4_0_41, List.forall_mem_cons.2 ⟨subd4_0_42, List.forall_mem_cons.2 ⟨subd4_0_43, List.forall_mem_cons.2 ⟨subd4_0_44, List.forall_mem_cons.2 ⟨subd4_0_45, List.forall_mem_cons.2 ⟨subd4_0_46, List.forall_mem_cons.2 ⟨subd4_0_47, List.forall_mem_cons.2 ⟨subd4_0_48, List.forall_mem_cons.2 ⟨subd4_0_49, List.forall_mem_cons.2 ⟨subd4_0_50, List.forall_mem_cons.2 ⟨subd4_0_51, List.forall_mem_cons.2 ⟨subd4_0_52, List.forall_mem_cons.2 ⟨subd4_0_53, List.forall_mem_cons.2 ⟨subd4_0_54, List.forall_mem_cons.2 ⟨subd4_0_55, List.forall_mem_cons.2 ⟨subd4_0_56, List.forall_mem_cons.2 ⟨subd4_0_57, List.forall_mem_cons.2 ⟨subd4_0_58, List.forall_mem_cons.2 ⟨subd4_0_59, List.forall_mem_cons.2 ⟨subd4_0_60, List.forall_mem_cons.2 ⟨subd4_0_61, List.forall_mem_cons.2 ⟨subd4_0_62, List.forall_mem_cons.2 ⟨subd4_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_0_64 : subd4_0 [3, 2] = true := by decide +kernel
theorem subd4_0_65 : subd4_0 [3, 3] = true := by decide +kernel
theorem subd4_0_66 : subd4_0 [3, 4] = true := by decide +kernel
theorem subd4_0_67 : subd4_0 [4] = true := by decide +kernel
theorem sbd4_0_2 : ∀ q ∈ blkd4_0_2, subd4_0 q = true := by
  unfold blkd4_0_2
  exact List.forall_mem_cons.2 ⟨subd4_0_64, List.forall_mem_cons.2 ⟨subd4_0_65, List.forall_mem_cons.2 ⟨subd4_0_66, List.forall_mem_cons.2 ⟨subd4_0_67, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [-3] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-2, -4] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-2, -3] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-2, -2] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-2, -1] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-2, 0] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-2, 1] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [-2, 2] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [-1, -5] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [-1, -4] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [-1, 3] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [0, -4] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_20 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_21 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_22 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_23 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_24 : subd4_1 [0, 3] = true := by decide +kernel
theorem subd4_1_25 : subd4_1 [1, -4] = true := by decide +kernel
theorem subd4_1_26 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_27 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_28 : subd4_1 [1, -1] = true := by decide +kernel
theorem subd4_1_29 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_30 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_31 : subd4_1 [1, 2] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_cons.2 ⟨subd4_1_20, List.forall_mem_cons.2 ⟨subd4_1_21, List.forall_mem_cons.2 ⟨subd4_1_22, List.forall_mem_cons.2 ⟨subd4_1_23, List.forall_mem_cons.2 ⟨subd4_1_24, List.forall_mem_cons.2 ⟨subd4_1_25, List.forall_mem_cons.2 ⟨subd4_1_26, List.forall_mem_cons.2 ⟨subd4_1_27, List.forall_mem_cons.2 ⟨subd4_1_28, List.forall_mem_cons.2 ⟨subd4_1_29, List.forall_mem_cons.2 ⟨subd4_1_30, List.forall_mem_cons.2 ⟨subd4_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_32 : subd4_1 [1, 3] = true := by decide +kernel
theorem subd4_1_33 : subd4_1 [1, 4] = true := by decide +kernel
theorem subd4_1_34 : subd4_1 [2, -3] = true := by decide +kernel
theorem subd4_1_35 : subd4_1 [2, -2] = true := by decide +kernel
theorem subd4_1_36 : subd4_1 [2, -1] = true := by decide +kernel
theorem subd4_1_37 : subd4_1 [2, 0] = true := by decide +kernel
theorem subd4_1_38 : subd4_1 [2, 1] = true := by decide +kernel
theorem subd4_1_39 : subd4_1 [2, 2] = true := by decide +kernel
theorem subd4_1_40 : subd4_1 [2, 3] = true := by decide +kernel
theorem subd4_1_41 : subd4_1 [3] = true := by decide +kernel
theorem sbd4_1_1 : ∀ q ∈ blkd4_1_1, subd4_1 q = true := by
  unfold blkd4_1_1
  exact List.forall_mem_cons.2 ⟨subd4_1_32, List.forall_mem_cons.2 ⟨subd4_1_33, List.forall_mem_cons.2 ⟨subd4_1_34, List.forall_mem_cons.2 ⟨subd4_1_35, List.forall_mem_cons.2 ⟨subd4_1_36, List.forall_mem_cons.2 ⟨subd4_1_37, List.forall_mem_cons.2 ⟨subd4_1_38, List.forall_mem_cons.2 ⟨subd4_1_39, List.forall_mem_cons.2 ⟨subd4_1_40, List.forall_mem_cons.2 ⟨subd4_1_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C103
