import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_7 : ldCheck G d5_7.U d5_7.ms ldd5_7 = true := by decide +kernel
theorem pre_okd5_7 : subPre G cell5 d5_7 = true := by decide +kernel
theorem subd5_7_0 : subd5_7 [-6] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-5, -3] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [-5, -2] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [-5, -1] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [-5, 0] = true := by decide +kernel
theorem subd5_7_5 : subd5_7 [-5, 1] = true := by decide +kernel
theorem subd5_7_6 : subd5_7 [-5, 2] = true := by decide +kernel
theorem subd5_7_7 : subd5_7 [-5, 3] = true := by decide +kernel
theorem subd5_7_8 : subd5_7 [-5, 4] = true := by decide +kernel
theorem subd5_7_9 : subd5_7 [-4, -4] = true := by decide +kernel
theorem subd5_7_10 : subd5_7 [-4, -3] = true := by decide +kernel
theorem subd5_7_11 : subd5_7 [-4, -2] = true := by decide +kernel
theorem subd5_7_12 : subd5_7 [-4, -1] = true := by decide +kernel
theorem subd5_7_13 : subd5_7 [-4, 0] = true := by decide +kernel
theorem subd5_7_14 : subd5_7 [-4, 1] = true := by decide +kernel
theorem subd5_7_15 : subd5_7 [-4, 2] = true := by decide +kernel
theorem subd5_7_16 : subd5_7 [-4, 3] = true := by decide +kernel
theorem subd5_7_17 : subd5_7 [-4, 4] = true := by decide +kernel
theorem subd5_7_18 : subd5_7 [-4, 5] = true := by decide +kernel
theorem subd5_7_19 : subd5_7 [-3, -5] = true := by decide +kernel
theorem subd5_7_20 : subd5_7 [-3, -4] = true := by decide +kernel
theorem subd5_7_21 : subd5_7 [-3, -3] = true := by decide +kernel
theorem subd5_7_22 : subd5_7 [-3, -2] = true := by decide +kernel
theorem subd5_7_23 : subd5_7 [-3, -1] = true := by decide +kernel
theorem subd5_7_24 : subd5_7 [-3, 0] = true := by decide +kernel
theorem subd5_7_25 : subd5_7 [-3, 1] = true := by decide +kernel
theorem subd5_7_26 : subd5_7 [-3, 2] = true := by decide +kernel
theorem subd5_7_27 : subd5_7 [-3, 3] = true := by decide +kernel
theorem subd5_7_28 : subd5_7 [-3, 4] = true := by decide +kernel
theorem subd5_7_29 : subd5_7 [-3, 5] = true := by decide +kernel
theorem subd5_7_30 : subd5_7 [-2, -6] = true := by decide +kernel
theorem subd5_7_31 : subd5_7 [-2, -5] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_cons.2 ⟨subd5_7_5, List.forall_mem_cons.2 ⟨subd5_7_6, List.forall_mem_cons.2 ⟨subd5_7_7, List.forall_mem_cons.2 ⟨subd5_7_8, List.forall_mem_cons.2 ⟨subd5_7_9, List.forall_mem_cons.2 ⟨subd5_7_10, List.forall_mem_cons.2 ⟨subd5_7_11, List.forall_mem_cons.2 ⟨subd5_7_12, List.forall_mem_cons.2 ⟨subd5_7_13, List.forall_mem_cons.2 ⟨subd5_7_14, List.forall_mem_cons.2 ⟨subd5_7_15, List.forall_mem_cons.2 ⟨subd5_7_16, List.forall_mem_cons.2 ⟨subd5_7_17, List.forall_mem_cons.2 ⟨subd5_7_18, List.forall_mem_cons.2 ⟨subd5_7_19, List.forall_mem_cons.2 ⟨subd5_7_20, List.forall_mem_cons.2 ⟨subd5_7_21, List.forall_mem_cons.2 ⟨subd5_7_22, List.forall_mem_cons.2 ⟨subd5_7_23, List.forall_mem_cons.2 ⟨subd5_7_24, List.forall_mem_cons.2 ⟨subd5_7_25, List.forall_mem_cons.2 ⟨subd5_7_26, List.forall_mem_cons.2 ⟨subd5_7_27, List.forall_mem_cons.2 ⟨subd5_7_28, List.forall_mem_cons.2 ⟨subd5_7_29, List.forall_mem_cons.2 ⟨subd5_7_30, List.forall_mem_cons.2 ⟨subd5_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_7_32 : subd5_7 [-2, -4] = true := by decide +kernel
theorem subd5_7_33 : subd5_7 [-2, -3] = true := by decide +kernel
theorem subd5_7_34 : subd5_7 [-2, -2] = true := by decide +kernel
theorem subd5_7_35 : subd5_7 [-2, -1] = true := by decide +kernel
theorem subd5_7_36 : subd5_7 [-2, 0] = true := by decide +kernel
theorem subd5_7_37 : subd5_7 [-2, 1] = true := by decide +kernel
theorem subd5_7_38 : subd5_7 [-2, 2] = true := by decide +kernel
theorem subd5_7_39 : subd5_7 [-2, 3] = true := by decide +kernel
theorem subd5_7_40 : subd5_7 [-2, 4] = true := by decide +kernel
theorem subd5_7_41 : subd5_7 [-2, 5] = true := by decide +kernel
theorem subd5_7_42 : subd5_7 [-2, 6] = true := by decide +kernel
theorem subd5_7_43 : subd5_7 [-1, -6] = true := by decide +kernel
theorem subd5_7_44 : subd5_7 [-1, -5] = true := by decide +kernel
theorem subd5_7_45 : subd5_7 [-1, -4] = true := by decide +kernel
theorem subd5_7_46 : subd5_7 [-1, -3] = true := by decide +kernel
theorem subd5_7_47 : subd5_7 [-1, -2] = true := by decide +kernel
theorem subd5_7_48 : subd5_7 [-1, -1] = true := by decide +kernel
theorem subd5_7_49 : subd5_7 [-1, 0] = true := by decide +kernel
theorem subd5_7_50 : subd5_7 [-1, 1] = true := by decide +kernel
theorem subd5_7_51 : subd5_7 [-1, 2] = true := by decide +kernel
theorem subd5_7_52 : subd5_7 [-1, 3] = true := by decide +kernel
theorem subd5_7_53 : subd5_7 [-1, 4] = true := by decide +kernel
theorem subd5_7_54 : subd5_7 [-1, 5] = true := by decide +kernel
theorem subd5_7_55 : subd5_7 [-1, 6] = true := by decide +kernel
theorem subd5_7_56 : subd5_7 [0, -6] = true := by decide +kernel
theorem subd5_7_57 : subd5_7 [0, -5] = true := by decide +kernel
theorem subd5_7_58 : subd5_7 [0, -4] = true := by decide +kernel
theorem subd5_7_59 : subd5_7 [0, -3] = true := by decide +kernel
theorem subd5_7_60 : subd5_7 [0, -2] = true := by decide +kernel
theorem subd5_7_61 : subd5_7 [0, -1] = true := by decide +kernel
theorem subd5_7_62 : subd5_7 [0, 0] = true := by decide +kernel
theorem subd5_7_63 : subd5_7 [0, 1] = true := by decide +kernel
theorem sbd5_7_1 : ∀ q ∈ blkd5_7_1, subd5_7 q = true := by
  unfold blkd5_7_1
  exact List.forall_mem_cons.2 ⟨subd5_7_32, List.forall_mem_cons.2 ⟨subd5_7_33, List.forall_mem_cons.2 ⟨subd5_7_34, List.forall_mem_cons.2 ⟨subd5_7_35, List.forall_mem_cons.2 ⟨subd5_7_36, List.forall_mem_cons.2 ⟨subd5_7_37, List.forall_mem_cons.2 ⟨subd5_7_38, List.forall_mem_cons.2 ⟨subd5_7_39, List.forall_mem_cons.2 ⟨subd5_7_40, List.forall_mem_cons.2 ⟨subd5_7_41, List.forall_mem_cons.2 ⟨subd5_7_42, List.forall_mem_cons.2 ⟨subd5_7_43, List.forall_mem_cons.2 ⟨subd5_7_44, List.forall_mem_cons.2 ⟨subd5_7_45, List.forall_mem_cons.2 ⟨subd5_7_46, List.forall_mem_cons.2 ⟨subd5_7_47, List.forall_mem_cons.2 ⟨subd5_7_48, List.forall_mem_cons.2 ⟨subd5_7_49, List.forall_mem_cons.2 ⟨subd5_7_50, List.forall_mem_cons.2 ⟨subd5_7_51, List.forall_mem_cons.2 ⟨subd5_7_52, List.forall_mem_cons.2 ⟨subd5_7_53, List.forall_mem_cons.2 ⟨subd5_7_54, List.forall_mem_cons.2 ⟨subd5_7_55, List.forall_mem_cons.2 ⟨subd5_7_56, List.forall_mem_cons.2 ⟨subd5_7_57, List.forall_mem_cons.2 ⟨subd5_7_58, List.forall_mem_cons.2 ⟨subd5_7_59, List.forall_mem_cons.2 ⟨subd5_7_60, List.forall_mem_cons.2 ⟨subd5_7_61, List.forall_mem_cons.2 ⟨subd5_7_62, List.forall_mem_cons.2 ⟨subd5_7_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
