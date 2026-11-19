import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd5_5 : ldCheck G d5_5.U d5_5.ms ldd5_5 = true := by decide +kernel
theorem pre_okd5_5 : subPre G cell5 d5_5 = true := by decide +kernel
theorem subd5_5_0 : subd5_5 [-4] = true := by decide +kernel
theorem subd5_5_1 : subd5_5 [-3] = true := by decide +kernel
theorem subd5_5_2 : subd5_5 [-2, -3] = true := by decide +kernel
theorem subd5_5_3 : subd5_5 [-2, -2] = true := by decide +kernel
theorem subd5_5_4 : subd5_5 [-2, -1] = true := by decide +kernel
theorem subd5_5_5 : subd5_5 [-2, 0] = true := by decide +kernel
theorem subd5_5_6 : subd5_5 [-2, 1] = true := by decide +kernel
theorem subd5_5_7 : subd5_5 [-2, 2] = true := by decide +kernel
theorem subd5_5_8 : subd5_5 [-2, 3] = true := by decide +kernel
theorem subd5_5_9 : subd5_5 [-1, -4] = true := by decide +kernel
theorem subd5_5_10 : subd5_5 [-1, -3] = true := by decide +kernel
theorem subd5_5_11 : subd5_5 [-1, -2] = true := by decide +kernel
theorem subd5_5_12 : subd5_5 [-1, -1] = true := by decide +kernel
theorem subd5_5_13 : subd5_5 [-1, 0] = true := by decide +kernel
theorem subd5_5_14 : subd5_5 [-1, 1] = true := by decide +kernel
theorem subd5_5_15 : subd5_5 [-1, 2] = true := by decide +kernel
theorem subd5_5_16 : subd5_5 [-1, 3] = true := by decide +kernel
theorem subd5_5_17 : subd5_5 [-1, 4] = true := by decide +kernel
theorem subd5_5_18 : subd5_5 [0, -5] = true := by decide +kernel
theorem subd5_5_19 : subd5_5 [0, -4] = true := by decide +kernel
theorem subd5_5_20 : subd5_5 [0, -3] = true := by decide +kernel
theorem subd5_5_21 : subd5_5 [0, -2] = true := by decide +kernel
theorem subd5_5_22 : subd5_5 [0, -1] = true := by decide +kernel
theorem subd5_5_23 : subd5_5 [0, 0] = true := by decide +kernel
theorem subd5_5_24 : subd5_5 [0, 1] = true := by decide +kernel
theorem subd5_5_25 : subd5_5 [0, 2] = true := by decide +kernel
theorem subd5_5_26 : subd5_5 [0, 3] = true := by decide +kernel
theorem subd5_5_27 : subd5_5 [0, 4] = true := by decide +kernel
theorem subd5_5_28 : subd5_5 [1, -5] = true := by decide +kernel
theorem subd5_5_29 : subd5_5 [1, -4] = true := by decide +kernel
theorem subd5_5_30 : subd5_5 [1, -3] = true := by decide +kernel
theorem subd5_5_31 : subd5_5 [1, -2] = true := by decide +kernel
theorem sbd5_5_0 : ∀ q ∈ blkd5_5_0, subd5_5 q = true := by
  unfold blkd5_5_0
  exact List.forall_mem_cons.2 ⟨subd5_5_0, List.forall_mem_cons.2 ⟨subd5_5_1, List.forall_mem_cons.2 ⟨subd5_5_2, List.forall_mem_cons.2 ⟨subd5_5_3, List.forall_mem_cons.2 ⟨subd5_5_4, List.forall_mem_cons.2 ⟨subd5_5_5, List.forall_mem_cons.2 ⟨subd5_5_6, List.forall_mem_cons.2 ⟨subd5_5_7, List.forall_mem_cons.2 ⟨subd5_5_8, List.forall_mem_cons.2 ⟨subd5_5_9, List.forall_mem_cons.2 ⟨subd5_5_10, List.forall_mem_cons.2 ⟨subd5_5_11, List.forall_mem_cons.2 ⟨subd5_5_12, List.forall_mem_cons.2 ⟨subd5_5_13, List.forall_mem_cons.2 ⟨subd5_5_14, List.forall_mem_cons.2 ⟨subd5_5_15, List.forall_mem_cons.2 ⟨subd5_5_16, List.forall_mem_cons.2 ⟨subd5_5_17, List.forall_mem_cons.2 ⟨subd5_5_18, List.forall_mem_cons.2 ⟨subd5_5_19, List.forall_mem_cons.2 ⟨subd5_5_20, List.forall_mem_cons.2 ⟨subd5_5_21, List.forall_mem_cons.2 ⟨subd5_5_22, List.forall_mem_cons.2 ⟨subd5_5_23, List.forall_mem_cons.2 ⟨subd5_5_24, List.forall_mem_cons.2 ⟨subd5_5_25, List.forall_mem_cons.2 ⟨subd5_5_26, List.forall_mem_cons.2 ⟨subd5_5_27, List.forall_mem_cons.2 ⟨subd5_5_28, List.forall_mem_cons.2 ⟨subd5_5_29, List.forall_mem_cons.2 ⟨subd5_5_30, List.forall_mem_cons.2 ⟨subd5_5_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_5_32 : subd5_5 [1, -1] = true := by decide +kernel
theorem subd5_5_33 : subd5_5 [1, 0] = true := by decide +kernel
theorem subd5_5_34 : subd5_5 [1, 1] = true := by decide +kernel
theorem subd5_5_35 : subd5_5 [1, 2] = true := by decide +kernel
theorem subd5_5_36 : subd5_5 [1, 3] = true := by decide +kernel
theorem subd5_5_37 : subd5_5 [2, -4] = true := by decide +kernel
theorem subd5_5_38 : subd5_5 [2, -3] = true := by decide +kernel
theorem subd5_5_39 : subd5_5 [2, -2] = true := by decide +kernel
theorem subd5_5_40 : subd5_5 [2, -1] = true := by decide +kernel
theorem subd5_5_41 : subd5_5 [2, 0] = true := by decide +kernel
theorem subd5_5_42 : subd5_5 [2, 1] = true := by decide +kernel
theorem subd5_5_43 : subd5_5 [2, 2] = true := by decide +kernel
theorem subd5_5_44 : subd5_5 [3] = true := by decide +kernel
theorem subd5_5_45 : subd5_5 [4] = true := by decide +kernel
theorem sbd5_5_1 : ∀ q ∈ blkd5_5_1, subd5_5 q = true := by
  unfold blkd5_5_1
  exact List.forall_mem_cons.2 ⟨subd5_5_32, List.forall_mem_cons.2 ⟨subd5_5_33, List.forall_mem_cons.2 ⟨subd5_5_34, List.forall_mem_cons.2 ⟨subd5_5_35, List.forall_mem_cons.2 ⟨subd5_5_36, List.forall_mem_cons.2 ⟨subd5_5_37, List.forall_mem_cons.2 ⟨subd5_5_38, List.forall_mem_cons.2 ⟨subd5_5_39, List.forall_mem_cons.2 ⟨subd5_5_40, List.forall_mem_cons.2 ⟨subd5_5_41, List.forall_mem_cons.2 ⟨subd5_5_42, List.forall_mem_cons.2 ⟨subd5_5_43, List.forall_mem_cons.2 ⟨subd5_5_44, List.forall_mem_cons.2 ⟨subd5_5_45, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd5_6 : ldCheck G d5_6.U d5_6.ms ldd5_6 = true := by decide +kernel
theorem pre_okd5_6 : subPre G cell5 d5_6 = true := by decide +kernel
theorem subd5_6_0 : subd5_6 [-1] = true := by decide +kernel
theorem subd5_6_1 : subd5_6 [0] = true := by decide +kernel
theorem subd5_6_2 : subd5_6 [1] = true := by decide +kernel
theorem sbd5_6_0 : ∀ q ∈ blkd5_6_0, subd5_6 q = true := by
  unfold blkd5_6_0
  exact List.forall_mem_cons.2 ⟨subd5_6_0, List.forall_mem_cons.2 ⟨subd5_6_1, List.forall_mem_cons.2 ⟨subd5_6_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd5_7 : ldCheck G d5_7.U d5_7.ms ldd5_7 = true := by decide +kernel
theorem pre_okd5_7 : subPre G cell5 d5_7 = true := by decide +kernel
theorem subd5_7_0 : subd5_7 [-2] = true := by decide +kernel
theorem subd5_7_1 : subd5_7 [-1] = true := by decide +kernel
theorem subd5_7_2 : subd5_7 [0] = true := by decide +kernel
theorem subd5_7_3 : subd5_7 [1] = true := by decide +kernel
theorem subd5_7_4 : subd5_7 [2] = true := by decide +kernel
theorem sbd5_7_0 : ∀ q ∈ blkd5_7_0, subd5_7 q = true := by
  unfold blkd5_7_0
  exact List.forall_mem_cons.2 ⟨subd5_7_0, List.forall_mem_cons.2 ⟨subd5_7_1, List.forall_mem_cons.2 ⟨subd5_7_2, List.forall_mem_cons.2 ⟨subd5_7_3, List.forall_mem_cons.2 ⟨subd5_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel
theorem subd6_0_0 : subd6_0 [] = true := by decide +kernel
theorem sbd6_0_0 : ∀ q ∈ blkd6_0_0, subd6_0 q = true := by
  unfold blkd6_0_0
  exact List.forall_mem_cons.2 ⟨subd6_0_0, List.forall_mem_nil _⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_nil _⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C122
