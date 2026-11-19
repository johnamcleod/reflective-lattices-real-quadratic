import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_3_0 : subd6_3 [-3] = true := by decide +kernel
theorem subd6_3_1 : subd6_3 [-2, -5] = true := by decide +kernel
theorem subd6_3_2 : subd6_3 [-2, -4] = true := by decide +kernel
theorem subd6_3_3 : subd6_3 [-2, -3] = true := by decide +kernel
theorem subd6_3_4 : subd6_3 [-2, -2] = true := by decide +kernel
theorem subd6_3_5 : subd6_3 [-2, -1] = true := by decide +kernel
theorem subd6_3_6 : subd6_3 [-2, 0] = true := by decide +kernel
theorem subd6_3_7 : subd6_3 [-2, 1] = true := by decide +kernel
theorem subd6_3_8 : subd6_3 [-2, 2] = true := by decide +kernel
theorem subd6_3_9 : subd6_3 [-1, -5] = true := by decide +kernel
theorem subd6_3_10 : subd6_3 [-1, -4] = true := by decide +kernel
theorem subd6_3_11 : subd6_3 [-1, -3] = true := by decide +kernel
theorem subd6_3_12 : subd6_3 [-1, -2] = true := by decide +kernel
theorem subd6_3_13 : subd6_3 [-1, -1] = true := by decide +kernel
theorem subd6_3_14 : subd6_3 [-1, 0] = true := by decide +kernel
theorem subd6_3_15 : subd6_3 [-1, 1] = true := by decide +kernel
theorem subd6_3_16 : subd6_3 [-1, 2] = true := by decide +kernel
theorem subd6_3_17 : subd6_3 [-1, 3] = true := by decide +kernel
theorem subd6_3_18 : subd6_3 [0, -4] = true := by decide +kernel
theorem subd6_3_19 : subd6_3 [0, -3] = true := by decide +kernel
theorem subd6_3_20 : subd6_3 [0, -2] = true := by decide +kernel
theorem subd6_3_21 : subd6_3 [0, -1] = true := by decide +kernel
theorem subd6_3_22 : subd6_3 [0, 0] = true := by decide +kernel
theorem subd6_3_23 : subd6_3 [0, 1] = true := by decide +kernel
theorem subd6_3_24 : subd6_3 [0, 2] = true := by decide +kernel
theorem subd6_3_25 : subd6_3 [0, 3] = true := by decide +kernel
theorem subd6_3_26 : subd6_3 [1, -4] = true := by decide +kernel
theorem subd6_3_27 : subd6_3 [1, -3] = true := by decide +kernel
theorem subd6_3_28 : subd6_3 [1, -2] = true := by decide +kernel
theorem subd6_3_29 : subd6_3 [1, -1] = true := by decide +kernel
theorem subd6_3_30 : subd6_3 [1, 0] = true := by decide +kernel
theorem subd6_3_31 : subd6_3 [1, 1] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_cons.2 ⟨subd6_3_1, List.forall_mem_cons.2 ⟨subd6_3_2, List.forall_mem_cons.2 ⟨subd6_3_3, List.forall_mem_cons.2 ⟨subd6_3_4, List.forall_mem_cons.2 ⟨subd6_3_5, List.forall_mem_cons.2 ⟨subd6_3_6, List.forall_mem_cons.2 ⟨subd6_3_7, List.forall_mem_cons.2 ⟨subd6_3_8, List.forall_mem_cons.2 ⟨subd6_3_9, List.forall_mem_cons.2 ⟨subd6_3_10, List.forall_mem_cons.2 ⟨subd6_3_11, List.forall_mem_cons.2 ⟨subd6_3_12, List.forall_mem_cons.2 ⟨subd6_3_13, List.forall_mem_cons.2 ⟨subd6_3_14, List.forall_mem_cons.2 ⟨subd6_3_15, List.forall_mem_cons.2 ⟨subd6_3_16, List.forall_mem_cons.2 ⟨subd6_3_17, List.forall_mem_cons.2 ⟨subd6_3_18, List.forall_mem_cons.2 ⟨subd6_3_19, List.forall_mem_cons.2 ⟨subd6_3_20, List.forall_mem_cons.2 ⟨subd6_3_21, List.forall_mem_cons.2 ⟨subd6_3_22, List.forall_mem_cons.2 ⟨subd6_3_23, List.forall_mem_cons.2 ⟨subd6_3_24, List.forall_mem_cons.2 ⟨subd6_3_25, List.forall_mem_cons.2 ⟨subd6_3_26, List.forall_mem_cons.2 ⟨subd6_3_27, List.forall_mem_cons.2 ⟨subd6_3_28, List.forall_mem_cons.2 ⟨subd6_3_29, List.forall_mem_cons.2 ⟨subd6_3_30, List.forall_mem_cons.2 ⟨subd6_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_3_32 : subd6_3 [1, 2] = true := by decide +kernel
theorem subd6_3_33 : subd6_3 [1, 3] = true := by decide +kernel
theorem subd6_3_34 : subd6_3 [1, 4] = true := by decide +kernel
theorem subd6_3_35 : subd6_3 [2, -3] = true := by decide +kernel
theorem subd6_3_36 : subd6_3 [2, -2] = true := by decide +kernel
theorem subd6_3_37 : subd6_3 [2, -1] = true := by decide +kernel
theorem subd6_3_38 : subd6_3 [2, 0] = true := by decide +kernel
theorem subd6_3_39 : subd6_3 [2, 1] = true := by decide +kernel
theorem subd6_3_40 : subd6_3 [2, 2] = true := by decide +kernel
theorem subd6_3_41 : subd6_3 [2, 3] = true := by decide +kernel
theorem subd6_3_42 : subd6_3 [2, 4] = true := by decide +kernel
theorem subd6_3_43 : subd6_3 [3] = true := by decide +kernel
theorem sbd6_3_1 : ∀ q ∈ blkd6_3_1, subd6_3 q = true := by
  unfold blkd6_3_1
  exact List.forall_mem_cons.2 ⟨subd6_3_32, List.forall_mem_cons.2 ⟨subd6_3_33, List.forall_mem_cons.2 ⟨subd6_3_34, List.forall_mem_cons.2 ⟨subd6_3_35, List.forall_mem_cons.2 ⟨subd6_3_36, List.forall_mem_cons.2 ⟨subd6_3_37, List.forall_mem_cons.2 ⟨subd6_3_38, List.forall_mem_cons.2 ⟨subd6_3_39, List.forall_mem_cons.2 ⟨subd6_3_40, List.forall_mem_cons.2 ⟨subd6_3_41, List.forall_mem_cons.2 ⟨subd6_3_42, List.forall_mem_cons.2 ⟨subd6_3_43, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-1] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [0] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [1] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [-2] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [-1] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [0] = true := by decide +kernel
theorem subd6_5_3 : subd6_5 [1] = true := by decide +kernel
theorem subd6_5_4 : subd6_5 [2] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_cons.2 ⟨subd6_5_3, List.forall_mem_cons.2 ⟨subd6_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_6 : ldCheck G d6_6.U d6_6.ms ldd6_6 = true := by decide +kernel
theorem pre_okd6_6 : subPre G cell6 d6_6 = true := by decide +kernel
theorem subd6_6_0 : subd6_6 [-2] = true := by decide +kernel
theorem subd6_6_1 : subd6_6 [-1, -2] = true := by decide +kernel
theorem subd6_6_2 : subd6_6 [-1, -1] = true := by decide +kernel
theorem subd6_6_3 : subd6_6 [-1, 0] = true := by decide +kernel
theorem subd6_6_4 : subd6_6 [-1, 1] = true := by decide +kernel
theorem subd6_6_5 : subd6_6 [-1, 2] = true := by decide +kernel
theorem subd6_6_6 : subd6_6 [0, -3] = true := by decide +kernel
theorem subd6_6_7 : subd6_6 [0, -2] = true := by decide +kernel
theorem subd6_6_8 : subd6_6 [0, -1] = true := by decide +kernel
theorem subd6_6_9 : subd6_6 [0, 0] = true := by decide +kernel
theorem subd6_6_10 : subd6_6 [0, 1] = true := by decide +kernel
theorem subd6_6_11 : subd6_6 [0, 2] = true := by decide +kernel
theorem subd6_6_12 : subd6_6 [1, -3] = true := by decide +kernel
theorem subd6_6_13 : subd6_6 [1, -2] = true := by decide +kernel
theorem subd6_6_14 : subd6_6 [1, -1] = true := by decide +kernel
theorem subd6_6_15 : subd6_6 [1, 0] = true := by decide +kernel
theorem subd6_6_16 : subd6_6 [1, 1] = true := by decide +kernel
theorem subd6_6_17 : subd6_6 [2] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_cons.2 ⟨subd6_6_1, List.forall_mem_cons.2 ⟨subd6_6_2, List.forall_mem_cons.2 ⟨subd6_6_3, List.forall_mem_cons.2 ⟨subd6_6_4, List.forall_mem_cons.2 ⟨subd6_6_5, List.forall_mem_cons.2 ⟨subd6_6_6, List.forall_mem_cons.2 ⟨subd6_6_7, List.forall_mem_cons.2 ⟨subd6_6_8, List.forall_mem_cons.2 ⟨subd6_6_9, List.forall_mem_cons.2 ⟨subd6_6_10, List.forall_mem_cons.2 ⟨subd6_6_11, List.forall_mem_cons.2 ⟨subd6_6_12, List.forall_mem_cons.2 ⟨subd6_6_13, List.forall_mem_cons.2 ⟨subd6_6_14, List.forall_mem_cons.2 ⟨subd6_6_15, List.forall_mem_cons.2 ⟨subd6_6_16, List.forall_mem_cons.2 ⟨subd6_6_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_7 : ldCheck G d6_7.U d6_7.ms ldd6_7 = true := by decide +kernel
theorem pre_okd6_7 : subPre G cell6 d6_7 = true := by decide +kernel
theorem subd6_7_0 : subd6_7 [-3] = true := by decide +kernel
theorem subd6_7_1 : subd6_7 [-2] = true := by decide +kernel
theorem subd6_7_2 : subd6_7 [-1] = true := by decide +kernel
theorem subd6_7_3 : subd6_7 [0, -3] = true := by decide +kernel
theorem subd6_7_4 : subd6_7 [0, -2] = true := by decide +kernel
theorem subd6_7_5 : subd6_7 [0, -1] = true := by decide +kernel
theorem subd6_7_6 : subd6_7 [0, 0] = true := by decide +kernel
theorem subd6_7_7 : subd6_7 [0, 1] = true := by decide +kernel
theorem subd6_7_8 : subd6_7 [0, 2] = true := by decide +kernel
theorem subd6_7_9 : subd6_7 [1] = true := by decide +kernel
theorem subd6_7_10 : subd6_7 [2] = true := by decide +kernel
theorem subd6_7_11 : subd6_7 [3] = true := by decide +kernel
theorem sbd6_7_0 : ∀ q ∈ blkd6_7_0, subd6_7 q = true := by
  unfold blkd6_7_0
  exact List.forall_mem_cons.2 ⟨subd6_7_0, List.forall_mem_cons.2 ⟨subd6_7_1, List.forall_mem_cons.2 ⟨subd6_7_2, List.forall_mem_cons.2 ⟨subd6_7_3, List.forall_mem_cons.2 ⟨subd6_7_4, List.forall_mem_cons.2 ⟨subd6_7_5, List.forall_mem_cons.2 ⟨subd6_7_6, List.forall_mem_cons.2 ⟨subd6_7_7, List.forall_mem_cons.2 ⟨subd6_7_8, List.forall_mem_cons.2 ⟨subd6_7_9, List.forall_mem_cons.2 ⟨subd6_7_10, List.forall_mem_cons.2 ⟨subd6_7_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C132
