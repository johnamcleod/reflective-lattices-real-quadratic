import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-1] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [0, -3] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [0, -2] = true := by decide +kernel
theorem subd8_2_3 : subd8_2 [0, -1] = true := by decide +kernel
theorem subd8_2_4 : subd8_2 [0, 0] = true := by decide +kernel
theorem subd8_2_5 : subd8_2 [0, 1] = true := by decide +kernel
theorem subd8_2_6 : subd8_2 [0, 2] = true := by decide +kernel
theorem subd8_2_7 : subd8_2 [1] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_cons.2 ⟨subd8_2_3, List.forall_mem_cons.2 ⟨subd8_2_4, List.forall_mem_cons.2 ⟨subd8_2_5, List.forall_mem_cons.2 ⟨subd8_2_6, List.forall_mem_cons.2 ⟨subd8_2_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-3] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [-2, -3] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [-2, -2] = true := by decide +kernel
theorem subd8_3_3 : subd8_3 [-2, -1] = true := by decide +kernel
theorem subd8_3_4 : subd8_3 [-2, 0] = true := by decide +kernel
theorem subd8_3_5 : subd8_3 [-2, 1] = true := by decide +kernel
theorem subd8_3_6 : subd8_3 [-2, 2] = true := by decide +kernel
theorem subd8_3_7 : subd8_3 [-2, 3] = true := by decide +kernel
theorem subd8_3_8 : subd8_3 [-1, -4] = true := by decide +kernel
theorem subd8_3_9 : subd8_3 [-1, -3] = true := by decide +kernel
theorem subd8_3_10 : subd8_3 [-1, -2] = true := by decide +kernel
theorem subd8_3_11 : subd8_3 [-1, -1] = true := by decide +kernel
theorem subd8_3_12 : subd8_3 [-1, 0] = true := by decide +kernel
theorem subd8_3_13 : subd8_3 [-1, 1] = true := by decide +kernel
theorem subd8_3_14 : subd8_3 [-1, 2] = true := by decide +kernel
theorem subd8_3_15 : subd8_3 [-1, 3] = true := by decide +kernel
theorem subd8_3_16 : subd8_3 [0, -4] = true := by decide +kernel
theorem subd8_3_17 : subd8_3 [0, -3] = true := by decide +kernel
theorem subd8_3_18 : subd8_3 [0, -2] = true := by decide +kernel
theorem subd8_3_19 : subd8_3 [0, -1] = true := by decide +kernel
theorem subd8_3_20 : subd8_3 [0, 0] = true := by decide +kernel
theorem subd8_3_21 : subd8_3 [0, 1] = true := by decide +kernel
theorem subd8_3_22 : subd8_3 [0, 2] = true := by decide +kernel
theorem subd8_3_23 : subd8_3 [0, 3] = true := by decide +kernel
theorem subd8_3_24 : subd8_3 [1, -4] = true := by decide +kernel
theorem subd8_3_25 : subd8_3 [1, -3] = true := by decide +kernel
theorem subd8_3_26 : subd8_3 [1, -2] = true := by decide +kernel
theorem subd8_3_27 : subd8_3 [1, -1] = true := by decide +kernel
theorem subd8_3_28 : subd8_3 [1, 0] = true := by decide +kernel
theorem subd8_3_29 : subd8_3 [1, 1] = true := by decide +kernel
theorem subd8_3_30 : subd8_3 [1, 2] = true := by decide +kernel
theorem subd8_3_31 : subd8_3 [1, 3] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_cons.2 ⟨subd8_3_3, List.forall_mem_cons.2 ⟨subd8_3_4, List.forall_mem_cons.2 ⟨subd8_3_5, List.forall_mem_cons.2 ⟨subd8_3_6, List.forall_mem_cons.2 ⟨subd8_3_7, List.forall_mem_cons.2 ⟨subd8_3_8, List.forall_mem_cons.2 ⟨subd8_3_9, List.forall_mem_cons.2 ⟨subd8_3_10, List.forall_mem_cons.2 ⟨subd8_3_11, List.forall_mem_cons.2 ⟨subd8_3_12, List.forall_mem_cons.2 ⟨subd8_3_13, List.forall_mem_cons.2 ⟨subd8_3_14, List.forall_mem_cons.2 ⟨subd8_3_15, List.forall_mem_cons.2 ⟨subd8_3_16, List.forall_mem_cons.2 ⟨subd8_3_17, List.forall_mem_cons.2 ⟨subd8_3_18, List.forall_mem_cons.2 ⟨subd8_3_19, List.forall_mem_cons.2 ⟨subd8_3_20, List.forall_mem_cons.2 ⟨subd8_3_21, List.forall_mem_cons.2 ⟨subd8_3_22, List.forall_mem_cons.2 ⟨subd8_3_23, List.forall_mem_cons.2 ⟨subd8_3_24, List.forall_mem_cons.2 ⟨subd8_3_25, List.forall_mem_cons.2 ⟨subd8_3_26, List.forall_mem_cons.2 ⟨subd8_3_27, List.forall_mem_cons.2 ⟨subd8_3_28, List.forall_mem_cons.2 ⟨subd8_3_29, List.forall_mem_cons.2 ⟨subd8_3_30, List.forall_mem_cons.2 ⟨subd8_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_3_32 : subd8_3 [2, -4] = true := by decide +kernel
theorem subd8_3_33 : subd8_3 [2, -3] = true := by decide +kernel
theorem subd8_3_34 : subd8_3 [2, -2] = true := by decide +kernel
theorem subd8_3_35 : subd8_3 [2, -1] = true := by decide +kernel
theorem subd8_3_36 : subd8_3 [2, 0] = true := by decide +kernel
theorem subd8_3_37 : subd8_3 [2, 1] = true := by decide +kernel
theorem subd8_3_38 : subd8_3 [2, 2] = true := by decide +kernel
theorem subd8_3_39 : subd8_3 [3] = true := by decide +kernel
theorem sbd8_3_1 : ∀ q ∈ blkd8_3_1, subd8_3 q = true := by
  unfold blkd8_3_1
  exact List.forall_mem_cons.2 ⟨subd8_3_32, List.forall_mem_cons.2 ⟨subd8_3_33, List.forall_mem_cons.2 ⟨subd8_3_34, List.forall_mem_cons.2 ⟨subd8_3_35, List.forall_mem_cons.2 ⟨subd8_3_36, List.forall_mem_cons.2 ⟨subd8_3_37, List.forall_mem_cons.2 ⟨subd8_3_38, List.forall_mem_cons.2 ⟨subd8_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel
theorem subd8_4_0 : subd8_4 [] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_nil _⟩
theorem ld_okd8_5 : ldCheck G d8_5.U d8_5.ms ldd8_5 = true := by decide +kernel
theorem pre_okd8_5 : subPre G cell8 d8_5 = true := by decide +kernel
theorem subd8_5_0 : subd8_5 [-1] = true := by decide +kernel
theorem subd8_5_1 : subd8_5 [0] = true := by decide +kernel
theorem subd8_5_2 : subd8_5 [1] = true := by decide +kernel
theorem sbd8_5_0 : ∀ q ∈ blkd8_5_0, subd8_5 q = true := by
  unfold blkd8_5_0
  exact List.forall_mem_cons.2 ⟨subd8_5_0, List.forall_mem_cons.2 ⟨subd8_5_1, List.forall_mem_cons.2 ⟨subd8_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_6 : ldCheck G d8_6.U d8_6.ms ldd8_6 = true := by decide +kernel
theorem pre_okd8_6 : subPre G cell8 d8_6 = true := by decide +kernel
theorem subd8_6_0 : subd8_6 [-2] = true := by decide +kernel
theorem subd8_6_1 : subd8_6 [-1, -4] = true := by decide +kernel
theorem subd8_6_2 : subd8_6 [-1, -3] = true := by decide +kernel
theorem subd8_6_3 : subd8_6 [-1, -2] = true := by decide +kernel
theorem subd8_6_4 : subd8_6 [-1, -1] = true := by decide +kernel
theorem subd8_6_5 : subd8_6 [-1, 0] = true := by decide +kernel
theorem subd8_6_6 : subd8_6 [-1, 1] = true := by decide +kernel
theorem subd8_6_7 : subd8_6 [-1, 2] = true := by decide +kernel
theorem subd8_6_8 : subd8_6 [0, -3] = true := by decide +kernel
theorem subd8_6_9 : subd8_6 [0, -2] = true := by decide +kernel
theorem subd8_6_10 : subd8_6 [0, -1] = true := by decide +kernel
theorem subd8_6_11 : subd8_6 [0, 0] = true := by decide +kernel
theorem subd8_6_12 : subd8_6 [0, 1] = true := by decide +kernel
theorem subd8_6_13 : subd8_6 [0, 2] = true := by decide +kernel
theorem subd8_6_14 : subd8_6 [1, -3] = true := by decide +kernel
theorem subd8_6_15 : subd8_6 [1, -2] = true := by decide +kernel
theorem subd8_6_16 : subd8_6 [1, -1] = true := by decide +kernel
theorem subd8_6_17 : subd8_6 [1, 0] = true := by decide +kernel
theorem subd8_6_18 : subd8_6 [1, 1] = true := by decide +kernel
theorem subd8_6_19 : subd8_6 [1, 2] = true := by decide +kernel
theorem subd8_6_20 : subd8_6 [1, 3] = true := by decide +kernel
theorem subd8_6_21 : subd8_6 [2] = true := by decide +kernel
theorem sbd8_6_0 : ∀ q ∈ blkd8_6_0, subd8_6 q = true := by
  unfold blkd8_6_0
  exact List.forall_mem_cons.2 ⟨subd8_6_0, List.forall_mem_cons.2 ⟨subd8_6_1, List.forall_mem_cons.2 ⟨subd8_6_2, List.forall_mem_cons.2 ⟨subd8_6_3, List.forall_mem_cons.2 ⟨subd8_6_4, List.forall_mem_cons.2 ⟨subd8_6_5, List.forall_mem_cons.2 ⟨subd8_6_6, List.forall_mem_cons.2 ⟨subd8_6_7, List.forall_mem_cons.2 ⟨subd8_6_8, List.forall_mem_cons.2 ⟨subd8_6_9, List.forall_mem_cons.2 ⟨subd8_6_10, List.forall_mem_cons.2 ⟨subd8_6_11, List.forall_mem_cons.2 ⟨subd8_6_12, List.forall_mem_cons.2 ⟨subd8_6_13, List.forall_mem_cons.2 ⟨subd8_6_14, List.forall_mem_cons.2 ⟨subd8_6_15, List.forall_mem_cons.2 ⟨subd8_6_16, List.forall_mem_cons.2 ⟨subd8_6_17, List.forall_mem_cons.2 ⟨subd8_6_18, List.forall_mem_cons.2 ⟨subd8_6_19, List.forall_mem_cons.2 ⟨subd8_6_20, List.forall_mem_cons.2 ⟨subd8_6_21, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd8_7 : ldCheck G d8_7.U d8_7.ms ldd8_7 = true := by decide +kernel
theorem pre_okd8_7 : subPre G cell8 d8_7 = true := by decide +kernel
theorem subd8_7_0 : subd8_7 [-2] = true := by decide +kernel
theorem subd8_7_1 : subd8_7 [-1] = true := by decide +kernel
theorem subd8_7_2 : subd8_7 [0] = true := by decide +kernel
theorem subd8_7_3 : subd8_7 [1] = true := by decide +kernel
theorem subd8_7_4 : subd8_7 [2] = true := by decide +kernel
theorem sbd8_7_0 : ∀ q ∈ blkd8_7_0, subd8_7 q = true := by
  unfold blkd8_7_0
  exact List.forall_mem_cons.2 ⟨subd8_7_0, List.forall_mem_cons.2 ⟨subd8_7_1, List.forall_mem_cons.2 ⟨subd8_7_2, List.forall_mem_cons.2 ⟨subd8_7_3, List.forall_mem_cons.2 ⟨subd8_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C132
