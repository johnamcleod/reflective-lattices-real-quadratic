import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_3_0 : subd10_3 [-3] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-2, -3] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [-2, -2] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [-2, -1] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [-2, 0] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [-2, 1] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [-1, -3] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [-1, -2] = true := by decide +kernel
theorem subd10_3_8 : subd10_3 [-1, -1] = true := by decide +kernel
theorem subd10_3_9 : subd10_3 [-1, 0] = true := by decide +kernel
theorem subd10_3_10 : subd10_3 [-1, 1] = true := by decide +kernel
theorem subd10_3_11 : subd10_3 [-1, 2] = true := by decide +kernel
theorem subd10_3_12 : subd10_3 [0, -3] = true := by decide +kernel
theorem subd10_3_13 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_14 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_15 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_16 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_17 : subd10_3 [0, 2] = true := by decide +kernel
theorem subd10_3_18 : subd10_3 [1, -3] = true := by decide +kernel
theorem subd10_3_19 : subd10_3 [1, -2] = true := by decide +kernel
theorem subd10_3_20 : subd10_3 [1, -1] = true := by decide +kernel
theorem subd10_3_21 : subd10_3 [1, 0] = true := by decide +kernel
theorem subd10_3_22 : subd10_3 [1, 1] = true := by decide +kernel
theorem subd10_3_23 : subd10_3 [1, 2] = true := by decide +kernel
theorem subd10_3_24 : subd10_3 [2, -2] = true := by decide +kernel
theorem subd10_3_25 : subd10_3 [2, -1] = true := by decide +kernel
theorem subd10_3_26 : subd10_3 [2, 0] = true := by decide +kernel
theorem subd10_3_27 : subd10_3 [2, 1] = true := by decide +kernel
theorem subd10_3_28 : subd10_3 [2, 2] = true := by decide +kernel
theorem subd10_3_29 : subd10_3 [3] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_cons.2 ⟨subd10_3_8, List.forall_mem_cons.2 ⟨subd10_3_9, List.forall_mem_cons.2 ⟨subd10_3_10, List.forall_mem_cons.2 ⟨subd10_3_11, List.forall_mem_cons.2 ⟨subd10_3_12, List.forall_mem_cons.2 ⟨subd10_3_13, List.forall_mem_cons.2 ⟨subd10_3_14, List.forall_mem_cons.2 ⟨subd10_3_15, List.forall_mem_cons.2 ⟨subd10_3_16, List.forall_mem_cons.2 ⟨subd10_3_17, List.forall_mem_cons.2 ⟨subd10_3_18, List.forall_mem_cons.2 ⟨subd10_3_19, List.forall_mem_cons.2 ⟨subd10_3_20, List.forall_mem_cons.2 ⟨subd10_3_21, List.forall_mem_cons.2 ⟨subd10_3_22, List.forall_mem_cons.2 ⟨subd10_3_23, List.forall_mem_cons.2 ⟨subd10_3_24, List.forall_mem_cons.2 ⟨subd10_3_25, List.forall_mem_cons.2 ⟨subd10_3_26, List.forall_mem_cons.2 ⟨subd10_3_27, List.forall_mem_cons.2 ⟨subd10_3_28, List.forall_mem_cons.2 ⟨subd10_3_29, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_nil _⟩
theorem ld_okd10_5 : ldCheck G d10_5.U d10_5.ms ldd10_5 = true := by decide +kernel
theorem pre_okd10_5 : subPre G cell10 d10_5 = true := by decide +kernel
theorem subd10_5_0 : subd10_5 [-1] = true := by decide +kernel
theorem subd10_5_1 : subd10_5 [0] = true := by decide +kernel
theorem subd10_5_2 : subd10_5 [1] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_cons.2 ⟨subd10_5_1, List.forall_mem_cons.2 ⟨subd10_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd10_6 : ldCheck G d10_6.U d10_6.ms ldd10_6 = true := by decide +kernel
theorem pre_okd10_6 : subPre G cell10 d10_6 = true := by decide +kernel
theorem subd10_6_0 : subd10_6 [-3] = true := by decide +kernel
theorem subd10_6_1 : subd10_6 [-2, -4] = true := by decide +kernel
theorem subd10_6_2 : subd10_6 [-2, -3] = true := by decide +kernel
theorem subd10_6_3 : subd10_6 [-2, -2] = true := by decide +kernel
theorem subd10_6_4 : subd10_6 [-2, -1] = true := by decide +kernel
theorem subd10_6_5 : subd10_6 [-2, 0] = true := by decide +kernel
theorem subd10_6_6 : subd10_6 [-2, 1] = true := by decide +kernel
theorem subd10_6_7 : subd10_6 [-2, 2] = true := by decide +kernel
theorem subd10_6_8 : subd10_6 [-2, 3] = true := by decide +kernel
theorem subd10_6_9 : subd10_6 [-1, -4] = true := by decide +kernel
theorem subd10_6_10 : subd10_6 [-1, -3] = true := by decide +kernel
theorem subd10_6_11 : subd10_6 [-1, -2] = true := by decide +kernel
theorem subd10_6_12 : subd10_6 [-1, -1] = true := by decide +kernel
theorem subd10_6_13 : subd10_6 [-1, 0] = true := by decide +kernel
theorem subd10_6_14 : subd10_6 [-1, 1] = true := by decide +kernel
theorem subd10_6_15 : subd10_6 [-1, 2] = true := by decide +kernel
theorem subd10_6_16 : subd10_6 [-1, 3] = true := by decide +kernel
theorem subd10_6_17 : subd10_6 [0, -4] = true := by decide +kernel
theorem subd10_6_18 : subd10_6 [0, -3] = true := by decide +kernel
theorem subd10_6_19 : subd10_6 [0, -2] = true := by decide +kernel
theorem subd10_6_20 : subd10_6 [0, -1] = true := by decide +kernel
theorem subd10_6_21 : subd10_6 [0, 0] = true := by decide +kernel
theorem subd10_6_22 : subd10_6 [0, 1] = true := by decide +kernel
theorem subd10_6_23 : subd10_6 [0, 2] = true := by decide +kernel
theorem subd10_6_24 : subd10_6 [0, 3] = true := by decide +kernel
theorem subd10_6_25 : subd10_6 [1, -4] = true := by decide +kernel
theorem subd10_6_26 : subd10_6 [1, -3] = true := by decide +kernel
theorem subd10_6_27 : subd10_6 [1, -2] = true := by decide +kernel
theorem subd10_6_28 : subd10_6 [1, -1] = true := by decide +kernel
theorem subd10_6_29 : subd10_6 [1, 0] = true := by decide +kernel
theorem subd10_6_30 : subd10_6 [1, 1] = true := by decide +kernel
theorem subd10_6_31 : subd10_6 [1, 2] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_cons.2 ⟨subd10_6_1, List.forall_mem_cons.2 ⟨subd10_6_2, List.forall_mem_cons.2 ⟨subd10_6_3, List.forall_mem_cons.2 ⟨subd10_6_4, List.forall_mem_cons.2 ⟨subd10_6_5, List.forall_mem_cons.2 ⟨subd10_6_6, List.forall_mem_cons.2 ⟨subd10_6_7, List.forall_mem_cons.2 ⟨subd10_6_8, List.forall_mem_cons.2 ⟨subd10_6_9, List.forall_mem_cons.2 ⟨subd10_6_10, List.forall_mem_cons.2 ⟨subd10_6_11, List.forall_mem_cons.2 ⟨subd10_6_12, List.forall_mem_cons.2 ⟨subd10_6_13, List.forall_mem_cons.2 ⟨subd10_6_14, List.forall_mem_cons.2 ⟨subd10_6_15, List.forall_mem_cons.2 ⟨subd10_6_16, List.forall_mem_cons.2 ⟨subd10_6_17, List.forall_mem_cons.2 ⟨subd10_6_18, List.forall_mem_cons.2 ⟨subd10_6_19, List.forall_mem_cons.2 ⟨subd10_6_20, List.forall_mem_cons.2 ⟨subd10_6_21, List.forall_mem_cons.2 ⟨subd10_6_22, List.forall_mem_cons.2 ⟨subd10_6_23, List.forall_mem_cons.2 ⟨subd10_6_24, List.forall_mem_cons.2 ⟨subd10_6_25, List.forall_mem_cons.2 ⟨subd10_6_26, List.forall_mem_cons.2 ⟨subd10_6_27, List.forall_mem_cons.2 ⟨subd10_6_28, List.forall_mem_cons.2 ⟨subd10_6_29, List.forall_mem_cons.2 ⟨subd10_6_30, List.forall_mem_cons.2 ⟨subd10_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_32 : subd10_6 [1, 3] = true := by decide +kernel
theorem subd10_6_33 : subd10_6 [2, -4] = true := by decide +kernel
theorem subd10_6_34 : subd10_6 [2, -3] = true := by decide +kernel
theorem subd10_6_35 : subd10_6 [2, -2] = true := by decide +kernel
theorem subd10_6_36 : subd10_6 [2, -1] = true := by decide +kernel
theorem subd10_6_37 : subd10_6 [2, 0] = true := by decide +kernel
theorem subd10_6_38 : subd10_6 [2, 1] = true := by decide +kernel
theorem subd10_6_39 : subd10_6 [2, 2] = true := by decide +kernel
theorem subd10_6_40 : subd10_6 [2, 3] = true := by decide +kernel
theorem subd10_6_41 : subd10_6 [3] = true := by decide +kernel
theorem sbd10_6_1 : ∀ q ∈ blkd10_6_1, subd10_6 q = true := by
  unfold blkd10_6_1
  exact List.forall_mem_cons.2 ⟨subd10_6_32, List.forall_mem_cons.2 ⟨subd10_6_33, List.forall_mem_cons.2 ⟨subd10_6_34, List.forall_mem_cons.2 ⟨subd10_6_35, List.forall_mem_cons.2 ⟨subd10_6_36, List.forall_mem_cons.2 ⟨subd10_6_37, List.forall_mem_cons.2 ⟨subd10_6_38, List.forall_mem_cons.2 ⟨subd10_6_39, List.forall_mem_cons.2 ⟨subd10_6_40, List.forall_mem_cons.2 ⟨subd10_6_41, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_7 : ldCheck G d10_7.U d10_7.ms ldd10_7 = true := by decide +kernel
theorem pre_okd10_7 : subPre G cell10 d10_7 = true := by decide +kernel
theorem subd10_7_0 : subd10_7 [-1, -2] = true := by decide +kernel
theorem subd10_7_1 : subd10_7 [-1, -1] = true := by decide +kernel
theorem subd10_7_2 : subd10_7 [-1, 0] = true := by decide +kernel
theorem subd10_7_3 : subd10_7 [-1, 1] = true := by decide +kernel
theorem subd10_7_4 : subd10_7 [0, -2] = true := by decide +kernel
theorem subd10_7_5 : subd10_7 [0, -1] = true := by decide +kernel
theorem subd10_7_6 : subd10_7 [0, 0] = true := by decide +kernel
theorem subd10_7_7 : subd10_7 [0, 1] = true := by decide +kernel
theorem subd10_7_8 : subd10_7 [1, -2] = true := by decide +kernel
theorem subd10_7_9 : subd10_7 [1, -1] = true := by decide +kernel
theorem subd10_7_10 : subd10_7 [1, 0] = true := by decide +kernel
theorem subd10_7_11 : subd10_7 [1, 1] = true := by decide +kernel
theorem sbd10_7_0 : ∀ q ∈ blkd10_7_0, subd10_7 q = true := by
  unfold blkd10_7_0
  exact List.forall_mem_cons.2 ⟨subd10_7_0, List.forall_mem_cons.2 ⟨subd10_7_1, List.forall_mem_cons.2 ⟨subd10_7_2, List.forall_mem_cons.2 ⟨subd10_7_3, List.forall_mem_cons.2 ⟨subd10_7_4, List.forall_mem_cons.2 ⟨subd10_7_5, List.forall_mem_cons.2 ⟨subd10_7_6, List.forall_mem_cons.2 ⟨subd10_7_7, List.forall_mem_cons.2 ⟨subd10_7_8, List.forall_mem_cons.2 ⟨subd10_7_9, List.forall_mem_cons.2 ⟨subd10_7_10, List.forall_mem_cons.2 ⟨subd10_7_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C132
