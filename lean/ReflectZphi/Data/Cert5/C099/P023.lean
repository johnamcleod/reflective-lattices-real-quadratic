import ReflectZphi.Data.Cert5.C099.Base

namespace ReflectZphi.Data.Cert5.C099

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd9_5 : ldCheck G d9_5.U d9_5.ms ldd9_5 = true := by decide +kernel
theorem pre_okd9_5 : subPre G cell9 d9_5 = true := by decide +kernel
theorem subd9_5_0 : subd9_5 [-1] = true := by decide +kernel
theorem subd9_5_1 : subd9_5 [0, -2] = true := by decide +kernel
theorem subd9_5_2 : subd9_5 [0, -1] = true := by decide +kernel
theorem subd9_5_3 : subd9_5 [0, 0] = true := by decide +kernel
theorem subd9_5_4 : subd9_5 [0, 1] = true := by decide +kernel
theorem subd9_5_5 : subd9_5 [1] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_cons.2 ⟨subd9_5_1, List.forall_mem_cons.2 ⟨subd9_5_2, List.forall_mem_cons.2 ⟨subd9_5_3, List.forall_mem_cons.2 ⟨subd9_5_4, List.forall_mem_cons.2 ⟨subd9_5_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd9_6 : ldCheck G d9_6.U d9_6.ms ldd9_6 = true := by decide +kernel
theorem pre_okd9_6 : subPre G cell9 d9_6 = true := by decide +kernel
theorem subd9_6_0 : subd9_6 [-2, -2] = true := by decide +kernel
theorem subd9_6_1 : subd9_6 [-2, -1] = true := by decide +kernel
theorem subd9_6_2 : subd9_6 [-2, 0] = true := by decide +kernel
theorem subd9_6_3 : subd9_6 [-2, 1] = true := by decide +kernel
theorem subd9_6_4 : subd9_6 [-1, -3] = true := by decide +kernel
theorem subd9_6_5 : subd9_6 [-1, -2] = true := by decide +kernel
theorem subd9_6_6 : subd9_6 [-1, -1] = true := by decide +kernel
theorem subd9_6_7 : subd9_6 [-1, 0] = true := by decide +kernel
theorem subd9_6_8 : subd9_6 [-1, 1] = true := by decide +kernel
theorem subd9_6_9 : subd9_6 [-1, 2] = true := by decide +kernel
theorem subd9_6_10 : subd9_6 [0, -3] = true := by decide +kernel
theorem subd9_6_11 : subd9_6 [0, -2] = true := by decide +kernel
theorem subd9_6_12 : subd9_6 [0, -1] = true := by decide +kernel
theorem subd9_6_13 : subd9_6 [0, 0] = true := by decide +kernel
theorem subd9_6_14 : subd9_6 [0, 1] = true := by decide +kernel
theorem subd9_6_15 : subd9_6 [0, 2] = true := by decide +kernel
theorem subd9_6_16 : subd9_6 [1, -3] = true := by decide +kernel
theorem subd9_6_17 : subd9_6 [1, -2] = true := by decide +kernel
theorem subd9_6_18 : subd9_6 [1, -1] = true := by decide +kernel
theorem subd9_6_19 : subd9_6 [1, 0] = true := by decide +kernel
theorem subd9_6_20 : subd9_6 [1, 1] = true := by decide +kernel
theorem subd9_6_21 : subd9_6 [1, 2] = true := by decide +kernel
theorem subd9_6_22 : subd9_6 [2, -2] = true := by decide +kernel
theorem subd9_6_23 : subd9_6 [2, -1] = true := by decide +kernel
theorem subd9_6_24 : subd9_6 [2, 0] = true := by decide +kernel
theorem subd9_6_25 : subd9_6 [2, 1] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_cons.2 ⟨subd9_6_1, List.forall_mem_cons.2 ⟨subd9_6_2, List.forall_mem_cons.2 ⟨subd9_6_3, List.forall_mem_cons.2 ⟨subd9_6_4, List.forall_mem_cons.2 ⟨subd9_6_5, List.forall_mem_cons.2 ⟨subd9_6_6, List.forall_mem_cons.2 ⟨subd9_6_7, List.forall_mem_cons.2 ⟨subd9_6_8, List.forall_mem_cons.2 ⟨subd9_6_9, List.forall_mem_cons.2 ⟨subd9_6_10, List.forall_mem_cons.2 ⟨subd9_6_11, List.forall_mem_cons.2 ⟨subd9_6_12, List.forall_mem_cons.2 ⟨subd9_6_13, List.forall_mem_cons.2 ⟨subd9_6_14, List.forall_mem_cons.2 ⟨subd9_6_15, List.forall_mem_cons.2 ⟨subd9_6_16, List.forall_mem_cons.2 ⟨subd9_6_17, List.forall_mem_cons.2 ⟨subd9_6_18, List.forall_mem_cons.2 ⟨subd9_6_19, List.forall_mem_cons.2 ⟨subd9_6_20, List.forall_mem_cons.2 ⟨subd9_6_21, List.forall_mem_cons.2 ⟨subd9_6_22, List.forall_mem_cons.2 ⟨subd9_6_23, List.forall_mem_cons.2 ⟨subd9_6_24, List.forall_mem_cons.2 ⟨subd9_6_25, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_7 : ldCheck G d9_7.U d9_7.ms ldd9_7 = true := by decide +kernel
theorem pre_okd9_7 : subPre G cell9 d9_7 = true := by decide +kernel
theorem subd9_7_0 : subd9_7 [-3] = true := by decide +kernel
theorem subd9_7_1 : subd9_7 [-2, -4] = true := by decide +kernel
theorem subd9_7_2 : subd9_7 [-2, -3] = true := by decide +kernel
theorem subd9_7_3 : subd9_7 [-2, -2] = true := by decide +kernel
theorem subd9_7_4 : subd9_7 [-2, -1] = true := by decide +kernel
theorem subd9_7_5 : subd9_7 [-2, 0] = true := by decide +kernel
theorem subd9_7_6 : subd9_7 [-2, 1] = true := by decide +kernel
theorem subd9_7_7 : subd9_7 [-2, 2] = true := by decide +kernel
theorem subd9_7_8 : subd9_7 [-1, -4] = true := by decide +kernel
theorem subd9_7_9 : subd9_7 [-1, -3] = true := by decide +kernel
theorem subd9_7_10 : subd9_7 [-1, -2] = true := by decide +kernel
theorem subd9_7_11 : subd9_7 [-1, -1] = true := by decide +kernel
theorem subd9_7_12 : subd9_7 [-1, 0] = true := by decide +kernel
theorem subd9_7_13 : subd9_7 [-1, 1] = true := by decide +kernel
theorem subd9_7_14 : subd9_7 [-1, 2] = true := by decide +kernel
theorem subd9_7_15 : subd9_7 [-1, 3] = true := by decide +kernel
theorem subd9_7_16 : subd9_7 [0, -4] = true := by decide +kernel
theorem subd9_7_17 : subd9_7 [0, -3] = true := by decide +kernel
theorem subd9_7_18 : subd9_7 [0, -2] = true := by decide +kernel
theorem subd9_7_19 : subd9_7 [0, -1] = true := by decide +kernel
theorem subd9_7_20 : subd9_7 [0, 0] = true := by decide +kernel
theorem subd9_7_21 : subd9_7 [0, 1] = true := by decide +kernel
theorem subd9_7_22 : subd9_7 [0, 2] = true := by decide +kernel
theorem subd9_7_23 : subd9_7 [0, 3] = true := by decide +kernel
theorem subd9_7_24 : subd9_7 [1, -4] = true := by decide +kernel
theorem subd9_7_25 : subd9_7 [1, -3] = true := by decide +kernel
theorem subd9_7_26 : subd9_7 [1, -2] = true := by decide +kernel
theorem subd9_7_27 : subd9_7 [1, -1] = true := by decide +kernel
theorem subd9_7_28 : subd9_7 [1, 0] = true := by decide +kernel
theorem subd9_7_29 : subd9_7 [1, 1] = true := by decide +kernel
theorem subd9_7_30 : subd9_7 [1, 2] = true := by decide +kernel
theorem subd9_7_31 : subd9_7 [1, 3] = true := by decide +kernel
theorem sbd9_7_0 : ∀ q ∈ blkd9_7_0, subd9_7 q = true := by
  unfold blkd9_7_0
  exact List.forall_mem_cons.2 ⟨subd9_7_0, List.forall_mem_cons.2 ⟨subd9_7_1, List.forall_mem_cons.2 ⟨subd9_7_2, List.forall_mem_cons.2 ⟨subd9_7_3, List.forall_mem_cons.2 ⟨subd9_7_4, List.forall_mem_cons.2 ⟨subd9_7_5, List.forall_mem_cons.2 ⟨subd9_7_6, List.forall_mem_cons.2 ⟨subd9_7_7, List.forall_mem_cons.2 ⟨subd9_7_8, List.forall_mem_cons.2 ⟨subd9_7_9, List.forall_mem_cons.2 ⟨subd9_7_10, List.forall_mem_cons.2 ⟨subd9_7_11, List.forall_mem_cons.2 ⟨subd9_7_12, List.forall_mem_cons.2 ⟨subd9_7_13, List.forall_mem_cons.2 ⟨subd9_7_14, List.forall_mem_cons.2 ⟨subd9_7_15, List.forall_mem_cons.2 ⟨subd9_7_16, List.forall_mem_cons.2 ⟨subd9_7_17, List.forall_mem_cons.2 ⟨subd9_7_18, List.forall_mem_cons.2 ⟨subd9_7_19, List.forall_mem_cons.2 ⟨subd9_7_20, List.forall_mem_cons.2 ⟨subd9_7_21, List.forall_mem_cons.2 ⟨subd9_7_22, List.forall_mem_cons.2 ⟨subd9_7_23, List.forall_mem_cons.2 ⟨subd9_7_24, List.forall_mem_cons.2 ⟨subd9_7_25, List.forall_mem_cons.2 ⟨subd9_7_26, List.forall_mem_cons.2 ⟨subd9_7_27, List.forall_mem_cons.2 ⟨subd9_7_28, List.forall_mem_cons.2 ⟨subd9_7_29, List.forall_mem_cons.2 ⟨subd9_7_30, List.forall_mem_cons.2 ⟨subd9_7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_7_32 : subd9_7 [2, -3] = true := by decide +kernel
theorem subd9_7_33 : subd9_7 [2, -2] = true := by decide +kernel
theorem subd9_7_34 : subd9_7 [2, -1] = true := by decide +kernel
theorem subd9_7_35 : subd9_7 [2, 0] = true := by decide +kernel
theorem subd9_7_36 : subd9_7 [2, 1] = true := by decide +kernel
theorem subd9_7_37 : subd9_7 [2, 2] = true := by decide +kernel
theorem subd9_7_38 : subd9_7 [2, 3] = true := by decide +kernel
theorem subd9_7_39 : subd9_7 [3] = true := by decide +kernel
theorem sbd9_7_1 : ∀ q ∈ blkd9_7_1, subd9_7 q = true := by
  unfold blkd9_7_1
  exact List.forall_mem_cons.2 ⟨subd9_7_32, List.forall_mem_cons.2 ⟨subd9_7_33, List.forall_mem_cons.2 ⟨subd9_7_34, List.forall_mem_cons.2 ⟨subd9_7_35, List.forall_mem_cons.2 ⟨subd9_7_36, List.forall_mem_cons.2 ⟨subd9_7_37, List.forall_mem_cons.2 ⟨subd9_7_38, List.forall_mem_cons.2 ⟨subd9_7_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_nil _⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C099
