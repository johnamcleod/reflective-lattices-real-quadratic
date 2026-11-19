import ReflectZphi.Data.Cert5.C123.Base

namespace ReflectZphi.Data.Cert5.C123

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_nil _⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [-3] = true := by decide +kernel
theorem subd10_4_1 : subd10_4 [-2] = true := by decide +kernel
theorem subd10_4_2 : subd10_4 [-1, -4] = true := by decide +kernel
theorem subd10_4_3 : subd10_4 [-1, -3] = true := by decide +kernel
theorem subd10_4_4 : subd10_4 [-1, -2] = true := by decide +kernel
theorem subd10_4_5 : subd10_4 [-1, -1] = true := by decide +kernel
theorem subd10_4_6 : subd10_4 [-1, 0] = true := by decide +kernel
theorem subd10_4_7 : subd10_4 [-1, 1] = true := by decide +kernel
theorem subd10_4_8 : subd10_4 [-1, 2] = true := by decide +kernel
theorem subd10_4_9 : subd10_4 [-1, 3] = true := by decide +kernel
theorem subd10_4_10 : subd10_4 [0, -4] = true := by decide +kernel
theorem subd10_4_11 : subd10_4 [0, -3] = true := by decide +kernel
theorem subd10_4_12 : subd10_4 [0, -2] = true := by decide +kernel
theorem subd10_4_13 : subd10_4 [0, -1] = true := by decide +kernel
theorem subd10_4_14 : subd10_4 [0, 0] = true := by decide +kernel
theorem subd10_4_15 : subd10_4 [0, 1] = true := by decide +kernel
theorem subd10_4_16 : subd10_4 [0, 2] = true := by decide +kernel
theorem subd10_4_17 : subd10_4 [0, 3] = true := by decide +kernel
theorem subd10_4_18 : subd10_4 [1, -4] = true := by decide +kernel
theorem subd10_4_19 : subd10_4 [1, -3] = true := by decide +kernel
theorem subd10_4_20 : subd10_4 [1, -2] = true := by decide +kernel
theorem subd10_4_21 : subd10_4 [1, -1] = true := by decide +kernel
theorem subd10_4_22 : subd10_4 [1, 0] = true := by decide +kernel
theorem subd10_4_23 : subd10_4 [1, 1] = true := by decide +kernel
theorem subd10_4_24 : subd10_4 [1, 2] = true := by decide +kernel
theorem subd10_4_25 : subd10_4 [1, 3] = true := by decide +kernel
theorem subd10_4_26 : subd10_4 [2] = true := by decide +kernel
theorem subd10_4_27 : subd10_4 [3] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_cons.2 ⟨subd10_4_1, List.forall_mem_cons.2 ⟨subd10_4_2, List.forall_mem_cons.2 ⟨subd10_4_3, List.forall_mem_cons.2 ⟨subd10_4_4, List.forall_mem_cons.2 ⟨subd10_4_5, List.forall_mem_cons.2 ⟨subd10_4_6, List.forall_mem_cons.2 ⟨subd10_4_7, List.forall_mem_cons.2 ⟨subd10_4_8, List.forall_mem_cons.2 ⟨subd10_4_9, List.forall_mem_cons.2 ⟨subd10_4_10, List.forall_mem_cons.2 ⟨subd10_4_11, List.forall_mem_cons.2 ⟨subd10_4_12, List.forall_mem_cons.2 ⟨subd10_4_13, List.forall_mem_cons.2 ⟨subd10_4_14, List.forall_mem_cons.2 ⟨subd10_4_15, List.forall_mem_cons.2 ⟨subd10_4_16, List.forall_mem_cons.2 ⟨subd10_4_17, List.forall_mem_cons.2 ⟨subd10_4_18, List.forall_mem_cons.2 ⟨subd10_4_19, List.forall_mem_cons.2 ⟨subd10_4_20, List.forall_mem_cons.2 ⟨subd10_4_21, List.forall_mem_cons.2 ⟨subd10_4_22, List.forall_mem_cons.2 ⟨subd10_4_23, List.forall_mem_cons.2 ⟨subd10_4_24, List.forall_mem_cons.2 ⟨subd10_4_25, List.forall_mem_cons.2 ⟨subd10_4_26, List.forall_mem_cons.2 ⟨subd10_4_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_5 : ldCheck G d10_5.U d10_5.ms ldd10_5 = true := by decide +kernel
theorem pre_okd10_5 : subPre G cell10 d10_5 = true := by decide +kernel
theorem subd10_5_0 : subd10_5 [-1] = true := by decide +kernel
theorem subd10_5_1 : subd10_5 [0, -3] = true := by decide +kernel
theorem subd10_5_2 : subd10_5 [0, -2] = true := by decide +kernel
theorem subd10_5_3 : subd10_5 [0, -1] = true := by decide +kernel
theorem subd10_5_4 : subd10_5 [0, 0] = true := by decide +kernel
theorem subd10_5_5 : subd10_5 [0, 1] = true := by decide +kernel
theorem subd10_5_6 : subd10_5 [0, 2] = true := by decide +kernel
theorem subd10_5_7 : subd10_5 [1] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_cons.2 ⟨subd10_5_1, List.forall_mem_cons.2 ⟨subd10_5_2, List.forall_mem_cons.2 ⟨subd10_5_3, List.forall_mem_cons.2 ⟨subd10_5_4, List.forall_mem_cons.2 ⟨subd10_5_5, List.forall_mem_cons.2 ⟨subd10_5_6, List.forall_mem_cons.2 ⟨subd10_5_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_6 : ldCheck G d10_6.U d10_6.ms ldd10_6 = true := by decide +kernel
theorem pre_okd10_6 : subPre G cell10 d10_6 = true := by decide +kernel
theorem subd10_6_0 : subd10_6 [-3] = true := by decide +kernel
theorem subd10_6_1 : subd10_6 [-2, -3] = true := by decide +kernel
theorem subd10_6_2 : subd10_6 [-2, -2] = true := by decide +kernel
theorem subd10_6_3 : subd10_6 [-2, -1] = true := by decide +kernel
theorem subd10_6_4 : subd10_6 [-2, 0] = true := by decide +kernel
theorem subd10_6_5 : subd10_6 [-2, 1] = true := by decide +kernel
theorem subd10_6_6 : subd10_6 [-2, 2] = true := by decide +kernel
theorem subd10_6_7 : subd10_6 [-2, 3] = true := by decide +kernel
theorem subd10_6_8 : subd10_6 [-1, -4] = true := by decide +kernel
theorem subd10_6_9 : subd10_6 [-1, -3] = true := by decide +kernel
theorem subd10_6_10 : subd10_6 [-1, -2] = true := by decide +kernel
theorem subd10_6_11 : subd10_6 [-1, -1] = true := by decide +kernel
theorem subd10_6_12 : subd10_6 [-1, 0] = true := by decide +kernel
theorem subd10_6_13 : subd10_6 [-1, 1] = true := by decide +kernel
theorem subd10_6_14 : subd10_6 [-1, 2] = true := by decide +kernel
theorem subd10_6_15 : subd10_6 [-1, 3] = true := by decide +kernel
theorem subd10_6_16 : subd10_6 [0, -4] = true := by decide +kernel
theorem subd10_6_17 : subd10_6 [0, -3] = true := by decide +kernel
theorem subd10_6_18 : subd10_6 [0, -2] = true := by decide +kernel
theorem subd10_6_19 : subd10_6 [0, -1] = true := by decide +kernel
theorem subd10_6_20 : subd10_6 [0, 0] = true := by decide +kernel
theorem subd10_6_21 : subd10_6 [0, 1] = true := by decide +kernel
theorem subd10_6_22 : subd10_6 [0, 2] = true := by decide +kernel
theorem subd10_6_23 : subd10_6 [0, 3] = true := by decide +kernel
theorem subd10_6_24 : subd10_6 [1, -4] = true := by decide +kernel
theorem subd10_6_25 : subd10_6 [1, -3] = true := by decide +kernel
theorem subd10_6_26 : subd10_6 [1, -2] = true := by decide +kernel
theorem subd10_6_27 : subd10_6 [1, -1] = true := by decide +kernel
theorem subd10_6_28 : subd10_6 [1, 0] = true := by decide +kernel
theorem subd10_6_29 : subd10_6 [1, 1] = true := by decide +kernel
theorem subd10_6_30 : subd10_6 [1, 2] = true := by decide +kernel
theorem subd10_6_31 : subd10_6 [1, 3] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_cons.2 ⟨subd10_6_1, List.forall_mem_cons.2 ⟨subd10_6_2, List.forall_mem_cons.2 ⟨subd10_6_3, List.forall_mem_cons.2 ⟨subd10_6_4, List.forall_mem_cons.2 ⟨subd10_6_5, List.forall_mem_cons.2 ⟨subd10_6_6, List.forall_mem_cons.2 ⟨subd10_6_7, List.forall_mem_cons.2 ⟨subd10_6_8, List.forall_mem_cons.2 ⟨subd10_6_9, List.forall_mem_cons.2 ⟨subd10_6_10, List.forall_mem_cons.2 ⟨subd10_6_11, List.forall_mem_cons.2 ⟨subd10_6_12, List.forall_mem_cons.2 ⟨subd10_6_13, List.forall_mem_cons.2 ⟨subd10_6_14, List.forall_mem_cons.2 ⟨subd10_6_15, List.forall_mem_cons.2 ⟨subd10_6_16, List.forall_mem_cons.2 ⟨subd10_6_17, List.forall_mem_cons.2 ⟨subd10_6_18, List.forall_mem_cons.2 ⟨subd10_6_19, List.forall_mem_cons.2 ⟨subd10_6_20, List.forall_mem_cons.2 ⟨subd10_6_21, List.forall_mem_cons.2 ⟨subd10_6_22, List.forall_mem_cons.2 ⟨subd10_6_23, List.forall_mem_cons.2 ⟨subd10_6_24, List.forall_mem_cons.2 ⟨subd10_6_25, List.forall_mem_cons.2 ⟨subd10_6_26, List.forall_mem_cons.2 ⟨subd10_6_27, List.forall_mem_cons.2 ⟨subd10_6_28, List.forall_mem_cons.2 ⟨subd10_6_29, List.forall_mem_cons.2 ⟨subd10_6_30, List.forall_mem_cons.2 ⟨subd10_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_32 : subd10_6 [2, -4] = true := by decide +kernel
theorem subd10_6_33 : subd10_6 [2, -3] = true := by decide +kernel
theorem subd10_6_34 : subd10_6 [2, -2] = true := by decide +kernel
theorem subd10_6_35 : subd10_6 [2, -1] = true := by decide +kernel
theorem subd10_6_36 : subd10_6 [2, 0] = true := by decide +kernel
theorem subd10_6_37 : subd10_6 [2, 1] = true := by decide +kernel
theorem subd10_6_38 : subd10_6 [2, 2] = true := by decide +kernel
theorem subd10_6_39 : subd10_6 [3] = true := by decide +kernel
theorem sbd10_6_1 : ∀ q ∈ blkd10_6_1, subd10_6 q = true := by
  unfold blkd10_6_1
  exact List.forall_mem_cons.2 ⟨subd10_6_32, List.forall_mem_cons.2 ⟨subd10_6_33, List.forall_mem_cons.2 ⟨subd10_6_34, List.forall_mem_cons.2 ⟨subd10_6_35, List.forall_mem_cons.2 ⟨subd10_6_36, List.forall_mem_cons.2 ⟨subd10_6_37, List.forall_mem_cons.2 ⟨subd10_6_38, List.forall_mem_cons.2 ⟨subd10_6_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_nil _⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C123
