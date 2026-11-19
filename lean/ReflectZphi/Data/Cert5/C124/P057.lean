import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_11 : ldCheck G d10_11.U d10_11.ms ldd10_11 = true := by decide +kernel
theorem pre_okd10_11 : subPre G cell10 d10_11 = true := by decide +kernel
theorem subd10_11_0 : subd10_11 [-3] = true := by decide +kernel
theorem subd10_11_1 : subd10_11 [-2] = true := by decide +kernel
theorem subd10_11_2 : subd10_11 [-1, -4] = true := by decide +kernel
theorem subd10_11_3 : subd10_11 [-1, -3] = true := by decide +kernel
theorem subd10_11_4 : subd10_11 [-1, -2] = true := by decide +kernel
theorem subd10_11_5 : subd10_11 [-1, -1] = true := by decide +kernel
theorem subd10_11_6 : subd10_11 [-1, 0] = true := by decide +kernel
theorem subd10_11_7 : subd10_11 [-1, 1] = true := by decide +kernel
theorem subd10_11_8 : subd10_11 [-1, 2] = true := by decide +kernel
theorem subd10_11_9 : subd10_11 [-1, 3] = true := by decide +kernel
theorem subd10_11_10 : subd10_11 [0, -4] = true := by decide +kernel
theorem subd10_11_11 : subd10_11 [0, -3] = true := by decide +kernel
theorem subd10_11_12 : subd10_11 [0, -2] = true := by decide +kernel
theorem subd10_11_13 : subd10_11 [0, -1] = true := by decide +kernel
theorem subd10_11_14 : subd10_11 [0, 0] = true := by decide +kernel
theorem subd10_11_15 : subd10_11 [0, 1] = true := by decide +kernel
theorem subd10_11_16 : subd10_11 [0, 2] = true := by decide +kernel
theorem subd10_11_17 : subd10_11 [0, 3] = true := by decide +kernel
theorem subd10_11_18 : subd10_11 [1, -4] = true := by decide +kernel
theorem subd10_11_19 : subd10_11 [1, -3] = true := by decide +kernel
theorem subd10_11_20 : subd10_11 [1, -2] = true := by decide +kernel
theorem subd10_11_21 : subd10_11 [1, -1] = true := by decide +kernel
theorem subd10_11_22 : subd10_11 [1, 0] = true := by decide +kernel
theorem subd10_11_23 : subd10_11 [1, 1] = true := by decide +kernel
theorem subd10_11_24 : subd10_11 [1, 2] = true := by decide +kernel
theorem subd10_11_25 : subd10_11 [1, 3] = true := by decide +kernel
theorem subd10_11_26 : subd10_11 [2] = true := by decide +kernel
theorem subd10_11_27 : subd10_11 [3] = true := by decide +kernel
theorem sbd10_11_0 : ∀ q ∈ blkd10_11_0, subd10_11 q = true := by
  unfold blkd10_11_0
  exact List.forall_mem_cons.2 ⟨subd10_11_0, List.forall_mem_cons.2 ⟨subd10_11_1, List.forall_mem_cons.2 ⟨subd10_11_2, List.forall_mem_cons.2 ⟨subd10_11_3, List.forall_mem_cons.2 ⟨subd10_11_4, List.forall_mem_cons.2 ⟨subd10_11_5, List.forall_mem_cons.2 ⟨subd10_11_6, List.forall_mem_cons.2 ⟨subd10_11_7, List.forall_mem_cons.2 ⟨subd10_11_8, List.forall_mem_cons.2 ⟨subd10_11_9, List.forall_mem_cons.2 ⟨subd10_11_10, List.forall_mem_cons.2 ⟨subd10_11_11, List.forall_mem_cons.2 ⟨subd10_11_12, List.forall_mem_cons.2 ⟨subd10_11_13, List.forall_mem_cons.2 ⟨subd10_11_14, List.forall_mem_cons.2 ⟨subd10_11_15, List.forall_mem_cons.2 ⟨subd10_11_16, List.forall_mem_cons.2 ⟨subd10_11_17, List.forall_mem_cons.2 ⟨subd10_11_18, List.forall_mem_cons.2 ⟨subd10_11_19, List.forall_mem_cons.2 ⟨subd10_11_20, List.forall_mem_cons.2 ⟨subd10_11_21, List.forall_mem_cons.2 ⟨subd10_11_22, List.forall_mem_cons.2 ⟨subd10_11_23, List.forall_mem_cons.2 ⟨subd10_11_24, List.forall_mem_cons.2 ⟨subd10_11_25, List.forall_mem_cons.2 ⟨subd10_11_26, List.forall_mem_cons.2 ⟨subd10_11_27, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_12 : ldCheck G d10_12.U d10_12.ms ldd10_12 = true := by decide +kernel
theorem pre_okd10_12 : subPre G cell10 d10_12 = true := by decide +kernel
theorem subd10_12_0 : subd10_12 [-2] = true := by decide +kernel
theorem subd10_12_1 : subd10_12 [-1] = true := by decide +kernel
theorem subd10_12_2 : subd10_12 [0] = true := by decide +kernel
theorem subd10_12_3 : subd10_12 [1] = true := by decide +kernel
theorem subd10_12_4 : subd10_12 [2] = true := by decide +kernel
theorem sbd10_12_0 : ∀ q ∈ blkd10_12_0, subd10_12 q = true := by
  unfold blkd10_12_0
  exact List.forall_mem_cons.2 ⟨subd10_12_0, List.forall_mem_cons.2 ⟨subd10_12_1, List.forall_mem_cons.2 ⟨subd10_12_2, List.forall_mem_cons.2 ⟨subd10_12_3, List.forall_mem_cons.2 ⟨subd10_12_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd10_13 : ldCheck G d10_13.U d10_13.ms ldd10_13 = true := by decide +kernel
theorem pre_okd10_13 : subPre G cell10 d10_13 = true := by decide +kernel
theorem subd10_13_0 : subd10_13 [-2] = true := by decide +kernel
theorem subd10_13_1 : subd10_13 [-1] = true := by decide +kernel
theorem subd10_13_2 : subd10_13 [0] = true := by decide +kernel
theorem subd10_13_3 : subd10_13 [1] = true := by decide +kernel
theorem subd10_13_4 : subd10_13 [2] = true := by decide +kernel
theorem sbd10_13_0 : ∀ q ∈ blkd10_13_0, subd10_13 q = true := by
  unfold blkd10_13_0
  exact List.forall_mem_cons.2 ⟨subd10_13_0, List.forall_mem_cons.2 ⟨subd10_13_1, List.forall_mem_cons.2 ⟨subd10_13_2, List.forall_mem_cons.2 ⟨subd10_13_3, List.forall_mem_cons.2 ⟨subd10_13_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd10_14 : ldCheck G d10_14.U d10_14.ms ldd10_14 = true := by decide +kernel
theorem pre_okd10_14 : subPre G cell10 d10_14 = true := by decide +kernel
theorem subd10_14_0 : subd10_14 [-4] = true := by decide +kernel
theorem subd10_14_1 : subd10_14 [-3] = true := by decide +kernel
theorem subd10_14_2 : subd10_14 [-2, -5] = true := by decide +kernel
theorem subd10_14_3 : subd10_14 [-2, -4] = true := by decide +kernel
theorem subd10_14_4 : subd10_14 [-2, -3] = true := by decide +kernel
theorem subd10_14_5 : subd10_14 [-2, -2] = true := by decide +kernel
theorem subd10_14_6 : subd10_14 [-2, -1] = true := by decide +kernel
theorem subd10_14_7 : subd10_14 [-2, 0] = true := by decide +kernel
theorem subd10_14_8 : subd10_14 [-2, 1] = true := by decide +kernel
theorem subd10_14_9 : subd10_14 [-2, 2] = true := by decide +kernel
theorem subd10_14_10 : subd10_14 [-1, -5] = true := by decide +kernel
theorem subd10_14_11 : subd10_14 [-1, -4] = true := by decide +kernel
theorem subd10_14_12 : subd10_14 [-1, -3] = true := by decide +kernel
theorem subd10_14_13 : subd10_14 [-1, -2] = true := by decide +kernel
theorem subd10_14_14 : subd10_14 [-1, -1] = true := by decide +kernel
theorem subd10_14_15 : subd10_14 [-1, 0] = true := by decide +kernel
theorem subd10_14_16 : subd10_14 [-1, 1] = true := by decide +kernel
theorem subd10_14_17 : subd10_14 [-1, 2] = true := by decide +kernel
theorem subd10_14_18 : subd10_14 [-1, 3] = true := by decide +kernel
theorem subd10_14_19 : subd10_14 [0, -5] = true := by decide +kernel
theorem subd10_14_20 : subd10_14 [0, -4] = true := by decide +kernel
theorem subd10_14_21 : subd10_14 [0, -3] = true := by decide +kernel
theorem subd10_14_22 : subd10_14 [0, -2] = true := by decide +kernel
theorem subd10_14_23 : subd10_14 [0, -1] = true := by decide +kernel
theorem subd10_14_24 : subd10_14 [0, 0] = true := by decide +kernel
theorem subd10_14_25 : subd10_14 [0, 1] = true := by decide +kernel
theorem subd10_14_26 : subd10_14 [0, 2] = true := by decide +kernel
theorem subd10_14_27 : subd10_14 [0, 3] = true := by decide +kernel
theorem subd10_14_28 : subd10_14 [0, 4] = true := by decide +kernel
theorem subd10_14_29 : subd10_14 [1, -4] = true := by decide +kernel
theorem subd10_14_30 : subd10_14 [1, -3] = true := by decide +kernel
theorem subd10_14_31 : subd10_14 [1, -2] = true := by decide +kernel
theorem sbd10_14_0 : ∀ q ∈ blkd10_14_0, subd10_14 q = true := by
  unfold blkd10_14_0
  exact List.forall_mem_cons.2 ⟨subd10_14_0, List.forall_mem_cons.2 ⟨subd10_14_1, List.forall_mem_cons.2 ⟨subd10_14_2, List.forall_mem_cons.2 ⟨subd10_14_3, List.forall_mem_cons.2 ⟨subd10_14_4, List.forall_mem_cons.2 ⟨subd10_14_5, List.forall_mem_cons.2 ⟨subd10_14_6, List.forall_mem_cons.2 ⟨subd10_14_7, List.forall_mem_cons.2 ⟨subd10_14_8, List.forall_mem_cons.2 ⟨subd10_14_9, List.forall_mem_cons.2 ⟨subd10_14_10, List.forall_mem_cons.2 ⟨subd10_14_11, List.forall_mem_cons.2 ⟨subd10_14_12, List.forall_mem_cons.2 ⟨subd10_14_13, List.forall_mem_cons.2 ⟨subd10_14_14, List.forall_mem_cons.2 ⟨subd10_14_15, List.forall_mem_cons.2 ⟨subd10_14_16, List.forall_mem_cons.2 ⟨subd10_14_17, List.forall_mem_cons.2 ⟨subd10_14_18, List.forall_mem_cons.2 ⟨subd10_14_19, List.forall_mem_cons.2 ⟨subd10_14_20, List.forall_mem_cons.2 ⟨subd10_14_21, List.forall_mem_cons.2 ⟨subd10_14_22, List.forall_mem_cons.2 ⟨subd10_14_23, List.forall_mem_cons.2 ⟨subd10_14_24, List.forall_mem_cons.2 ⟨subd10_14_25, List.forall_mem_cons.2 ⟨subd10_14_26, List.forall_mem_cons.2 ⟨subd10_14_27, List.forall_mem_cons.2 ⟨subd10_14_28, List.forall_mem_cons.2 ⟨subd10_14_29, List.forall_mem_cons.2 ⟨subd10_14_30, List.forall_mem_cons.2 ⟨subd10_14_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_14_32 : subd10_14 [1, -1] = true := by decide +kernel
theorem subd10_14_33 : subd10_14 [1, 0] = true := by decide +kernel
theorem subd10_14_34 : subd10_14 [1, 1] = true := by decide +kernel
theorem subd10_14_35 : subd10_14 [1, 2] = true := by decide +kernel
theorem subd10_14_36 : subd10_14 [1, 3] = true := by decide +kernel
theorem subd10_14_37 : subd10_14 [1, 4] = true := by decide +kernel
theorem subd10_14_38 : subd10_14 [2, -3] = true := by decide +kernel
theorem subd10_14_39 : subd10_14 [2, -2] = true := by decide +kernel
theorem subd10_14_40 : subd10_14 [2, -1] = true := by decide +kernel
theorem subd10_14_41 : subd10_14 [2, 0] = true := by decide +kernel
theorem subd10_14_42 : subd10_14 [2, 1] = true := by decide +kernel
theorem subd10_14_43 : subd10_14 [2, 2] = true := by decide +kernel
theorem subd10_14_44 : subd10_14 [2, 3] = true := by decide +kernel
theorem subd10_14_45 : subd10_14 [2, 4] = true := by decide +kernel
theorem subd10_14_46 : subd10_14 [3] = true := by decide +kernel
theorem subd10_14_47 : subd10_14 [4] = true := by decide +kernel
theorem sbd10_14_1 : ∀ q ∈ blkd10_14_1, subd10_14 q = true := by
  unfold blkd10_14_1
  exact List.forall_mem_cons.2 ⟨subd10_14_32, List.forall_mem_cons.2 ⟨subd10_14_33, List.forall_mem_cons.2 ⟨subd10_14_34, List.forall_mem_cons.2 ⟨subd10_14_35, List.forall_mem_cons.2 ⟨subd10_14_36, List.forall_mem_cons.2 ⟨subd10_14_37, List.forall_mem_cons.2 ⟨subd10_14_38, List.forall_mem_cons.2 ⟨subd10_14_39, List.forall_mem_cons.2 ⟨subd10_14_40, List.forall_mem_cons.2 ⟨subd10_14_41, List.forall_mem_cons.2 ⟨subd10_14_42, List.forall_mem_cons.2 ⟨subd10_14_43, List.forall_mem_cons.2 ⟨subd10_14_44, List.forall_mem_cons.2 ⟨subd10_14_45, List.forall_mem_cons.2 ⟨subd10_14_46, List.forall_mem_cons.2 ⟨subd10_14_47, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C124
