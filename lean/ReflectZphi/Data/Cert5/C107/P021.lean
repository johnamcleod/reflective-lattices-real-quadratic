import ReflectZphi.Data.Cert5.C107.Base

namespace ReflectZphi.Data.Cert5.C107

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd10_6 : ldCheck G d10_6.U d10_6.ms ldd10_6 = true := by decide +kernel
theorem pre_okd10_6 : subPre G cell10 d10_6 = true := by decide +kernel
theorem subd10_6_0 : subd10_6 [-1, -1] = true := by decide +kernel
theorem subd10_6_1 : subd10_6 [-1, 0, -7] = true := by decide +kernel
theorem subd10_6_2 : subd10_6 [-1, 0, -6] = true := by decide +kernel
theorem subd10_6_3 : subd10_6 [-1, 0, -5] = true := by decide +kernel
theorem subd10_6_4 : subd10_6 [-1, 0, -4] = true := by decide +kernel
theorem subd10_6_5 : subd10_6 [-1, 0, -3] = true := by decide +kernel
theorem subd10_6_6 : subd10_6 [-1, 0, -2] = true := by decide +kernel
theorem subd10_6_7 : subd10_6 [-1, 0, -1] = true := by decide +kernel
theorem subd10_6_8 : subd10_6 [-1, 0, 0] = true := by decide +kernel
theorem subd10_6_9 : subd10_6 [-1, 0, 1] = true := by decide +kernel
theorem subd10_6_10 : subd10_6 [-1, 0, 2] = true := by decide +kernel
theorem subd10_6_11 : subd10_6 [-1, 0, 3] = true := by decide +kernel
theorem subd10_6_12 : subd10_6 [-1, 0, 4] = true := by decide +kernel
theorem subd10_6_13 : subd10_6 [-1, 0, 5] = true := by decide +kernel
theorem subd10_6_14 : subd10_6 [-1, 0, 6] = true := by decide +kernel
theorem subd10_6_15 : subd10_6 [-1, 1] = true := by decide +kernel
theorem subd10_6_16 : subd10_6 [0, -2] = true := by decide +kernel
theorem subd10_6_17 : subd10_6 [0, -1] = true := by decide +kernel
theorem subd10_6_18 : subd10_6 [0, 0, -9] = true := by decide +kernel
theorem subd10_6_19 : subd10_6 [0, 0, -8] = true := by decide +kernel
theorem subd10_6_20 : subd10_6 [0, 0, -7] = true := by decide +kernel
theorem subd10_6_21 : subd10_6 [0, 0, -6] = true := by decide +kernel
theorem subd10_6_22 : subd10_6 [0, 0, -5] = true := by decide +kernel
theorem subd10_6_23 : subd10_6 [0, 0, -4] = true := by decide +kernel
theorem subd10_6_24 : subd10_6 [0, 0, -3] = true := by decide +kernel
theorem subd10_6_25 : subd10_6 [0, 0, -2] = true := by decide +kernel
theorem subd10_6_26 : subd10_6 [0, 0, -1] = true := by decide +kernel
theorem subd10_6_27 : subd10_6 [0, 0, 0] = true := by decide +kernel
theorem subd10_6_28 : subd10_6 [0, 0, 1] = true := by decide +kernel
theorem subd10_6_29 : subd10_6 [0, 0, 2] = true := by decide +kernel
theorem subd10_6_30 : subd10_6 [0, 0, 3] = true := by decide +kernel
theorem subd10_6_31 : subd10_6 [0, 0, 4] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_cons.2 ⟨subd10_6_1, List.forall_mem_cons.2 ⟨subd10_6_2, List.forall_mem_cons.2 ⟨subd10_6_3, List.forall_mem_cons.2 ⟨subd10_6_4, List.forall_mem_cons.2 ⟨subd10_6_5, List.forall_mem_cons.2 ⟨subd10_6_6, List.forall_mem_cons.2 ⟨subd10_6_7, List.forall_mem_cons.2 ⟨subd10_6_8, List.forall_mem_cons.2 ⟨subd10_6_9, List.forall_mem_cons.2 ⟨subd10_6_10, List.forall_mem_cons.2 ⟨subd10_6_11, List.forall_mem_cons.2 ⟨subd10_6_12, List.forall_mem_cons.2 ⟨subd10_6_13, List.forall_mem_cons.2 ⟨subd10_6_14, List.forall_mem_cons.2 ⟨subd10_6_15, List.forall_mem_cons.2 ⟨subd10_6_16, List.forall_mem_cons.2 ⟨subd10_6_17, List.forall_mem_cons.2 ⟨subd10_6_18, List.forall_mem_cons.2 ⟨subd10_6_19, List.forall_mem_cons.2 ⟨subd10_6_20, List.forall_mem_cons.2 ⟨subd10_6_21, List.forall_mem_cons.2 ⟨subd10_6_22, List.forall_mem_cons.2 ⟨subd10_6_23, List.forall_mem_cons.2 ⟨subd10_6_24, List.forall_mem_cons.2 ⟨subd10_6_25, List.forall_mem_cons.2 ⟨subd10_6_26, List.forall_mem_cons.2 ⟨subd10_6_27, List.forall_mem_cons.2 ⟨subd10_6_28, List.forall_mem_cons.2 ⟨subd10_6_29, List.forall_mem_cons.2 ⟨subd10_6_30, List.forall_mem_cons.2 ⟨subd10_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_6_32 : subd10_6 [0, 0, 5] = true := by decide +kernel
theorem subd10_6_33 : subd10_6 [0, 0, 6] = true := by decide +kernel
theorem subd10_6_34 : subd10_6 [0, 0, 7] = true := by decide +kernel
theorem subd10_6_35 : subd10_6 [0, 0, 8] = true := by decide +kernel
theorem subd10_6_36 : subd10_6 [0, 1] = true := by decide +kernel
theorem subd10_6_37 : subd10_6 [1, -2] = true := by decide +kernel
theorem subd10_6_38 : subd10_6 [1, -1] = true := by decide +kernel
theorem subd10_6_39 : subd10_6 [1, 0, -7] = true := by decide +kernel
theorem subd10_6_40 : subd10_6 [1, 0, -6] = true := by decide +kernel
theorem subd10_6_41 : subd10_6 [1, 0, -5] = true := by decide +kernel
theorem subd10_6_42 : subd10_6 [1, 0, -4] = true := by decide +kernel
theorem subd10_6_43 : subd10_6 [1, 0, -3] = true := by decide +kernel
theorem subd10_6_44 : subd10_6 [1, 0, -2] = true := by decide +kernel
theorem subd10_6_45 : subd10_6 [1, 0, -1] = true := by decide +kernel
theorem subd10_6_46 : subd10_6 [1, 0, 0] = true := by decide +kernel
theorem subd10_6_47 : subd10_6 [1, 0, 1] = true := by decide +kernel
theorem subd10_6_48 : subd10_6 [1, 0, 2] = true := by decide +kernel
theorem subd10_6_49 : subd10_6 [1, 0, 3] = true := by decide +kernel
theorem subd10_6_50 : subd10_6 [1, 0, 4] = true := by decide +kernel
theorem subd10_6_51 : subd10_6 [1, 0, 5] = true := by decide +kernel
theorem subd10_6_52 : subd10_6 [1, 0, 6] = true := by decide +kernel
theorem sbd10_6_1 : ∀ q ∈ blkd10_6_1, subd10_6 q = true := by
  unfold blkd10_6_1
  exact List.forall_mem_cons.2 ⟨subd10_6_32, List.forall_mem_cons.2 ⟨subd10_6_33, List.forall_mem_cons.2 ⟨subd10_6_34, List.forall_mem_cons.2 ⟨subd10_6_35, List.forall_mem_cons.2 ⟨subd10_6_36, List.forall_mem_cons.2 ⟨subd10_6_37, List.forall_mem_cons.2 ⟨subd10_6_38, List.forall_mem_cons.2 ⟨subd10_6_39, List.forall_mem_cons.2 ⟨subd10_6_40, List.forall_mem_cons.2 ⟨subd10_6_41, List.forall_mem_cons.2 ⟨subd10_6_42, List.forall_mem_cons.2 ⟨subd10_6_43, List.forall_mem_cons.2 ⟨subd10_6_44, List.forall_mem_cons.2 ⟨subd10_6_45, List.forall_mem_cons.2 ⟨subd10_6_46, List.forall_mem_cons.2 ⟨subd10_6_47, List.forall_mem_cons.2 ⟨subd10_6_48, List.forall_mem_cons.2 ⟨subd10_6_49, List.forall_mem_cons.2 ⟨subd10_6_50, List.forall_mem_cons.2 ⟨subd10_6_51, List.forall_mem_cons.2 ⟨subd10_6_52, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_7 : ldCheck G d10_7.U d10_7.ms ldd10_7 = true := by decide +kernel
theorem pre_okd10_7 : subPre G cell10 d10_7 = true := by decide +kernel
theorem subd10_7_0 : subd10_7 [-2] = true := by decide +kernel
theorem subd10_7_1 : subd10_7 [-1] = true := by decide +kernel
theorem subd10_7_2 : subd10_7 [0] = true := by decide +kernel
theorem subd10_7_3 : subd10_7 [1] = true := by decide +kernel
theorem subd10_7_4 : subd10_7 [2] = true := by decide +kernel
theorem sbd10_7_0 : ∀ q ∈ blkd10_7_0, subd10_7 q = true := by
  unfold blkd10_7_0
  exact List.forall_mem_cons.2 ⟨subd10_7_0, List.forall_mem_cons.2 ⟨subd10_7_1, List.forall_mem_cons.2 ⟨subd10_7_2, List.forall_mem_cons.2 ⟨subd10_7_3, List.forall_mem_cons.2 ⟨subd10_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-2] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-1] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [0] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [1] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [2] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [-2] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-1] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [0] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [1] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [2] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [-2] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-1] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [0] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [1] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [2] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [-2] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-1] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [0] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [1] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [2] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C107
