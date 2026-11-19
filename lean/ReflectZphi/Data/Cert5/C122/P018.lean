import ReflectZphi.Data.Cert5.C122.Base

namespace ReflectZphi.Data.Cert5.C122

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_2_0 : subd10_2 [-1] = true := by decide +kernel
theorem subd10_2_1 : subd10_2 [0] = true := by decide +kernel
theorem subd10_2_2 : subd10_2 [1] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_cons.2 ⟨subd10_2_1, List.forall_mem_cons.2 ⟨subd10_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [-2] = true := by decide +kernel
theorem subd10_3_1 : subd10_3 [-1] = true := by decide +kernel
theorem subd10_3_2 : subd10_3 [0, -2] = true := by decide +kernel
theorem subd10_3_3 : subd10_3 [0, -1] = true := by decide +kernel
theorem subd10_3_4 : subd10_3 [0, 0] = true := by decide +kernel
theorem subd10_3_5 : subd10_3 [0, 1] = true := by decide +kernel
theorem subd10_3_6 : subd10_3 [1] = true := by decide +kernel
theorem subd10_3_7 : subd10_3 [2] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_cons.2 ⟨subd10_3_1, List.forall_mem_cons.2 ⟨subd10_3_2, List.forall_mem_cons.2 ⟨subd10_3_3, List.forall_mem_cons.2 ⟨subd10_3_4, List.forall_mem_cons.2 ⟨subd10_3_5, List.forall_mem_cons.2 ⟨subd10_3_6, List.forall_mem_cons.2 ⟨subd10_3_7, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [-2, -2] = true := by decide +kernel
theorem subd10_4_1 : subd10_4 [-2, -1] = true := by decide +kernel
theorem subd10_4_2 : subd10_4 [-2, 0] = true := by decide +kernel
theorem subd10_4_3 : subd10_4 [-2, 1] = true := by decide +kernel
theorem subd10_4_4 : subd10_4 [-2, 2] = true := by decide +kernel
theorem subd10_4_5 : subd10_4 [-1, -3] = true := by decide +kernel
theorem subd10_4_6 : subd10_4 [-1, -2] = true := by decide +kernel
theorem subd10_4_7 : subd10_4 [-1, -1] = true := by decide +kernel
theorem subd10_4_8 : subd10_4 [-1, 0] = true := by decide +kernel
theorem subd10_4_9 : subd10_4 [-1, 1] = true := by decide +kernel
theorem subd10_4_10 : subd10_4 [-1, 2] = true := by decide +kernel
theorem subd10_4_11 : subd10_4 [-1, 3] = true := by decide +kernel
theorem subd10_4_12 : subd10_4 [0, -4] = true := by decide +kernel
theorem subd10_4_13 : subd10_4 [0, -3] = true := by decide +kernel
theorem subd10_4_14 : subd10_4 [0, -2] = true := by decide +kernel
theorem subd10_4_15 : subd10_4 [0, -1] = true := by decide +kernel
theorem subd10_4_16 : subd10_4 [0, 0] = true := by decide +kernel
theorem subd10_4_17 : subd10_4 [0, 1] = true := by decide +kernel
theorem subd10_4_18 : subd10_4 [0, 2] = true := by decide +kernel
theorem subd10_4_19 : subd10_4 [0, 3] = true := by decide +kernel
theorem subd10_4_20 : subd10_4 [1, -4] = true := by decide +kernel
theorem subd10_4_21 : subd10_4 [1, -3] = true := by decide +kernel
theorem subd10_4_22 : subd10_4 [1, -2] = true := by decide +kernel
theorem subd10_4_23 : subd10_4 [1, -1] = true := by decide +kernel
theorem subd10_4_24 : subd10_4 [1, 0] = true := by decide +kernel
theorem subd10_4_25 : subd10_4 [1, 1] = true := by decide +kernel
theorem subd10_4_26 : subd10_4 [1, 2] = true := by decide +kernel
theorem subd10_4_27 : subd10_4 [2, -3] = true := by decide +kernel
theorem subd10_4_28 : subd10_4 [2, -2] = true := by decide +kernel
theorem subd10_4_29 : subd10_4 [2, -1] = true := by decide +kernel
theorem subd10_4_30 : subd10_4 [2, 0] = true := by decide +kernel
theorem subd10_4_31 : subd10_4 [2, 1] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_cons.2 ⟨subd10_4_1, List.forall_mem_cons.2 ⟨subd10_4_2, List.forall_mem_cons.2 ⟨subd10_4_3, List.forall_mem_cons.2 ⟨subd10_4_4, List.forall_mem_cons.2 ⟨subd10_4_5, List.forall_mem_cons.2 ⟨subd10_4_6, List.forall_mem_cons.2 ⟨subd10_4_7, List.forall_mem_cons.2 ⟨subd10_4_8, List.forall_mem_cons.2 ⟨subd10_4_9, List.forall_mem_cons.2 ⟨subd10_4_10, List.forall_mem_cons.2 ⟨subd10_4_11, List.forall_mem_cons.2 ⟨subd10_4_12, List.forall_mem_cons.2 ⟨subd10_4_13, List.forall_mem_cons.2 ⟨subd10_4_14, List.forall_mem_cons.2 ⟨subd10_4_15, List.forall_mem_cons.2 ⟨subd10_4_16, List.forall_mem_cons.2 ⟨subd10_4_17, List.forall_mem_cons.2 ⟨subd10_4_18, List.forall_mem_cons.2 ⟨subd10_4_19, List.forall_mem_cons.2 ⟨subd10_4_20, List.forall_mem_cons.2 ⟨subd10_4_21, List.forall_mem_cons.2 ⟨subd10_4_22, List.forall_mem_cons.2 ⟨subd10_4_23, List.forall_mem_cons.2 ⟨subd10_4_24, List.forall_mem_cons.2 ⟨subd10_4_25, List.forall_mem_cons.2 ⟨subd10_4_26, List.forall_mem_cons.2 ⟨subd10_4_27, List.forall_mem_cons.2 ⟨subd10_4_28, List.forall_mem_cons.2 ⟨subd10_4_29, List.forall_mem_cons.2 ⟨subd10_4_30, List.forall_mem_cons.2 ⟨subd10_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_5 : ldCheck G d10_5.U d10_5.ms ldd10_5 = true := by decide +kernel
theorem pre_okd10_5 : subPre G cell10 d10_5 = true := by decide +kernel
theorem subd10_5_0 : subd10_5 [-2] = true := by decide +kernel
theorem subd10_5_1 : subd10_5 [-1] = true := by decide +kernel
theorem subd10_5_2 : subd10_5 [0] = true := by decide +kernel
theorem subd10_5_3 : subd10_5 [1] = true := by decide +kernel
theorem subd10_5_4 : subd10_5 [2] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_cons.2 ⟨subd10_5_1, List.forall_mem_cons.2 ⟨subd10_5_2, List.forall_mem_cons.2 ⟨subd10_5_3, List.forall_mem_cons.2 ⟨subd10_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd10_6 : ldCheck G d10_6.U d10_6.ms ldd10_6 = true := by decide +kernel
theorem pre_okd10_6 : subPre G cell10 d10_6 = true := by decide +kernel
theorem subd10_6_0 : subd10_6 [] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_nil _⟩
theorem ld_okd10_7 : ldCheck G d10_7.U d10_7.ms ldd10_7 = true := by decide +kernel
theorem pre_okd10_7 : subPre G cell10 d10_7 = true := by decide +kernel
theorem subd10_7_0 : subd10_7 [] = true := by decide +kernel
theorem sbd10_7_0 : ∀ q ∈ blkd10_7_0, subd10_7 q = true := by
  unfold blkd10_7_0
  exact List.forall_mem_cons.2 ⟨subd10_7_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C122
