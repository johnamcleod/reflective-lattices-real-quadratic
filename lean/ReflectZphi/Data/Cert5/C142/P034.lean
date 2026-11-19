import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd18_0 : ldCheck G d18_0.U d18_0.ms ldd18_0 = true := by decide +kernel
theorem pre_okd18_0 : subPre G cell18 d18_0 = true := by decide +kernel
theorem subd18_0_0 : subd18_0 [-1] = true := by decide +kernel
theorem subd18_0_1 : subd18_0 [0] = true := by decide +kernel
theorem subd18_0_2 : subd18_0 [1] = true := by decide +kernel
theorem sbd18_0_0 : ∀ q ∈ blkd18_0_0, subd18_0 q = true := by
  unfold blkd18_0_0
  exact List.forall_mem_cons.2 ⟨subd18_0_0, List.forall_mem_cons.2 ⟨subd18_0_1, List.forall_mem_cons.2 ⟨subd18_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd18_1 : ldCheck G d18_1.U d18_1.ms ldd18_1 = true := by decide +kernel
theorem pre_okd18_1 : subPre G cell18 d18_1 = true := by decide +kernel
theorem subd18_1_0 : subd18_1 [-1] = true := by decide +kernel
theorem subd18_1_1 : subd18_1 [0] = true := by decide +kernel
theorem subd18_1_2 : subd18_1 [1] = true := by decide +kernel
theorem sbd18_1_0 : ∀ q ∈ blkd18_1_0, subd18_1 q = true := by
  unfold blkd18_1_0
  exact List.forall_mem_cons.2 ⟨subd18_1_0, List.forall_mem_cons.2 ⟨subd18_1_1, List.forall_mem_cons.2 ⟨subd18_1_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd18_2 : ldCheck G d18_2.U d18_2.ms ldd18_2 = true := by decide +kernel
theorem pre_okd18_2 : subPre G cell18 d18_2 = true := by decide +kernel
theorem subd18_2_0 : subd18_2 [-4] = true := by decide +kernel
theorem subd18_2_1 : subd18_2 [-3] = true := by decide +kernel
theorem subd18_2_2 : subd18_2 [-2, -4] = true := by decide +kernel
theorem subd18_2_3 : subd18_2 [-2, -3] = true := by decide +kernel
theorem subd18_2_4 : subd18_2 [-2, -2] = true := by decide +kernel
theorem subd18_2_5 : subd18_2 [-2, -1] = true := by decide +kernel
theorem subd18_2_6 : subd18_2 [-2, 0] = true := by decide +kernel
theorem subd18_2_7 : subd18_2 [-2, 1] = true := by decide +kernel
theorem subd18_2_8 : subd18_2 [-2, 2] = true := by decide +kernel
theorem subd18_2_9 : subd18_2 [-2, 3] = true := by decide +kernel
theorem subd18_2_10 : subd18_2 [-2, 4] = true := by decide +kernel
theorem subd18_2_11 : subd18_2 [-1, -4] = true := by decide +kernel
theorem subd18_2_12 : subd18_2 [-1, -3] = true := by decide +kernel
theorem subd18_2_13 : subd18_2 [-1, -2] = true := by decide +kernel
theorem subd18_2_14 : subd18_2 [-1, -1] = true := by decide +kernel
theorem subd18_2_15 : subd18_2 [-1, 0] = true := by decide +kernel
theorem subd18_2_16 : subd18_2 [-1, 1] = true := by decide +kernel
theorem subd18_2_17 : subd18_2 [-1, 2] = true := by decide +kernel
theorem subd18_2_18 : subd18_2 [-1, 3] = true := by decide +kernel
theorem subd18_2_19 : subd18_2 [-1, 4] = true := by decide +kernel
theorem subd18_2_20 : subd18_2 [0, -5] = true := by decide +kernel
theorem subd18_2_21 : subd18_2 [0, -4] = true := by decide +kernel
theorem subd18_2_22 : subd18_2 [0, -3] = true := by decide +kernel
theorem subd18_2_23 : subd18_2 [0, -2] = true := by decide +kernel
theorem subd18_2_24 : subd18_2 [0, -1] = true := by decide +kernel
theorem subd18_2_25 : subd18_2 [0, 0] = true := by decide +kernel
theorem subd18_2_26 : subd18_2 [0, 1] = true := by decide +kernel
theorem subd18_2_27 : subd18_2 [0, 2] = true := by decide +kernel
theorem subd18_2_28 : subd18_2 [0, 3] = true := by decide +kernel
theorem subd18_2_29 : subd18_2 [0, 4] = true := by decide +kernel
theorem subd18_2_30 : subd18_2 [1, -5] = true := by decide +kernel
theorem subd18_2_31 : subd18_2 [1, -4] = true := by decide +kernel
theorem sbd18_2_0 : ∀ q ∈ blkd18_2_0, subd18_2 q = true := by
  unfold blkd18_2_0
  exact List.forall_mem_cons.2 ⟨subd18_2_0, List.forall_mem_cons.2 ⟨subd18_2_1, List.forall_mem_cons.2 ⟨subd18_2_2, List.forall_mem_cons.2 ⟨subd18_2_3, List.forall_mem_cons.2 ⟨subd18_2_4, List.forall_mem_cons.2 ⟨subd18_2_5, List.forall_mem_cons.2 ⟨subd18_2_6, List.forall_mem_cons.2 ⟨subd18_2_7, List.forall_mem_cons.2 ⟨subd18_2_8, List.forall_mem_cons.2 ⟨subd18_2_9, List.forall_mem_cons.2 ⟨subd18_2_10, List.forall_mem_cons.2 ⟨subd18_2_11, List.forall_mem_cons.2 ⟨subd18_2_12, List.forall_mem_cons.2 ⟨subd18_2_13, List.forall_mem_cons.2 ⟨subd18_2_14, List.forall_mem_cons.2 ⟨subd18_2_15, List.forall_mem_cons.2 ⟨subd18_2_16, List.forall_mem_cons.2 ⟨subd18_2_17, List.forall_mem_cons.2 ⟨subd18_2_18, List.forall_mem_cons.2 ⟨subd18_2_19, List.forall_mem_cons.2 ⟨subd18_2_20, List.forall_mem_cons.2 ⟨subd18_2_21, List.forall_mem_cons.2 ⟨subd18_2_22, List.forall_mem_cons.2 ⟨subd18_2_23, List.forall_mem_cons.2 ⟨subd18_2_24, List.forall_mem_cons.2 ⟨subd18_2_25, List.forall_mem_cons.2 ⟨subd18_2_26, List.forall_mem_cons.2 ⟨subd18_2_27, List.forall_mem_cons.2 ⟨subd18_2_28, List.forall_mem_cons.2 ⟨subd18_2_29, List.forall_mem_cons.2 ⟨subd18_2_30, List.forall_mem_cons.2 ⟨subd18_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd18_2_32 : subd18_2 [1, -3] = true := by decide +kernel
theorem subd18_2_33 : subd18_2 [1, -2] = true := by decide +kernel
theorem subd18_2_34 : subd18_2 [1, -1] = true := by decide +kernel
theorem subd18_2_35 : subd18_2 [1, 0] = true := by decide +kernel
theorem subd18_2_36 : subd18_2 [1, 1] = true := by decide +kernel
theorem subd18_2_37 : subd18_2 [1, 2] = true := by decide +kernel
theorem subd18_2_38 : subd18_2 [1, 3] = true := by decide +kernel
theorem subd18_2_39 : subd18_2 [2, -5] = true := by decide +kernel
theorem subd18_2_40 : subd18_2 [2, -4] = true := by decide +kernel
theorem subd18_2_41 : subd18_2 [2, -3] = true := by decide +kernel
theorem subd18_2_42 : subd18_2 [2, -2] = true := by decide +kernel
theorem subd18_2_43 : subd18_2 [2, -1] = true := by decide +kernel
theorem subd18_2_44 : subd18_2 [2, 0] = true := by decide +kernel
theorem subd18_2_45 : subd18_2 [2, 1] = true := by decide +kernel
theorem subd18_2_46 : subd18_2 [2, 2] = true := by decide +kernel
theorem subd18_2_47 : subd18_2 [2, 3] = true := by decide +kernel
theorem subd18_2_48 : subd18_2 [3] = true := by decide +kernel
theorem subd18_2_49 : subd18_2 [4] = true := by decide +kernel
theorem sbd18_2_1 : ∀ q ∈ blkd18_2_1, subd18_2 q = true := by
  unfold blkd18_2_1
  exact List.forall_mem_cons.2 ⟨subd18_2_32, List.forall_mem_cons.2 ⟨subd18_2_33, List.forall_mem_cons.2 ⟨subd18_2_34, List.forall_mem_cons.2 ⟨subd18_2_35, List.forall_mem_cons.2 ⟨subd18_2_36, List.forall_mem_cons.2 ⟨subd18_2_37, List.forall_mem_cons.2 ⟨subd18_2_38, List.forall_mem_cons.2 ⟨subd18_2_39, List.forall_mem_cons.2 ⟨subd18_2_40, List.forall_mem_cons.2 ⟨subd18_2_41, List.forall_mem_cons.2 ⟨subd18_2_42, List.forall_mem_cons.2 ⟨subd18_2_43, List.forall_mem_cons.2 ⟨subd18_2_44, List.forall_mem_cons.2 ⟨subd18_2_45, List.forall_mem_cons.2 ⟨subd18_2_46, List.forall_mem_cons.2 ⟨subd18_2_47, List.forall_mem_cons.2 ⟨subd18_2_48, List.forall_mem_cons.2 ⟨subd18_2_49, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd18_3 : ldCheck G d18_3.U d18_3.ms ldd18_3 = true := by decide +kernel
theorem pre_okd18_3 : subPre G cell18 d18_3 = true := by decide +kernel
theorem subd18_3_0 : subd18_3 [-1] = true := by decide +kernel
theorem subd18_3_1 : subd18_3 [0] = true := by decide +kernel
theorem subd18_3_2 : subd18_3 [1] = true := by decide +kernel
theorem sbd18_3_0 : ∀ q ∈ blkd18_3_0, subd18_3 q = true := by
  unfold blkd18_3_0
  exact List.forall_mem_cons.2 ⟨subd18_3_0, List.forall_mem_cons.2 ⟨subd18_3_1, List.forall_mem_cons.2 ⟨subd18_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd19_0 : ldCheck G d19_0.U d19_0.ms ldd19_0 = true := by decide +kernel
theorem pre_okd19_0 : subPre G cell19 d19_0 = true := by decide +kernel
theorem subd19_0_0 : subd19_0 [-1] = true := by decide +kernel
theorem subd19_0_1 : subd19_0 [0] = true := by decide +kernel
theorem subd19_0_2 : subd19_0 [1] = true := by decide +kernel
theorem sbd19_0_0 : ∀ q ∈ blkd19_0_0, subd19_0 q = true := by
  unfold blkd19_0_0
  exact List.forall_mem_cons.2 ⟨subd19_0_0, List.forall_mem_cons.2 ⟨subd19_0_1, List.forall_mem_cons.2 ⟨subd19_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd19_1 : ldCheck G d19_1.U d19_1.ms ldd19_1 = true := by decide +kernel
theorem pre_okd19_1 : subPre G cell19 d19_1 = true := by decide +kernel
theorem subd19_1_0 : subd19_1 [-1] = true := by decide +kernel
theorem subd19_1_1 : subd19_1 [0] = true := by decide +kernel
theorem subd19_1_2 : subd19_1 [1] = true := by decide +kernel
theorem sbd19_1_0 : ∀ q ∈ blkd19_1_0, subd19_1 q = true := by
  unfold blkd19_1_0
  exact List.forall_mem_cons.2 ⟨subd19_1_0, List.forall_mem_cons.2 ⟨subd19_1_1, List.forall_mem_cons.2 ⟨subd19_1_2, List.forall_mem_nil _⟩⟩⟩

end ReflectZphi.Data.Cert5.C142
