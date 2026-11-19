import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_4_0 : subd11_4 [-3] = true := by decide +kernel
theorem subd11_4_1 : subd11_4 [-2, -4] = true := by decide +kernel
theorem subd11_4_2 : subd11_4 [-2, -3] = true := by decide +kernel
theorem subd11_4_3 : subd11_4 [-2, -2] = true := by decide +kernel
theorem subd11_4_4 : subd11_4 [-2, -1] = true := by decide +kernel
theorem subd11_4_5 : subd11_4 [-2, 0] = true := by decide +kernel
theorem subd11_4_6 : subd11_4 [-2, 1] = true := by decide +kernel
theorem subd11_4_7 : subd11_4 [-2, 2] = true := by decide +kernel
theorem subd11_4_8 : subd11_4 [-2, 3] = true := by decide +kernel
theorem subd11_4_9 : subd11_4 [-2, 4] = true := by decide +kernel
theorem subd11_4_10 : subd11_4 [-1, -5] = true := by decide +kernel
theorem subd11_4_11 : subd11_4 [-1, -4] = true := by decide +kernel
theorem subd11_4_12 : subd11_4 [-1, -3] = true := by decide +kernel
theorem subd11_4_13 : subd11_4 [-1, -2] = true := by decide +kernel
theorem subd11_4_14 : subd11_4 [-1, -1] = true := by decide +kernel
theorem subd11_4_15 : subd11_4 [-1, 0] = true := by decide +kernel
theorem subd11_4_16 : subd11_4 [-1, 1] = true := by decide +kernel
theorem subd11_4_17 : subd11_4 [-1, 2] = true := by decide +kernel
theorem subd11_4_18 : subd11_4 [-1, 3] = true := by decide +kernel
theorem subd11_4_19 : subd11_4 [-1, 4] = true := by decide +kernel
theorem subd11_4_20 : subd11_4 [-1, 5] = true := by decide +kernel
theorem subd11_4_21 : subd11_4 [0, -6] = true := by decide +kernel
theorem subd11_4_22 : subd11_4 [0, -5] = true := by decide +kernel
theorem subd11_4_23 : subd11_4 [0, -4] = true := by decide +kernel
theorem subd11_4_24 : subd11_4 [0, -3] = true := by decide +kernel
theorem subd11_4_25 : subd11_4 [0, -2] = true := by decide +kernel
theorem subd11_4_26 : subd11_4 [0, -1] = true := by decide +kernel
theorem subd11_4_27 : subd11_4 [0, 0] = true := by decide +kernel
theorem subd11_4_28 : subd11_4 [0, 1] = true := by decide +kernel
theorem subd11_4_29 : subd11_4 [0, 2] = true := by decide +kernel
theorem subd11_4_30 : subd11_4 [0, 3] = true := by decide +kernel
theorem subd11_4_31 : subd11_4 [0, 4] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_cons.2 ⟨subd11_4_1, List.forall_mem_cons.2 ⟨subd11_4_2, List.forall_mem_cons.2 ⟨subd11_4_3, List.forall_mem_cons.2 ⟨subd11_4_4, List.forall_mem_cons.2 ⟨subd11_4_5, List.forall_mem_cons.2 ⟨subd11_4_6, List.forall_mem_cons.2 ⟨subd11_4_7, List.forall_mem_cons.2 ⟨subd11_4_8, List.forall_mem_cons.2 ⟨subd11_4_9, List.forall_mem_cons.2 ⟨subd11_4_10, List.forall_mem_cons.2 ⟨subd11_4_11, List.forall_mem_cons.2 ⟨subd11_4_12, List.forall_mem_cons.2 ⟨subd11_4_13, List.forall_mem_cons.2 ⟨subd11_4_14, List.forall_mem_cons.2 ⟨subd11_4_15, List.forall_mem_cons.2 ⟨subd11_4_16, List.forall_mem_cons.2 ⟨subd11_4_17, List.forall_mem_cons.2 ⟨subd11_4_18, List.forall_mem_cons.2 ⟨subd11_4_19, List.forall_mem_cons.2 ⟨subd11_4_20, List.forall_mem_cons.2 ⟨subd11_4_21, List.forall_mem_cons.2 ⟨subd11_4_22, List.forall_mem_cons.2 ⟨subd11_4_23, List.forall_mem_cons.2 ⟨subd11_4_24, List.forall_mem_cons.2 ⟨subd11_4_25, List.forall_mem_cons.2 ⟨subd11_4_26, List.forall_mem_cons.2 ⟨subd11_4_27, List.forall_mem_cons.2 ⟨subd11_4_28, List.forall_mem_cons.2 ⟨subd11_4_29, List.forall_mem_cons.2 ⟨subd11_4_30, List.forall_mem_cons.2 ⟨subd11_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_4_32 : subd11_4 [0, 5] = true := by decide +kernel
theorem subd11_4_33 : subd11_4 [1, -6] = true := by decide +kernel
theorem subd11_4_34 : subd11_4 [1, -5] = true := by decide +kernel
theorem subd11_4_35 : subd11_4 [1, -4] = true := by decide +kernel
theorem subd11_4_36 : subd11_4 [1, -3] = true := by decide +kernel
theorem subd11_4_37 : subd11_4 [1, -2] = true := by decide +kernel
theorem subd11_4_38 : subd11_4 [1, -1] = true := by decide +kernel
theorem subd11_4_39 : subd11_4 [1, 0] = true := by decide +kernel
theorem subd11_4_40 : subd11_4 [1, 1] = true := by decide +kernel
theorem subd11_4_41 : subd11_4 [1, 2] = true := by decide +kernel
theorem subd11_4_42 : subd11_4 [1, 3] = true := by decide +kernel
theorem subd11_4_43 : subd11_4 [1, 4] = true := by decide +kernel
theorem subd11_4_44 : subd11_4 [2, -5] = true := by decide +kernel
theorem subd11_4_45 : subd11_4 [2, -4] = true := by decide +kernel
theorem subd11_4_46 : subd11_4 [2, -3] = true := by decide +kernel
theorem subd11_4_47 : subd11_4 [2, -2] = true := by decide +kernel
theorem subd11_4_48 : subd11_4 [2, -1] = true := by decide +kernel
theorem subd11_4_49 : subd11_4 [2, 0] = true := by decide +kernel
theorem subd11_4_50 : subd11_4 [2, 1] = true := by decide +kernel
theorem subd11_4_51 : subd11_4 [2, 2] = true := by decide +kernel
theorem subd11_4_52 : subd11_4 [2, 3] = true := by decide +kernel
theorem subd11_4_53 : subd11_4 [3] = true := by decide +kernel
theorem sbd11_4_1 : ∀ q ∈ blkd11_4_1, subd11_4 q = true := by
  unfold blkd11_4_1
  exact List.forall_mem_cons.2 ⟨subd11_4_32, List.forall_mem_cons.2 ⟨subd11_4_33, List.forall_mem_cons.2 ⟨subd11_4_34, List.forall_mem_cons.2 ⟨subd11_4_35, List.forall_mem_cons.2 ⟨subd11_4_36, List.forall_mem_cons.2 ⟨subd11_4_37, List.forall_mem_cons.2 ⟨subd11_4_38, List.forall_mem_cons.2 ⟨subd11_4_39, List.forall_mem_cons.2 ⟨subd11_4_40, List.forall_mem_cons.2 ⟨subd11_4_41, List.forall_mem_cons.2 ⟨subd11_4_42, List.forall_mem_cons.2 ⟨subd11_4_43, List.forall_mem_cons.2 ⟨subd11_4_44, List.forall_mem_cons.2 ⟨subd11_4_45, List.forall_mem_cons.2 ⟨subd11_4_46, List.forall_mem_cons.2 ⟨subd11_4_47, List.forall_mem_cons.2 ⟨subd11_4_48, List.forall_mem_cons.2 ⟨subd11_4_49, List.forall_mem_cons.2 ⟨subd11_4_50, List.forall_mem_cons.2 ⟨subd11_4_51, List.forall_mem_cons.2 ⟨subd11_4_52, List.forall_mem_cons.2 ⟨subd11_4_53, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_0 : ldCheck G d12_0.U d12_0.ms ldd12_0 = true := by decide +kernel
theorem pre_okd12_0 : subPre G cell12 d12_0 = true := by decide +kernel
theorem subd12_0_0 : subd12_0 [-1] = true := by decide +kernel
theorem subd12_0_1 : subd12_0 [0] = true := by decide +kernel
theorem subd12_0_2 : subd12_0 [1] = true := by decide +kernel
theorem sbd12_0_0 : ∀ q ∈ blkd12_0_0, subd12_0 q = true := by
  unfold blkd12_0_0
  exact List.forall_mem_cons.2 ⟨subd12_0_0, List.forall_mem_cons.2 ⟨subd12_0_1, List.forall_mem_cons.2 ⟨subd12_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd12_1 : ldCheck G d12_1.U d12_1.ms ldd12_1 = true := by decide +kernel
theorem pre_okd12_1 : subPre G cell12 d12_1 = true := by decide +kernel
theorem subd12_1_0 : subd12_1 [-2] = true := by decide +kernel
theorem subd12_1_1 : subd12_1 [-1, -3] = true := by decide +kernel
theorem subd12_1_2 : subd12_1 [-1, -2] = true := by decide +kernel
theorem subd12_1_3 : subd12_1 [-1, -1] = true := by decide +kernel
theorem subd12_1_4 : subd12_1 [-1, 0] = true := by decide +kernel
theorem subd12_1_5 : subd12_1 [-1, 1] = true := by decide +kernel
theorem subd12_1_6 : subd12_1 [0, -3] = true := by decide +kernel
theorem subd12_1_7 : subd12_1 [0, -2] = true := by decide +kernel
theorem subd12_1_8 : subd12_1 [0, -1] = true := by decide +kernel
theorem subd12_1_9 : subd12_1 [0, 0] = true := by decide +kernel
theorem subd12_1_10 : subd12_1 [0, 1] = true := by decide +kernel
theorem subd12_1_11 : subd12_1 [0, 2] = true := by decide +kernel
theorem subd12_1_12 : subd12_1 [1, -2] = true := by decide +kernel
theorem subd12_1_13 : subd12_1 [1, -1] = true := by decide +kernel
theorem subd12_1_14 : subd12_1 [1, 0] = true := by decide +kernel
theorem subd12_1_15 : subd12_1 [1, 1] = true := by decide +kernel
theorem subd12_1_16 : subd12_1 [1, 2] = true := by decide +kernel
theorem subd12_1_17 : subd12_1 [2] = true := by decide +kernel
theorem sbd12_1_0 : ∀ q ∈ blkd12_1_0, subd12_1 q = true := by
  unfold blkd12_1_0
  exact List.forall_mem_cons.2 ⟨subd12_1_0, List.forall_mem_cons.2 ⟨subd12_1_1, List.forall_mem_cons.2 ⟨subd12_1_2, List.forall_mem_cons.2 ⟨subd12_1_3, List.forall_mem_cons.2 ⟨subd12_1_4, List.forall_mem_cons.2 ⟨subd12_1_5, List.forall_mem_cons.2 ⟨subd12_1_6, List.forall_mem_cons.2 ⟨subd12_1_7, List.forall_mem_cons.2 ⟨subd12_1_8, List.forall_mem_cons.2 ⟨subd12_1_9, List.forall_mem_cons.2 ⟨subd12_1_10, List.forall_mem_cons.2 ⟨subd12_1_11, List.forall_mem_cons.2 ⟨subd12_1_12, List.forall_mem_cons.2 ⟨subd12_1_13, List.forall_mem_cons.2 ⟨subd12_1_14, List.forall_mem_cons.2 ⟨subd12_1_15, List.forall_mem_cons.2 ⟨subd12_1_16, List.forall_mem_cons.2 ⟨subd12_1_17, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd12_2 : ldCheck G d12_2.U d12_2.ms ldd12_2 = true := by decide +kernel
theorem pre_okd12_2 : subPre G cell12 d12_2 = true := by decide +kernel
theorem subd12_2_0 : subd12_2 [-4] = true := by decide +kernel
theorem subd12_2_1 : subd12_2 [-3, -5] = true := by decide +kernel
theorem subd12_2_2 : subd12_2 [-3, -4] = true := by decide +kernel
theorem subd12_2_3 : subd12_2 [-3, -3] = true := by decide +kernel
theorem subd12_2_4 : subd12_2 [-3, -2] = true := by decide +kernel
theorem subd12_2_5 : subd12_2 [-3, -1] = true := by decide +kernel
theorem subd12_2_6 : subd12_2 [-3, 0] = true := by decide +kernel
theorem subd12_2_7 : subd12_2 [-3, 1] = true := by decide +kernel
theorem subd12_2_8 : subd12_2 [-3, 2] = true := by decide +kernel
theorem subd12_2_9 : subd12_2 [-2, -5] = true := by decide +kernel
theorem subd12_2_10 : subd12_2 [-2, -4] = true := by decide +kernel
theorem subd12_2_11 : subd12_2 [-2, -3] = true := by decide +kernel
theorem subd12_2_12 : subd12_2 [-2, -2] = true := by decide +kernel
theorem subd12_2_13 : subd12_2 [-2, -1] = true := by decide +kernel
theorem subd12_2_14 : subd12_2 [-2, 0] = true := by decide +kernel
theorem subd12_2_15 : subd12_2 [-2, 1] = true := by decide +kernel
theorem subd12_2_16 : subd12_2 [-2, 2] = true := by decide +kernel
theorem subd12_2_17 : subd12_2 [-2, 3] = true := by decide +kernel
theorem subd12_2_18 : subd12_2 [-1, -5] = true := by decide +kernel
theorem subd12_2_19 : subd12_2 [-1, -4] = true := by decide +kernel
theorem subd12_2_20 : subd12_2 [-1, -3] = true := by decide +kernel
theorem subd12_2_21 : subd12_2 [-1, -2] = true := by decide +kernel
theorem subd12_2_22 : subd12_2 [-1, -1] = true := by decide +kernel
theorem subd12_2_23 : subd12_2 [-1, 0] = true := by decide +kernel
theorem subd12_2_24 : subd12_2 [-1, 1] = true := by decide +kernel
theorem subd12_2_25 : subd12_2 [-1, 2] = true := by decide +kernel
theorem subd12_2_26 : subd12_2 [-1, 3] = true := by decide +kernel
theorem subd12_2_27 : subd12_2 [-1, 4] = true := by decide +kernel
theorem subd12_2_28 : subd12_2 [0, -5] = true := by decide +kernel
theorem subd12_2_29 : subd12_2 [0, -4] = true := by decide +kernel
theorem subd12_2_30 : subd12_2 [0, -3] = true := by decide +kernel
theorem subd12_2_31 : subd12_2 [0, -2] = true := by decide +kernel
theorem sbd12_2_0 : ∀ q ∈ blkd12_2_0, subd12_2 q = true := by
  unfold blkd12_2_0
  exact List.forall_mem_cons.2 ⟨subd12_2_0, List.forall_mem_cons.2 ⟨subd12_2_1, List.forall_mem_cons.2 ⟨subd12_2_2, List.forall_mem_cons.2 ⟨subd12_2_3, List.forall_mem_cons.2 ⟨subd12_2_4, List.forall_mem_cons.2 ⟨subd12_2_5, List.forall_mem_cons.2 ⟨subd12_2_6, List.forall_mem_cons.2 ⟨subd12_2_7, List.forall_mem_cons.2 ⟨subd12_2_8, List.forall_mem_cons.2 ⟨subd12_2_9, List.forall_mem_cons.2 ⟨subd12_2_10, List.forall_mem_cons.2 ⟨subd12_2_11, List.forall_mem_cons.2 ⟨subd12_2_12, List.forall_mem_cons.2 ⟨subd12_2_13, List.forall_mem_cons.2 ⟨subd12_2_14, List.forall_mem_cons.2 ⟨subd12_2_15, List.forall_mem_cons.2 ⟨subd12_2_16, List.forall_mem_cons.2 ⟨subd12_2_17, List.forall_mem_cons.2 ⟨subd12_2_18, List.forall_mem_cons.2 ⟨subd12_2_19, List.forall_mem_cons.2 ⟨subd12_2_20, List.forall_mem_cons.2 ⟨subd12_2_21, List.forall_mem_cons.2 ⟨subd12_2_22, List.forall_mem_cons.2 ⟨subd12_2_23, List.forall_mem_cons.2 ⟨subd12_2_24, List.forall_mem_cons.2 ⟨subd12_2_25, List.forall_mem_cons.2 ⟨subd12_2_26, List.forall_mem_cons.2 ⟨subd12_2_27, List.forall_mem_cons.2 ⟨subd12_2_28, List.forall_mem_cons.2 ⟨subd12_2_29, List.forall_mem_cons.2 ⟨subd12_2_30, List.forall_mem_cons.2 ⟨subd12_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
