import ReflectZphi.Data.Cert5.C136.Base

namespace ReflectZphi.Data.Cert5.C136

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd3_3_0 : subd3_3 [-1, -2] = true := by decide +kernel
theorem subd3_3_1 : subd3_3 [-1, -1] = true := by decide +kernel
theorem subd3_3_2 : subd3_3 [-1, 0] = true := by decide +kernel
theorem subd3_3_3 : subd3_3 [-1, 1] = true := by decide +kernel
theorem subd3_3_4 : subd3_3 [0, -2] = true := by decide +kernel
theorem subd3_3_5 : subd3_3 [0, -1] = true := by decide +kernel
theorem subd3_3_6 : subd3_3 [0, 0] = true := by decide +kernel
theorem subd3_3_7 : subd3_3 [0, 1] = true := by decide +kernel
theorem subd3_3_8 : subd3_3 [1, -2] = true := by decide +kernel
theorem subd3_3_9 : subd3_3 [1, -1] = true := by decide +kernel
theorem subd3_3_10 : subd3_3 [1, 0] = true := by decide +kernel
theorem subd3_3_11 : subd3_3 [1, 1] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_cons.2 ⟨subd3_3_1, List.forall_mem_cons.2 ⟨subd3_3_2, List.forall_mem_cons.2 ⟨subd3_3_3, List.forall_mem_cons.2 ⟨subd3_3_4, List.forall_mem_cons.2 ⟨subd3_3_5, List.forall_mem_cons.2 ⟨subd3_3_6, List.forall_mem_cons.2 ⟨subd3_3_7, List.forall_mem_cons.2 ⟨subd3_3_8, List.forall_mem_cons.2 ⟨subd3_3_9, List.forall_mem_cons.2 ⟨subd3_3_10, List.forall_mem_cons.2 ⟨subd3_3_11, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_0 : ldCheck G d4_0.U d4_0.ms ldd4_0 = true := by decide +kernel
theorem pre_okd4_0 : subPre G cell4 d4_0 = true := by decide +kernel
theorem subd4_0_0 : subd4_0 [-1] = true := by decide +kernel
theorem subd4_0_1 : subd4_0 [0] = true := by decide +kernel
theorem subd4_0_2 : subd4_0 [1] = true := by decide +kernel
theorem sbd4_0_0 : ∀ q ∈ blkd4_0_0, subd4_0 q = true := by
  unfold blkd4_0_0
  exact List.forall_mem_cons.2 ⟨subd4_0_0, List.forall_mem_cons.2 ⟨subd4_0_1, List.forall_mem_cons.2 ⟨subd4_0_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_1 : ldCheck G d4_1.U d4_1.ms ldd4_1 = true := by decide +kernel
theorem pre_okd4_1 : subPre G cell4 d4_1 = true := by decide +kernel
theorem subd4_1_0 : subd4_1 [-3, -2] = true := by decide +kernel
theorem subd4_1_1 : subd4_1 [-3, -1] = true := by decide +kernel
theorem subd4_1_2 : subd4_1 [-3, 0] = true := by decide +kernel
theorem subd4_1_3 : subd4_1 [-3, 1] = true := by decide +kernel
theorem subd4_1_4 : subd4_1 [-3, 2] = true := by decide +kernel
theorem subd4_1_5 : subd4_1 [-2, -3] = true := by decide +kernel
theorem subd4_1_6 : subd4_1 [-2, -2] = true := by decide +kernel
theorem subd4_1_7 : subd4_1 [-2, -1] = true := by decide +kernel
theorem subd4_1_8 : subd4_1 [-2, 0] = true := by decide +kernel
theorem subd4_1_9 : subd4_1 [-2, 1] = true := by decide +kernel
theorem subd4_1_10 : subd4_1 [-2, 2] = true := by decide +kernel
theorem subd4_1_11 : subd4_1 [-2, 3] = true := by decide +kernel
theorem subd4_1_12 : subd4_1 [-1, -4] = true := by decide +kernel
theorem subd4_1_13 : subd4_1 [-1, -3] = true := by decide +kernel
theorem subd4_1_14 : subd4_1 [-1, -2] = true := by decide +kernel
theorem subd4_1_15 : subd4_1 [-1, -1] = true := by decide +kernel
theorem subd4_1_16 : subd4_1 [-1, 0] = true := by decide +kernel
theorem subd4_1_17 : subd4_1 [-1, 1] = true := by decide +kernel
theorem subd4_1_18 : subd4_1 [-1, 2] = true := by decide +kernel
theorem subd4_1_19 : subd4_1 [-1, 3] = true := by decide +kernel
theorem subd4_1_20 : subd4_1 [0, -4] = true := by decide +kernel
theorem subd4_1_21 : subd4_1 [0, -3] = true := by decide +kernel
theorem subd4_1_22 : subd4_1 [0, -2] = true := by decide +kernel
theorem subd4_1_23 : subd4_1 [0, -1] = true := by decide +kernel
theorem subd4_1_24 : subd4_1 [0, 0] = true := by decide +kernel
theorem subd4_1_25 : subd4_1 [0, 1] = true := by decide +kernel
theorem subd4_1_26 : subd4_1 [0, 2] = true := by decide +kernel
theorem subd4_1_27 : subd4_1 [0, 3] = true := by decide +kernel
theorem subd4_1_28 : subd4_1 [1, -4] = true := by decide +kernel
theorem subd4_1_29 : subd4_1 [1, -3] = true := by decide +kernel
theorem subd4_1_30 : subd4_1 [1, -2] = true := by decide +kernel
theorem subd4_1_31 : subd4_1 [1, -1] = true := by decide +kernel
theorem sbd4_1_0 : ∀ q ∈ blkd4_1_0, subd4_1 q = true := by
  unfold blkd4_1_0
  exact List.forall_mem_cons.2 ⟨subd4_1_0, List.forall_mem_cons.2 ⟨subd4_1_1, List.forall_mem_cons.2 ⟨subd4_1_2, List.forall_mem_cons.2 ⟨subd4_1_3, List.forall_mem_cons.2 ⟨subd4_1_4, List.forall_mem_cons.2 ⟨subd4_1_5, List.forall_mem_cons.2 ⟨subd4_1_6, List.forall_mem_cons.2 ⟨subd4_1_7, List.forall_mem_cons.2 ⟨subd4_1_8, List.forall_mem_cons.2 ⟨subd4_1_9, List.forall_mem_cons.2 ⟨subd4_1_10, List.forall_mem_cons.2 ⟨subd4_1_11, List.forall_mem_cons.2 ⟨subd4_1_12, List.forall_mem_cons.2 ⟨subd4_1_13, List.forall_mem_cons.2 ⟨subd4_1_14, List.forall_mem_cons.2 ⟨subd4_1_15, List.forall_mem_cons.2 ⟨subd4_1_16, List.forall_mem_cons.2 ⟨subd4_1_17, List.forall_mem_cons.2 ⟨subd4_1_18, List.forall_mem_cons.2 ⟨subd4_1_19, List.forall_mem_cons.2 ⟨subd4_1_20, List.forall_mem_cons.2 ⟨subd4_1_21, List.forall_mem_cons.2 ⟨subd4_1_22, List.forall_mem_cons.2 ⟨subd4_1_23, List.forall_mem_cons.2 ⟨subd4_1_24, List.forall_mem_cons.2 ⟨subd4_1_25, List.forall_mem_cons.2 ⟨subd4_1_26, List.forall_mem_cons.2 ⟨subd4_1_27, List.forall_mem_cons.2 ⟨subd4_1_28, List.forall_mem_cons.2 ⟨subd4_1_29, List.forall_mem_cons.2 ⟨subd4_1_30, List.forall_mem_cons.2 ⟨subd4_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_1_32 : subd4_1 [1, 0] = true := by decide +kernel
theorem subd4_1_33 : subd4_1 [1, 1] = true := by decide +kernel
theorem subd4_1_34 : subd4_1 [1, 2] = true := by decide +kernel
theorem subd4_1_35 : subd4_1 [1, 3] = true := by decide +kernel
theorem subd4_1_36 : subd4_1 [2, -4] = true := by decide +kernel
theorem subd4_1_37 : subd4_1 [2, -3] = true := by decide +kernel
theorem subd4_1_38 : subd4_1 [2, -2] = true := by decide +kernel
theorem subd4_1_39 : subd4_1 [2, -1] = true := by decide +kernel
theorem subd4_1_40 : subd4_1 [2, 0] = true := by decide +kernel
theorem subd4_1_41 : subd4_1 [2, 1] = true := by decide +kernel
theorem subd4_1_42 : subd4_1 [2, 2] = true := by decide +kernel
theorem subd4_1_43 : subd4_1 [3, -3] = true := by decide +kernel
theorem subd4_1_44 : subd4_1 [3, -2] = true := by decide +kernel
theorem subd4_1_45 : subd4_1 [3, -1] = true := by decide +kernel
theorem subd4_1_46 : subd4_1 [3, 0] = true := by decide +kernel
theorem subd4_1_47 : subd4_1 [3, 1] = true := by decide +kernel
theorem sbd4_1_1 : ∀ q ∈ blkd4_1_1, subd4_1 q = true := by
  unfold blkd4_1_1
  exact List.forall_mem_cons.2 ⟨subd4_1_32, List.forall_mem_cons.2 ⟨subd4_1_33, List.forall_mem_cons.2 ⟨subd4_1_34, List.forall_mem_cons.2 ⟨subd4_1_35, List.forall_mem_cons.2 ⟨subd4_1_36, List.forall_mem_cons.2 ⟨subd4_1_37, List.forall_mem_cons.2 ⟨subd4_1_38, List.forall_mem_cons.2 ⟨subd4_1_39, List.forall_mem_cons.2 ⟨subd4_1_40, List.forall_mem_cons.2 ⟨subd4_1_41, List.forall_mem_cons.2 ⟨subd4_1_42, List.forall_mem_cons.2 ⟨subd4_1_43, List.forall_mem_cons.2 ⟨subd4_1_44, List.forall_mem_cons.2 ⟨subd4_1_45, List.forall_mem_cons.2 ⟨subd4_1_46, List.forall_mem_cons.2 ⟨subd4_1_47, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C136
