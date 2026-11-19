import ReflectZphi.Data.Cert5.C107.Base

namespace ReflectZphi.Data.Cert5.C107

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [-2] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [-1] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [0] = true := by decide +kernel
theorem subd4_4_3 : subd4_4 [1] = true := by decide +kernel
theorem subd4_4_4 : subd4_4 [2] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_cons.2 ⟨subd4_4_3, List.forall_mem_cons.2 ⟨subd4_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel
theorem subd4_5_0 : subd4_5 [-1] = true := by decide +kernel
theorem subd4_5_1 : subd4_5 [0] = true := by decide +kernel
theorem subd4_5_2 : subd4_5 [1] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_cons.2 ⟨subd4_5_1, List.forall_mem_cons.2 ⟨subd4_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [-3] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [-2, -4] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [-2, -3] = true := by decide +kernel
theorem subd4_6_3 : subd4_6 [-2, -2] = true := by decide +kernel
theorem subd4_6_4 : subd4_6 [-2, -1] = true := by decide +kernel
theorem subd4_6_5 : subd4_6 [-2, 0] = true := by decide +kernel
theorem subd4_6_6 : subd4_6 [-2, 1] = true := by decide +kernel
theorem subd4_6_7 : subd4_6 [-2, 2] = true := by decide +kernel
theorem subd4_6_8 : subd4_6 [-1, -4] = true := by decide +kernel
theorem subd4_6_9 : subd4_6 [-1, -3] = true := by decide +kernel
theorem subd4_6_10 : subd4_6 [-1, -2] = true := by decide +kernel
theorem subd4_6_11 : subd4_6 [-1, -1] = true := by decide +kernel
theorem subd4_6_12 : subd4_6 [-1, 0] = true := by decide +kernel
theorem subd4_6_13 : subd4_6 [-1, 1] = true := by decide +kernel
theorem subd4_6_14 : subd4_6 [-1, 2] = true := by decide +kernel
theorem subd4_6_15 : subd4_6 [-1, 3] = true := by decide +kernel
theorem subd4_6_16 : subd4_6 [0, -4] = true := by decide +kernel
theorem subd4_6_17 : subd4_6 [0, -3] = true := by decide +kernel
theorem subd4_6_18 : subd4_6 [0, -2] = true := by decide +kernel
theorem subd4_6_19 : subd4_6 [0, -1] = true := by decide +kernel
theorem subd4_6_20 : subd4_6 [0, 0] = true := by decide +kernel
theorem subd4_6_21 : subd4_6 [0, 1] = true := by decide +kernel
theorem subd4_6_22 : subd4_6 [0, 2] = true := by decide +kernel
theorem subd4_6_23 : subd4_6 [0, 3] = true := by decide +kernel
theorem subd4_6_24 : subd4_6 [1, -4] = true := by decide +kernel
theorem subd4_6_25 : subd4_6 [1, -3] = true := by decide +kernel
theorem subd4_6_26 : subd4_6 [1, -2] = true := by decide +kernel
theorem subd4_6_27 : subd4_6 [1, -1] = true := by decide +kernel
theorem subd4_6_28 : subd4_6 [1, 0] = true := by decide +kernel
theorem subd4_6_29 : subd4_6 [1, 1] = true := by decide +kernel
theorem subd4_6_30 : subd4_6 [1, 2] = true := by decide +kernel
theorem subd4_6_31 : subd4_6 [1, 3] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_cons.2 ⟨subd4_6_3, List.forall_mem_cons.2 ⟨subd4_6_4, List.forall_mem_cons.2 ⟨subd4_6_5, List.forall_mem_cons.2 ⟨subd4_6_6, List.forall_mem_cons.2 ⟨subd4_6_7, List.forall_mem_cons.2 ⟨subd4_6_8, List.forall_mem_cons.2 ⟨subd4_6_9, List.forall_mem_cons.2 ⟨subd4_6_10, List.forall_mem_cons.2 ⟨subd4_6_11, List.forall_mem_cons.2 ⟨subd4_6_12, List.forall_mem_cons.2 ⟨subd4_6_13, List.forall_mem_cons.2 ⟨subd4_6_14, List.forall_mem_cons.2 ⟨subd4_6_15, List.forall_mem_cons.2 ⟨subd4_6_16, List.forall_mem_cons.2 ⟨subd4_6_17, List.forall_mem_cons.2 ⟨subd4_6_18, List.forall_mem_cons.2 ⟨subd4_6_19, List.forall_mem_cons.2 ⟨subd4_6_20, List.forall_mem_cons.2 ⟨subd4_6_21, List.forall_mem_cons.2 ⟨subd4_6_22, List.forall_mem_cons.2 ⟨subd4_6_23, List.forall_mem_cons.2 ⟨subd4_6_24, List.forall_mem_cons.2 ⟨subd4_6_25, List.forall_mem_cons.2 ⟨subd4_6_26, List.forall_mem_cons.2 ⟨subd4_6_27, List.forall_mem_cons.2 ⟨subd4_6_28, List.forall_mem_cons.2 ⟨subd4_6_29, List.forall_mem_cons.2 ⟨subd4_6_30, List.forall_mem_cons.2 ⟨subd4_6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_6_32 : subd4_6 [2, -3] = true := by decide +kernel
theorem subd4_6_33 : subd4_6 [2, -2] = true := by decide +kernel
theorem subd4_6_34 : subd4_6 [2, -1] = true := by decide +kernel
theorem subd4_6_35 : subd4_6 [2, 0] = true := by decide +kernel
theorem subd4_6_36 : subd4_6 [2, 1] = true := by decide +kernel
theorem subd4_6_37 : subd4_6 [2, 2] = true := by decide +kernel
theorem subd4_6_38 : subd4_6 [2, 3] = true := by decide +kernel
theorem subd4_6_39 : subd4_6 [3] = true := by decide +kernel
theorem sbd4_6_1 : ∀ q ∈ blkd4_6_1, subd4_6 q = true := by
  unfold blkd4_6_1
  exact List.forall_mem_cons.2 ⟨subd4_6_32, List.forall_mem_cons.2 ⟨subd4_6_33, List.forall_mem_cons.2 ⟨subd4_6_34, List.forall_mem_cons.2 ⟨subd4_6_35, List.forall_mem_cons.2 ⟨subd4_6_36, List.forall_mem_cons.2 ⟨subd4_6_37, List.forall_mem_cons.2 ⟨subd4_6_38, List.forall_mem_cons.2 ⟨subd4_6_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [-2] = true := by decide +kernel
theorem subd4_7_1 : subd4_7 [-1] = true := by decide +kernel
theorem subd4_7_2 : subd4_7 [0] = true := by decide +kernel
theorem subd4_7_3 : subd4_7 [1] = true := by decide +kernel
theorem subd4_7_4 : subd4_7 [2] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_cons.2 ⟨subd4_7_1, List.forall_mem_cons.2 ⟨subd4_7_2, List.forall_mem_cons.2 ⟨subd4_7_3, List.forall_mem_cons.2 ⟨subd4_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C107
