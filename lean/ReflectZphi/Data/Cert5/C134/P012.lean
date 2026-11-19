import ReflectZphi.Data.Cert5.C134.Base

namespace ReflectZphi.Data.Cert5.C134

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd4_2 : ldCheck G d4_2.U d4_2.ms ldd4_2 = true := by decide +kernel
theorem pre_okd4_2 : subPre G cell4 d4_2 = true := by decide +kernel
theorem subd4_2_0 : subd4_2 [-2] = true := by decide +kernel
theorem subd4_2_1 : subd4_2 [-1, -3] = true := by decide +kernel
theorem subd4_2_2 : subd4_2 [-1, -2] = true := by decide +kernel
theorem subd4_2_3 : subd4_2 [-1, -1] = true := by decide +kernel
theorem subd4_2_4 : subd4_2 [-1, 0] = true := by decide +kernel
theorem subd4_2_5 : subd4_2 [-1, 1] = true := by decide +kernel
theorem subd4_2_6 : subd4_2 [-1, 2] = true := by decide +kernel
theorem subd4_2_7 : subd4_2 [0, -3] = true := by decide +kernel
theorem subd4_2_8 : subd4_2 [0, -2] = true := by decide +kernel
theorem subd4_2_9 : subd4_2 [0, -1] = true := by decide +kernel
theorem subd4_2_10 : subd4_2 [0, 0] = true := by decide +kernel
theorem subd4_2_11 : subd4_2 [0, 1] = true := by decide +kernel
theorem subd4_2_12 : subd4_2 [0, 2] = true := by decide +kernel
theorem subd4_2_13 : subd4_2 [1, -3] = true := by decide +kernel
theorem subd4_2_14 : subd4_2 [1, -2] = true := by decide +kernel
theorem subd4_2_15 : subd4_2 [1, -1] = true := by decide +kernel
theorem subd4_2_16 : subd4_2 [1, 0] = true := by decide +kernel
theorem subd4_2_17 : subd4_2 [1, 1] = true := by decide +kernel
theorem subd4_2_18 : subd4_2 [1, 2] = true := by decide +kernel
theorem subd4_2_19 : subd4_2 [2] = true := by decide +kernel
theorem sbd4_2_0 : ∀ q ∈ blkd4_2_0, subd4_2 q = true := by
  unfold blkd4_2_0
  exact List.forall_mem_cons.2 ⟨subd4_2_0, List.forall_mem_cons.2 ⟨subd4_2_1, List.forall_mem_cons.2 ⟨subd4_2_2, List.forall_mem_cons.2 ⟨subd4_2_3, List.forall_mem_cons.2 ⟨subd4_2_4, List.forall_mem_cons.2 ⟨subd4_2_5, List.forall_mem_cons.2 ⟨subd4_2_6, List.forall_mem_cons.2 ⟨subd4_2_7, List.forall_mem_cons.2 ⟨subd4_2_8, List.forall_mem_cons.2 ⟨subd4_2_9, List.forall_mem_cons.2 ⟨subd4_2_10, List.forall_mem_cons.2 ⟨subd4_2_11, List.forall_mem_cons.2 ⟨subd4_2_12, List.forall_mem_cons.2 ⟨subd4_2_13, List.forall_mem_cons.2 ⟨subd4_2_14, List.forall_mem_cons.2 ⟨subd4_2_15, List.forall_mem_cons.2 ⟨subd4_2_16, List.forall_mem_cons.2 ⟨subd4_2_17, List.forall_mem_cons.2 ⟨subd4_2_18, List.forall_mem_cons.2 ⟨subd4_2_19, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [-3] = true := by decide +kernel
theorem subd4_3_1 : subd4_3 [-2, -4] = true := by decide +kernel
theorem subd4_3_2 : subd4_3 [-2, -3] = true := by decide +kernel
theorem subd4_3_3 : subd4_3 [-2, -2] = true := by decide +kernel
theorem subd4_3_4 : subd4_3 [-2, -1] = true := by decide +kernel
theorem subd4_3_5 : subd4_3 [-2, 0] = true := by decide +kernel
theorem subd4_3_6 : subd4_3 [-2, 1] = true := by decide +kernel
theorem subd4_3_7 : subd4_3 [-2, 2] = true := by decide +kernel
theorem subd4_3_8 : subd4_3 [-1, -4] = true := by decide +kernel
theorem subd4_3_9 : subd4_3 [-1, -3] = true := by decide +kernel
theorem subd4_3_10 : subd4_3 [-1, -2] = true := by decide +kernel
theorem subd4_3_11 : subd4_3 [-1, -1] = true := by decide +kernel
theorem subd4_3_12 : subd4_3 [-1, 0] = true := by decide +kernel
theorem subd4_3_13 : subd4_3 [-1, 1] = true := by decide +kernel
theorem subd4_3_14 : subd4_3 [-1, 2] = true := by decide +kernel
theorem subd4_3_15 : subd4_3 [-1, 3] = true := by decide +kernel
theorem subd4_3_16 : subd4_3 [0, -4] = true := by decide +kernel
theorem subd4_3_17 : subd4_3 [0, -3] = true := by decide +kernel
theorem subd4_3_18 : subd4_3 [0, -2] = true := by decide +kernel
theorem subd4_3_19 : subd4_3 [0, -1] = true := by decide +kernel
theorem subd4_3_20 : subd4_3 [0, 0] = true := by decide +kernel
theorem subd4_3_21 : subd4_3 [0, 1] = true := by decide +kernel
theorem subd4_3_22 : subd4_3 [0, 2] = true := by decide +kernel
theorem subd4_3_23 : subd4_3 [0, 3] = true := by decide +kernel
theorem subd4_3_24 : subd4_3 [1, -4] = true := by decide +kernel
theorem subd4_3_25 : subd4_3 [1, -3] = true := by decide +kernel
theorem subd4_3_26 : subd4_3 [1, -2] = true := by decide +kernel
theorem subd4_3_27 : subd4_3 [1, -1] = true := by decide +kernel
theorem subd4_3_28 : subd4_3 [1, 0] = true := by decide +kernel
theorem subd4_3_29 : subd4_3 [1, 1] = true := by decide +kernel
theorem subd4_3_30 : subd4_3 [1, 2] = true := by decide +kernel
theorem subd4_3_31 : subd4_3 [1, 3] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_cons.2 ⟨subd4_3_1, List.forall_mem_cons.2 ⟨subd4_3_2, List.forall_mem_cons.2 ⟨subd4_3_3, List.forall_mem_cons.2 ⟨subd4_3_4, List.forall_mem_cons.2 ⟨subd4_3_5, List.forall_mem_cons.2 ⟨subd4_3_6, List.forall_mem_cons.2 ⟨subd4_3_7, List.forall_mem_cons.2 ⟨subd4_3_8, List.forall_mem_cons.2 ⟨subd4_3_9, List.forall_mem_cons.2 ⟨subd4_3_10, List.forall_mem_cons.2 ⟨subd4_3_11, List.forall_mem_cons.2 ⟨subd4_3_12, List.forall_mem_cons.2 ⟨subd4_3_13, List.forall_mem_cons.2 ⟨subd4_3_14, List.forall_mem_cons.2 ⟨subd4_3_15, List.forall_mem_cons.2 ⟨subd4_3_16, List.forall_mem_cons.2 ⟨subd4_3_17, List.forall_mem_cons.2 ⟨subd4_3_18, List.forall_mem_cons.2 ⟨subd4_3_19, List.forall_mem_cons.2 ⟨subd4_3_20, List.forall_mem_cons.2 ⟨subd4_3_21, List.forall_mem_cons.2 ⟨subd4_3_22, List.forall_mem_cons.2 ⟨subd4_3_23, List.forall_mem_cons.2 ⟨subd4_3_24, List.forall_mem_cons.2 ⟨subd4_3_25, List.forall_mem_cons.2 ⟨subd4_3_26, List.forall_mem_cons.2 ⟨subd4_3_27, List.forall_mem_cons.2 ⟨subd4_3_28, List.forall_mem_cons.2 ⟨subd4_3_29, List.forall_mem_cons.2 ⟨subd4_3_30, List.forall_mem_cons.2 ⟨subd4_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_3_32 : subd4_3 [2, -3] = true := by decide +kernel
theorem subd4_3_33 : subd4_3 [2, -2] = true := by decide +kernel
theorem subd4_3_34 : subd4_3 [2, -1] = true := by decide +kernel
theorem subd4_3_35 : subd4_3 [2, 0] = true := by decide +kernel
theorem subd4_3_36 : subd4_3 [2, 1] = true := by decide +kernel
theorem subd4_3_37 : subd4_3 [2, 2] = true := by decide +kernel
theorem subd4_3_38 : subd4_3 [2, 3] = true := by decide +kernel
theorem subd4_3_39 : subd4_3 [3] = true := by decide +kernel
theorem sbd4_3_1 : ∀ q ∈ blkd4_3_1, subd4_3 q = true := by
  unfold blkd4_3_1
  exact List.forall_mem_cons.2 ⟨subd4_3_32, List.forall_mem_cons.2 ⟨subd4_3_33, List.forall_mem_cons.2 ⟨subd4_3_34, List.forall_mem_cons.2 ⟨subd4_3_35, List.forall_mem_cons.2 ⟨subd4_3_36, List.forall_mem_cons.2 ⟨subd4_3_37, List.forall_mem_cons.2 ⟨subd4_3_38, List.forall_mem_cons.2 ⟨subd4_3_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [-3] = true := by decide +kernel
theorem subd4_4_1 : subd4_4 [-2, -3] = true := by decide +kernel
theorem subd4_4_2 : subd4_4 [-2, -2] = true := by decide +kernel
theorem subd4_4_3 : subd4_4 [-2, -1] = true := by decide +kernel
theorem subd4_4_4 : subd4_4 [-2, 0] = true := by decide +kernel
theorem subd4_4_5 : subd4_4 [-2, 1] = true := by decide +kernel
theorem subd4_4_6 : subd4_4 [-2, 2] = true := by decide +kernel
theorem subd4_4_7 : subd4_4 [-1, -4] = true := by decide +kernel
theorem subd4_4_8 : subd4_4 [-1, -3] = true := by decide +kernel
theorem subd4_4_9 : subd4_4 [-1, -2] = true := by decide +kernel
theorem subd4_4_10 : subd4_4 [-1, -1] = true := by decide +kernel
theorem subd4_4_11 : subd4_4 [-1, 0] = true := by decide +kernel
theorem subd4_4_12 : subd4_4 [-1, 1] = true := by decide +kernel
theorem subd4_4_13 : subd4_4 [-1, 2] = true := by decide +kernel
theorem subd4_4_14 : subd4_4 [-1, 3] = true := by decide +kernel
theorem subd4_4_15 : subd4_4 [0, -4] = true := by decide +kernel
theorem subd4_4_16 : subd4_4 [0, -3] = true := by decide +kernel
theorem subd4_4_17 : subd4_4 [0, -2] = true := by decide +kernel
theorem subd4_4_18 : subd4_4 [0, -1] = true := by decide +kernel
theorem subd4_4_19 : subd4_4 [0, 0] = true := by decide +kernel
theorem subd4_4_20 : subd4_4 [0, 1] = true := by decide +kernel
theorem subd4_4_21 : subd4_4 [0, 2] = true := by decide +kernel
theorem subd4_4_22 : subd4_4 [0, 3] = true := by decide +kernel
theorem subd4_4_23 : subd4_4 [1, -4] = true := by decide +kernel
theorem subd4_4_24 : subd4_4 [1, -3] = true := by decide +kernel
theorem subd4_4_25 : subd4_4 [1, -2] = true := by decide +kernel
theorem subd4_4_26 : subd4_4 [1, -1] = true := by decide +kernel
theorem subd4_4_27 : subd4_4 [1, 0] = true := by decide +kernel
theorem subd4_4_28 : subd4_4 [1, 1] = true := by decide +kernel
theorem subd4_4_29 : subd4_4 [1, 2] = true := by decide +kernel
theorem subd4_4_30 : subd4_4 [1, 3] = true := by decide +kernel
theorem subd4_4_31 : subd4_4 [2, -3] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_cons.2 ⟨subd4_4_1, List.forall_mem_cons.2 ⟨subd4_4_2, List.forall_mem_cons.2 ⟨subd4_4_3, List.forall_mem_cons.2 ⟨subd4_4_4, List.forall_mem_cons.2 ⟨subd4_4_5, List.forall_mem_cons.2 ⟨subd4_4_6, List.forall_mem_cons.2 ⟨subd4_4_7, List.forall_mem_cons.2 ⟨subd4_4_8, List.forall_mem_cons.2 ⟨subd4_4_9, List.forall_mem_cons.2 ⟨subd4_4_10, List.forall_mem_cons.2 ⟨subd4_4_11, List.forall_mem_cons.2 ⟨subd4_4_12, List.forall_mem_cons.2 ⟨subd4_4_13, List.forall_mem_cons.2 ⟨subd4_4_14, List.forall_mem_cons.2 ⟨subd4_4_15, List.forall_mem_cons.2 ⟨subd4_4_16, List.forall_mem_cons.2 ⟨subd4_4_17, List.forall_mem_cons.2 ⟨subd4_4_18, List.forall_mem_cons.2 ⟨subd4_4_19, List.forall_mem_cons.2 ⟨subd4_4_20, List.forall_mem_cons.2 ⟨subd4_4_21, List.forall_mem_cons.2 ⟨subd4_4_22, List.forall_mem_cons.2 ⟨subd4_4_23, List.forall_mem_cons.2 ⟨subd4_4_24, List.forall_mem_cons.2 ⟨subd4_4_25, List.forall_mem_cons.2 ⟨subd4_4_26, List.forall_mem_cons.2 ⟨subd4_4_27, List.forall_mem_cons.2 ⟨subd4_4_28, List.forall_mem_cons.2 ⟨subd4_4_29, List.forall_mem_cons.2 ⟨subd4_4_30, List.forall_mem_cons.2 ⟨subd4_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd4_4_32 : subd4_4 [2, -2] = true := by decide +kernel
theorem subd4_4_33 : subd4_4 [2, -1] = true := by decide +kernel
theorem subd4_4_34 : subd4_4 [2, 0] = true := by decide +kernel
theorem subd4_4_35 : subd4_4 [2, 1] = true := by decide +kernel
theorem subd4_4_36 : subd4_4 [2, 2] = true := by decide +kernel
theorem subd4_4_37 : subd4_4 [3] = true := by decide +kernel
theorem sbd4_4_1 : ∀ q ∈ blkd4_4_1, subd4_4 q = true := by
  unfold blkd4_4_1
  exact List.forall_mem_cons.2 ⟨subd4_4_32, List.forall_mem_cons.2 ⟨subd4_4_33, List.forall_mem_cons.2 ⟨subd4_4_34, List.forall_mem_cons.2 ⟨subd4_4_35, List.forall_mem_cons.2 ⟨subd4_4_36, List.forall_mem_cons.2 ⟨subd4_4_37, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel
theorem subd4_5_0 : subd4_5 [-2] = true := by decide +kernel
theorem subd4_5_1 : subd4_5 [-1, -4] = true := by decide +kernel
theorem subd4_5_2 : subd4_5 [-1, -3] = true := by decide +kernel
theorem subd4_5_3 : subd4_5 [-1, -2] = true := by decide +kernel
theorem subd4_5_4 : subd4_5 [-1, -1] = true := by decide +kernel
theorem subd4_5_5 : subd4_5 [-1, 0] = true := by decide +kernel
theorem subd4_5_6 : subd4_5 [-1, 1] = true := by decide +kernel
theorem subd4_5_7 : subd4_5 [-1, 2] = true := by decide +kernel
theorem subd4_5_8 : subd4_5 [0, -4] = true := by decide +kernel
theorem subd4_5_9 : subd4_5 [0, -3] = true := by decide +kernel
theorem subd4_5_10 : subd4_5 [0, -2] = true := by decide +kernel
theorem subd4_5_11 : subd4_5 [0, -1] = true := by decide +kernel
theorem subd4_5_12 : subd4_5 [0, 0] = true := by decide +kernel
theorem subd4_5_13 : subd4_5 [0, 1] = true := by decide +kernel
theorem subd4_5_14 : subd4_5 [0, 2] = true := by decide +kernel
theorem subd4_5_15 : subd4_5 [0, 3] = true := by decide +kernel
theorem subd4_5_16 : subd4_5 [1, -3] = true := by decide +kernel
theorem subd4_5_17 : subd4_5 [1, -2] = true := by decide +kernel
theorem subd4_5_18 : subd4_5 [1, -1] = true := by decide +kernel
theorem subd4_5_19 : subd4_5 [1, 0] = true := by decide +kernel
theorem subd4_5_20 : subd4_5 [1, 1] = true := by decide +kernel
theorem subd4_5_21 : subd4_5 [1, 2] = true := by decide +kernel
theorem subd4_5_22 : subd4_5 [1, 3] = true := by decide +kernel
theorem subd4_5_23 : subd4_5 [2] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_cons.2 ⟨subd4_5_1, List.forall_mem_cons.2 ⟨subd4_5_2, List.forall_mem_cons.2 ⟨subd4_5_3, List.forall_mem_cons.2 ⟨subd4_5_4, List.forall_mem_cons.2 ⟨subd4_5_5, List.forall_mem_cons.2 ⟨subd4_5_6, List.forall_mem_cons.2 ⟨subd4_5_7, List.forall_mem_cons.2 ⟨subd4_5_8, List.forall_mem_cons.2 ⟨subd4_5_9, List.forall_mem_cons.2 ⟨subd4_5_10, List.forall_mem_cons.2 ⟨subd4_5_11, List.forall_mem_cons.2 ⟨subd4_5_12, List.forall_mem_cons.2 ⟨subd4_5_13, List.forall_mem_cons.2 ⟨subd4_5_14, List.forall_mem_cons.2 ⟨subd4_5_15, List.forall_mem_cons.2 ⟨subd4_5_16, List.forall_mem_cons.2 ⟨subd4_5_17, List.forall_mem_cons.2 ⟨subd4_5_18, List.forall_mem_cons.2 ⟨subd4_5_19, List.forall_mem_cons.2 ⟨subd4_5_20, List.forall_mem_cons.2 ⟨subd4_5_21, List.forall_mem_cons.2 ⟨subd4_5_22, List.forall_mem_cons.2 ⟨subd4_5_23, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C134
