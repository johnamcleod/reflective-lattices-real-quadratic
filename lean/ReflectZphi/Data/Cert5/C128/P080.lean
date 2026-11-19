import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd11_2_0 : subd11_2 [-3] = true := by decide +kernel
theorem subd11_2_1 : subd11_2 [-2, -3] = true := by decide +kernel
theorem subd11_2_2 : subd11_2 [-2, -2] = true := by decide +kernel
theorem subd11_2_3 : subd11_2 [-2, -1] = true := by decide +kernel
theorem subd11_2_4 : subd11_2 [-2, 0] = true := by decide +kernel
theorem subd11_2_5 : subd11_2 [-2, 1] = true := by decide +kernel
theorem subd11_2_6 : subd11_2 [-2, 2] = true := by decide +kernel
theorem subd11_2_7 : subd11_2 [-2, 3] = true := by decide +kernel
theorem subd11_2_8 : subd11_2 [-1, -4] = true := by decide +kernel
theorem subd11_2_9 : subd11_2 [-1, -3] = true := by decide +kernel
theorem subd11_2_10 : subd11_2 [-1, -2] = true := by decide +kernel
theorem subd11_2_11 : subd11_2 [-1, -1] = true := by decide +kernel
theorem subd11_2_12 : subd11_2 [-1, 0] = true := by decide +kernel
theorem subd11_2_13 : subd11_2 [-1, 1] = true := by decide +kernel
theorem subd11_2_14 : subd11_2 [-1, 2] = true := by decide +kernel
theorem subd11_2_15 : subd11_2 [-1, 3] = true := by decide +kernel
theorem subd11_2_16 : subd11_2 [0, -4] = true := by decide +kernel
theorem subd11_2_17 : subd11_2 [0, -3] = true := by decide +kernel
theorem subd11_2_18 : subd11_2 [0, -2] = true := by decide +kernel
theorem subd11_2_19 : subd11_2 [0, -1] = true := by decide +kernel
theorem subd11_2_20 : subd11_2 [0, 0] = true := by decide +kernel
theorem subd11_2_21 : subd11_2 [0, 1] = true := by decide +kernel
theorem subd11_2_22 : subd11_2 [0, 2] = true := by decide +kernel
theorem subd11_2_23 : subd11_2 [0, 3] = true := by decide +kernel
theorem subd11_2_24 : subd11_2 [1, -4] = true := by decide +kernel
theorem subd11_2_25 : subd11_2 [1, -3] = true := by decide +kernel
theorem subd11_2_26 : subd11_2 [1, -2] = true := by decide +kernel
theorem subd11_2_27 : subd11_2 [1, -1] = true := by decide +kernel
theorem subd11_2_28 : subd11_2 [1, 0] = true := by decide +kernel
theorem subd11_2_29 : subd11_2 [1, 1] = true := by decide +kernel
theorem subd11_2_30 : subd11_2 [1, 2] = true := by decide +kernel
theorem subd11_2_31 : subd11_2 [1, 3] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_cons.2 ⟨subd11_2_1, List.forall_mem_cons.2 ⟨subd11_2_2, List.forall_mem_cons.2 ⟨subd11_2_3, List.forall_mem_cons.2 ⟨subd11_2_4, List.forall_mem_cons.2 ⟨subd11_2_5, List.forall_mem_cons.2 ⟨subd11_2_6, List.forall_mem_cons.2 ⟨subd11_2_7, List.forall_mem_cons.2 ⟨subd11_2_8, List.forall_mem_cons.2 ⟨subd11_2_9, List.forall_mem_cons.2 ⟨subd11_2_10, List.forall_mem_cons.2 ⟨subd11_2_11, List.forall_mem_cons.2 ⟨subd11_2_12, List.forall_mem_cons.2 ⟨subd11_2_13, List.forall_mem_cons.2 ⟨subd11_2_14, List.forall_mem_cons.2 ⟨subd11_2_15, List.forall_mem_cons.2 ⟨subd11_2_16, List.forall_mem_cons.2 ⟨subd11_2_17, List.forall_mem_cons.2 ⟨subd11_2_18, List.forall_mem_cons.2 ⟨subd11_2_19, List.forall_mem_cons.2 ⟨subd11_2_20, List.forall_mem_cons.2 ⟨subd11_2_21, List.forall_mem_cons.2 ⟨subd11_2_22, List.forall_mem_cons.2 ⟨subd11_2_23, List.forall_mem_cons.2 ⟨subd11_2_24, List.forall_mem_cons.2 ⟨subd11_2_25, List.forall_mem_cons.2 ⟨subd11_2_26, List.forall_mem_cons.2 ⟨subd11_2_27, List.forall_mem_cons.2 ⟨subd11_2_28, List.forall_mem_cons.2 ⟨subd11_2_29, List.forall_mem_cons.2 ⟨subd11_2_30, List.forall_mem_cons.2 ⟨subd11_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_2_32 : subd11_2 [2, -4] = true := by decide +kernel
theorem subd11_2_33 : subd11_2 [2, -3] = true := by decide +kernel
theorem subd11_2_34 : subd11_2 [2, -2] = true := by decide +kernel
theorem subd11_2_35 : subd11_2 [2, -1] = true := by decide +kernel
theorem subd11_2_36 : subd11_2 [2, 0] = true := by decide +kernel
theorem subd11_2_37 : subd11_2 [2, 1] = true := by decide +kernel
theorem subd11_2_38 : subd11_2 [2, 2] = true := by decide +kernel
theorem subd11_2_39 : subd11_2 [3] = true := by decide +kernel
theorem sbd11_2_1 : ∀ q ∈ blkd11_2_1, subd11_2 q = true := by
  unfold blkd11_2_1
  exact List.forall_mem_cons.2 ⟨subd11_2_32, List.forall_mem_cons.2 ⟨subd11_2_33, List.forall_mem_cons.2 ⟨subd11_2_34, List.forall_mem_cons.2 ⟨subd11_2_35, List.forall_mem_cons.2 ⟨subd11_2_36, List.forall_mem_cons.2 ⟨subd11_2_37, List.forall_mem_cons.2 ⟨subd11_2_38, List.forall_mem_cons.2 ⟨subd11_2_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [-3] = true := by decide +kernel
theorem subd11_3_1 : subd11_3 [-2, -3] = true := by decide +kernel
theorem subd11_3_2 : subd11_3 [-2, -2] = true := by decide +kernel
theorem subd11_3_3 : subd11_3 [-2, -1] = true := by decide +kernel
theorem subd11_3_4 : subd11_3 [-2, 0] = true := by decide +kernel
theorem subd11_3_5 : subd11_3 [-2, 1] = true := by decide +kernel
theorem subd11_3_6 : subd11_3 [-2, 2] = true := by decide +kernel
theorem subd11_3_7 : subd11_3 [-1, -3] = true := by decide +kernel
theorem subd11_3_8 : subd11_3 [-1, -2] = true := by decide +kernel
theorem subd11_3_9 : subd11_3 [-1, -1] = true := by decide +kernel
theorem subd11_3_10 : subd11_3 [-1, 0] = true := by decide +kernel
theorem subd11_3_11 : subd11_3 [-1, 1] = true := by decide +kernel
theorem subd11_3_12 : subd11_3 [-1, 2] = true := by decide +kernel
theorem subd11_3_13 : subd11_3 [-1, 3] = true := by decide +kernel
theorem subd11_3_14 : subd11_3 [0, -4] = true := by decide +kernel
theorem subd11_3_15 : subd11_3 [0, -3] = true := by decide +kernel
theorem subd11_3_16 : subd11_3 [0, -2] = true := by decide +kernel
theorem subd11_3_17 : subd11_3 [0, -1] = true := by decide +kernel
theorem subd11_3_18 : subd11_3 [0, 0] = true := by decide +kernel
theorem subd11_3_19 : subd11_3 [0, 1] = true := by decide +kernel
theorem subd11_3_20 : subd11_3 [0, 2] = true := by decide +kernel
theorem subd11_3_21 : subd11_3 [0, 3] = true := by decide +kernel
theorem subd11_3_22 : subd11_3 [1, -4] = true := by decide +kernel
theorem subd11_3_23 : subd11_3 [1, -3] = true := by decide +kernel
theorem subd11_3_24 : subd11_3 [1, -2] = true := by decide +kernel
theorem subd11_3_25 : subd11_3 [1, -1] = true := by decide +kernel
theorem subd11_3_26 : subd11_3 [1, 0] = true := by decide +kernel
theorem subd11_3_27 : subd11_3 [1, 1] = true := by decide +kernel
theorem subd11_3_28 : subd11_3 [1, 2] = true := by decide +kernel
theorem subd11_3_29 : subd11_3 [2, -3] = true := by decide +kernel
theorem subd11_3_30 : subd11_3 [2, -2] = true := by decide +kernel
theorem subd11_3_31 : subd11_3 [2, -1] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_cons.2 ⟨subd11_3_1, List.forall_mem_cons.2 ⟨subd11_3_2, List.forall_mem_cons.2 ⟨subd11_3_3, List.forall_mem_cons.2 ⟨subd11_3_4, List.forall_mem_cons.2 ⟨subd11_3_5, List.forall_mem_cons.2 ⟨subd11_3_6, List.forall_mem_cons.2 ⟨subd11_3_7, List.forall_mem_cons.2 ⟨subd11_3_8, List.forall_mem_cons.2 ⟨subd11_3_9, List.forall_mem_cons.2 ⟨subd11_3_10, List.forall_mem_cons.2 ⟨subd11_3_11, List.forall_mem_cons.2 ⟨subd11_3_12, List.forall_mem_cons.2 ⟨subd11_3_13, List.forall_mem_cons.2 ⟨subd11_3_14, List.forall_mem_cons.2 ⟨subd11_3_15, List.forall_mem_cons.2 ⟨subd11_3_16, List.forall_mem_cons.2 ⟨subd11_3_17, List.forall_mem_cons.2 ⟨subd11_3_18, List.forall_mem_cons.2 ⟨subd11_3_19, List.forall_mem_cons.2 ⟨subd11_3_20, List.forall_mem_cons.2 ⟨subd11_3_21, List.forall_mem_cons.2 ⟨subd11_3_22, List.forall_mem_cons.2 ⟨subd11_3_23, List.forall_mem_cons.2 ⟨subd11_3_24, List.forall_mem_cons.2 ⟨subd11_3_25, List.forall_mem_cons.2 ⟨subd11_3_26, List.forall_mem_cons.2 ⟨subd11_3_27, List.forall_mem_cons.2 ⟨subd11_3_28, List.forall_mem_cons.2 ⟨subd11_3_29, List.forall_mem_cons.2 ⟨subd11_3_30, List.forall_mem_cons.2 ⟨subd11_3_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_3_32 : subd11_3 [2, 0] = true := by decide +kernel
theorem subd11_3_33 : subd11_3 [2, 1] = true := by decide +kernel
theorem subd11_3_34 : subd11_3 [2, 2] = true := by decide +kernel
theorem subd11_3_35 : subd11_3 [3] = true := by decide +kernel
theorem sbd11_3_1 : ∀ q ∈ blkd11_3_1, subd11_3 q = true := by
  unfold blkd11_3_1
  exact List.forall_mem_cons.2 ⟨subd11_3_32, List.forall_mem_cons.2 ⟨subd11_3_33, List.forall_mem_cons.2 ⟨subd11_3_34, List.forall_mem_cons.2 ⟨subd11_3_35, List.forall_mem_nil _⟩⟩⟩⟩
theorem ld_okd11_4 : ldCheck G d11_4.U d11_4.ms ldd11_4 = true := by decide +kernel
theorem pre_okd11_4 : subPre G cell11 d11_4 = true := by decide +kernel
theorem subd11_4_0 : subd11_4 [-3] = true := by decide +kernel
theorem subd11_4_1 : subd11_4 [-2, -3] = true := by decide +kernel
theorem subd11_4_2 : subd11_4 [-2, -2] = true := by decide +kernel
theorem subd11_4_3 : subd11_4 [-2, -1] = true := by decide +kernel
theorem subd11_4_4 : subd11_4 [-2, 0] = true := by decide +kernel
theorem subd11_4_5 : subd11_4 [-2, 1] = true := by decide +kernel
theorem subd11_4_6 : subd11_4 [-2, 2] = true := by decide +kernel
theorem subd11_4_7 : subd11_4 [-2, 3] = true := by decide +kernel
theorem subd11_4_8 : subd11_4 [-1, -4] = true := by decide +kernel
theorem subd11_4_9 : subd11_4 [-1, -3] = true := by decide +kernel
theorem subd11_4_10 : subd11_4 [-1, -2] = true := by decide +kernel
theorem subd11_4_11 : subd11_4 [-1, -1] = true := by decide +kernel
theorem subd11_4_12 : subd11_4 [-1, 0] = true := by decide +kernel
theorem subd11_4_13 : subd11_4 [-1, 1] = true := by decide +kernel
theorem subd11_4_14 : subd11_4 [-1, 2] = true := by decide +kernel
theorem subd11_4_15 : subd11_4 [-1, 3] = true := by decide +kernel
theorem subd11_4_16 : subd11_4 [0, -4] = true := by decide +kernel
theorem subd11_4_17 : subd11_4 [0, -3] = true := by decide +kernel
theorem subd11_4_18 : subd11_4 [0, -2] = true := by decide +kernel
theorem subd11_4_19 : subd11_4 [0, -1] = true := by decide +kernel
theorem subd11_4_20 : subd11_4 [0, 0] = true := by decide +kernel
theorem subd11_4_21 : subd11_4 [0, 1] = true := by decide +kernel
theorem subd11_4_22 : subd11_4 [0, 2] = true := by decide +kernel
theorem subd11_4_23 : subd11_4 [0, 3] = true := by decide +kernel
theorem subd11_4_24 : subd11_4 [1, -4] = true := by decide +kernel
theorem subd11_4_25 : subd11_4 [1, -3] = true := by decide +kernel
theorem subd11_4_26 : subd11_4 [1, -2] = true := by decide +kernel
theorem subd11_4_27 : subd11_4 [1, -1] = true := by decide +kernel
theorem subd11_4_28 : subd11_4 [1, 0] = true := by decide +kernel
theorem subd11_4_29 : subd11_4 [1, 1] = true := by decide +kernel
theorem subd11_4_30 : subd11_4 [1, 2] = true := by decide +kernel
theorem subd11_4_31 : subd11_4 [1, 3] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_cons.2 ⟨subd11_4_1, List.forall_mem_cons.2 ⟨subd11_4_2, List.forall_mem_cons.2 ⟨subd11_4_3, List.forall_mem_cons.2 ⟨subd11_4_4, List.forall_mem_cons.2 ⟨subd11_4_5, List.forall_mem_cons.2 ⟨subd11_4_6, List.forall_mem_cons.2 ⟨subd11_4_7, List.forall_mem_cons.2 ⟨subd11_4_8, List.forall_mem_cons.2 ⟨subd11_4_9, List.forall_mem_cons.2 ⟨subd11_4_10, List.forall_mem_cons.2 ⟨subd11_4_11, List.forall_mem_cons.2 ⟨subd11_4_12, List.forall_mem_cons.2 ⟨subd11_4_13, List.forall_mem_cons.2 ⟨subd11_4_14, List.forall_mem_cons.2 ⟨subd11_4_15, List.forall_mem_cons.2 ⟨subd11_4_16, List.forall_mem_cons.2 ⟨subd11_4_17, List.forall_mem_cons.2 ⟨subd11_4_18, List.forall_mem_cons.2 ⟨subd11_4_19, List.forall_mem_cons.2 ⟨subd11_4_20, List.forall_mem_cons.2 ⟨subd11_4_21, List.forall_mem_cons.2 ⟨subd11_4_22, List.forall_mem_cons.2 ⟨subd11_4_23, List.forall_mem_cons.2 ⟨subd11_4_24, List.forall_mem_cons.2 ⟨subd11_4_25, List.forall_mem_cons.2 ⟨subd11_4_26, List.forall_mem_cons.2 ⟨subd11_4_27, List.forall_mem_cons.2 ⟨subd11_4_28, List.forall_mem_cons.2 ⟨subd11_4_29, List.forall_mem_cons.2 ⟨subd11_4_30, List.forall_mem_cons.2 ⟨subd11_4_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_4_32 : subd11_4 [2, -4] = true := by decide +kernel
theorem subd11_4_33 : subd11_4 [2, -3] = true := by decide +kernel
theorem subd11_4_34 : subd11_4 [2, -2] = true := by decide +kernel
theorem subd11_4_35 : subd11_4 [2, -1] = true := by decide +kernel
theorem subd11_4_36 : subd11_4 [2, 0] = true := by decide +kernel
theorem subd11_4_37 : subd11_4 [2, 1] = true := by decide +kernel
theorem subd11_4_38 : subd11_4 [2, 2] = true := by decide +kernel
theorem subd11_4_39 : subd11_4 [3] = true := by decide +kernel
theorem sbd11_4_1 : ∀ q ∈ blkd11_4_1, subd11_4 q = true := by
  unfold blkd11_4_1
  exact List.forall_mem_cons.2 ⟨subd11_4_32, List.forall_mem_cons.2 ⟨subd11_4_33, List.forall_mem_cons.2 ⟨subd11_4_34, List.forall_mem_cons.2 ⟨subd11_4_35, List.forall_mem_cons.2 ⟨subd11_4_36, List.forall_mem_cons.2 ⟨subd11_4_37, List.forall_mem_cons.2 ⟨subd11_4_38, List.forall_mem_cons.2 ⟨subd11_4_39, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_5 : ldCheck G d11_5.U d11_5.ms ldd11_5 = true := by decide +kernel
theorem pre_okd11_5 : subPre G cell11 d11_5 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C128
