import ReflectZphi.Data.Cert5.C077.Base

namespace ReflectZphi.Data.Cert5.C077

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_3_416 : subd10_3 [4, -2] = true := by decide +kernel
theorem subd10_3_417 : subd10_3 [4, -1] = true := by decide +kernel
theorem subd10_3_418 : subd10_3 [4, 0] = true := by decide +kernel
theorem subd10_3_419 : subd10_3 [4, 1] = true := by decide +kernel
theorem subd10_3_420 : subd10_3 [4, 2] = true := by decide +kernel
theorem subd10_3_421 : subd10_3 [4, 3] = true := by decide +kernel
theorem subd10_3_422 : subd10_3 [4, 4] = true := by decide +kernel
theorem subd10_3_423 : subd10_3 [4, 5] = true := by decide +kernel
theorem subd10_3_424 : subd10_3 [5, -6] = true := by decide +kernel
theorem subd10_3_425 : subd10_3 [5, -5] = true := by decide +kernel
theorem subd10_3_426 : subd10_3 [5, -4] = true := by decide +kernel
theorem subd10_3_427 : subd10_3 [5, -3] = true := by decide +kernel
theorem subd10_3_428 : subd10_3 [5, -2] = true := by decide +kernel
theorem subd10_3_429 : subd10_3 [5, -1] = true := by decide +kernel
theorem subd10_3_430 : subd10_3 [5, 0] = true := by decide +kernel
theorem subd10_3_431 : subd10_3 [5, 1] = true := by decide +kernel
theorem subd10_3_432 : subd10_3 [5, 2] = true := by decide +kernel
theorem subd10_3_433 : subd10_3 [5, 3] = true := by decide +kernel
theorem subd10_3_434 : subd10_3 [6] = true := by decide +kernel
theorem sbd10_3_13 : ∀ q ∈ blkd10_3_13, subd10_3 q = true := by
  unfold blkd10_3_13
  exact List.forall_mem_cons.2 ⟨subd10_3_416, List.forall_mem_cons.2 ⟨subd10_3_417, List.forall_mem_cons.2 ⟨subd10_3_418, List.forall_mem_cons.2 ⟨subd10_3_419, List.forall_mem_cons.2 ⟨subd10_3_420, List.forall_mem_cons.2 ⟨subd10_3_421, List.forall_mem_cons.2 ⟨subd10_3_422, List.forall_mem_cons.2 ⟨subd10_3_423, List.forall_mem_cons.2 ⟨subd10_3_424, List.forall_mem_cons.2 ⟨subd10_3_425, List.forall_mem_cons.2 ⟨subd10_3_426, List.forall_mem_cons.2 ⟨subd10_3_427, List.forall_mem_cons.2 ⟨subd10_3_428, List.forall_mem_cons.2 ⟨subd10_3_429, List.forall_mem_cons.2 ⟨subd10_3_430, List.forall_mem_cons.2 ⟨subd10_3_431, List.forall_mem_cons.2 ⟨subd10_3_432, List.forall_mem_cons.2 ⟨subd10_3_433, List.forall_mem_cons.2 ⟨subd10_3_434, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_0 : ldCheck G d11_0.U d11_0.ms ldd11_0 = true := by decide +kernel
theorem pre_okd11_0 : subPre G cell11 d11_0 = true := by decide +kernel
theorem subd11_0_0 : subd11_0 [-4] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [-3, -5] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [-3, -4] = true := by decide +kernel
theorem subd11_0_3 : subd11_0 [-3, -3] = true := by decide +kernel
theorem subd11_0_4 : subd11_0 [-3, -2] = true := by decide +kernel
theorem subd11_0_5 : subd11_0 [-3, -1] = true := by decide +kernel
theorem subd11_0_6 : subd11_0 [-3, 0] = true := by decide +kernel
theorem subd11_0_7 : subd11_0 [-3, 1] = true := by decide +kernel
theorem subd11_0_8 : subd11_0 [-3, 2] = true := by decide +kernel
theorem subd11_0_9 : subd11_0 [-2, -5] = true := by decide +kernel
theorem subd11_0_10 : subd11_0 [-2, -4] = true := by decide +kernel
theorem subd11_0_11 : subd11_0 [-2, -3] = true := by decide +kernel
theorem subd11_0_12 : subd11_0 [-2, -2] = true := by decide +kernel
theorem subd11_0_13 : subd11_0 [-2, -1] = true := by decide +kernel
theorem subd11_0_14 : subd11_0 [-2, 0] = true := by decide +kernel
theorem subd11_0_15 : subd11_0 [-2, 1] = true := by decide +kernel
theorem subd11_0_16 : subd11_0 [-2, 2] = true := by decide +kernel
theorem subd11_0_17 : subd11_0 [-2, 3] = true := by decide +kernel
theorem subd11_0_18 : subd11_0 [-1, -5] = true := by decide +kernel
theorem subd11_0_19 : subd11_0 [-1, -4] = true := by decide +kernel
theorem subd11_0_20 : subd11_0 [-1, -3] = true := by decide +kernel
theorem subd11_0_21 : subd11_0 [-1, -2] = true := by decide +kernel
theorem subd11_0_22 : subd11_0 [-1, -1] = true := by decide +kernel
theorem subd11_0_23 : subd11_0 [-1, 0] = true := by decide +kernel
theorem subd11_0_24 : subd11_0 [-1, 1] = true := by decide +kernel
theorem subd11_0_25 : subd11_0 [-1, 2] = true := by decide +kernel
theorem subd11_0_26 : subd11_0 [-1, 3] = true := by decide +kernel
theorem subd11_0_27 : subd11_0 [-1, 4] = true := by decide +kernel
theorem subd11_0_28 : subd11_0 [0, -5] = true := by decide +kernel
theorem subd11_0_29 : subd11_0 [0, -4] = true := by decide +kernel
theorem subd11_0_30 : subd11_0 [0, -3] = true := by decide +kernel
theorem subd11_0_31 : subd11_0 [0, -2] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_cons.2 ⟨subd11_0_3, List.forall_mem_cons.2 ⟨subd11_0_4, List.forall_mem_cons.2 ⟨subd11_0_5, List.forall_mem_cons.2 ⟨subd11_0_6, List.forall_mem_cons.2 ⟨subd11_0_7, List.forall_mem_cons.2 ⟨subd11_0_8, List.forall_mem_cons.2 ⟨subd11_0_9, List.forall_mem_cons.2 ⟨subd11_0_10, List.forall_mem_cons.2 ⟨subd11_0_11, List.forall_mem_cons.2 ⟨subd11_0_12, List.forall_mem_cons.2 ⟨subd11_0_13, List.forall_mem_cons.2 ⟨subd11_0_14, List.forall_mem_cons.2 ⟨subd11_0_15, List.forall_mem_cons.2 ⟨subd11_0_16, List.forall_mem_cons.2 ⟨subd11_0_17, List.forall_mem_cons.2 ⟨subd11_0_18, List.forall_mem_cons.2 ⟨subd11_0_19, List.forall_mem_cons.2 ⟨subd11_0_20, List.forall_mem_cons.2 ⟨subd11_0_21, List.forall_mem_cons.2 ⟨subd11_0_22, List.forall_mem_cons.2 ⟨subd11_0_23, List.forall_mem_cons.2 ⟨subd11_0_24, List.forall_mem_cons.2 ⟨subd11_0_25, List.forall_mem_cons.2 ⟨subd11_0_26, List.forall_mem_cons.2 ⟨subd11_0_27, List.forall_mem_cons.2 ⟨subd11_0_28, List.forall_mem_cons.2 ⟨subd11_0_29, List.forall_mem_cons.2 ⟨subd11_0_30, List.forall_mem_cons.2 ⟨subd11_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_32 : subd11_0 [0, -1] = true := by decide +kernel
theorem subd11_0_33 : subd11_0 [0, 0] = true := by decide +kernel
theorem subd11_0_34 : subd11_0 [0, 1] = true := by decide +kernel
theorem subd11_0_35 : subd11_0 [0, 2] = true := by decide +kernel
theorem subd11_0_36 : subd11_0 [0, 3] = true := by decide +kernel
theorem subd11_0_37 : subd11_0 [0, 4] = true := by decide +kernel
theorem subd11_0_38 : subd11_0 [1, -5] = true := by decide +kernel
theorem subd11_0_39 : subd11_0 [1, -4] = true := by decide +kernel
theorem subd11_0_40 : subd11_0 [1, -3] = true := by decide +kernel
theorem subd11_0_41 : subd11_0 [1, -2] = true := by decide +kernel
theorem subd11_0_42 : subd11_0 [1, -1] = true := by decide +kernel
theorem subd11_0_43 : subd11_0 [1, 0] = true := by decide +kernel
theorem subd11_0_44 : subd11_0 [1, 1] = true := by decide +kernel
theorem subd11_0_45 : subd11_0 [1, 2] = true := by decide +kernel
theorem subd11_0_46 : subd11_0 [1, 3] = true := by decide +kernel
theorem subd11_0_47 : subd11_0 [1, 4] = true := by decide +kernel
theorem subd11_0_48 : subd11_0 [2, -4] = true := by decide +kernel
theorem subd11_0_49 : subd11_0 [2, -3] = true := by decide +kernel
theorem subd11_0_50 : subd11_0 [2, -2] = true := by decide +kernel
theorem subd11_0_51 : subd11_0 [2, -1] = true := by decide +kernel
theorem subd11_0_52 : subd11_0 [2, 0] = true := by decide +kernel
theorem subd11_0_53 : subd11_0 [2, 1] = true := by decide +kernel
theorem subd11_0_54 : subd11_0 [2, 2] = true := by decide +kernel
theorem subd11_0_55 : subd11_0 [2, 3] = true := by decide +kernel
theorem subd11_0_56 : subd11_0 [2, 4] = true := by decide +kernel
theorem subd11_0_57 : subd11_0 [3, -3] = true := by decide +kernel
theorem subd11_0_58 : subd11_0 [3, -2] = true := by decide +kernel
theorem subd11_0_59 : subd11_0 [3, -1] = true := by decide +kernel
theorem subd11_0_60 : subd11_0 [3, 0] = true := by decide +kernel
theorem subd11_0_61 : subd11_0 [3, 1] = true := by decide +kernel
theorem subd11_0_62 : subd11_0 [3, 2] = true := by decide +kernel
theorem subd11_0_63 : subd11_0 [3, 3] = true := by decide +kernel
theorem sbd11_0_1 : ∀ q ∈ blkd11_0_1, subd11_0 q = true := by
  unfold blkd11_0_1
  exact List.forall_mem_cons.2 ⟨subd11_0_32, List.forall_mem_cons.2 ⟨subd11_0_33, List.forall_mem_cons.2 ⟨subd11_0_34, List.forall_mem_cons.2 ⟨subd11_0_35, List.forall_mem_cons.2 ⟨subd11_0_36, List.forall_mem_cons.2 ⟨subd11_0_37, List.forall_mem_cons.2 ⟨subd11_0_38, List.forall_mem_cons.2 ⟨subd11_0_39, List.forall_mem_cons.2 ⟨subd11_0_40, List.forall_mem_cons.2 ⟨subd11_0_41, List.forall_mem_cons.2 ⟨subd11_0_42, List.forall_mem_cons.2 ⟨subd11_0_43, List.forall_mem_cons.2 ⟨subd11_0_44, List.forall_mem_cons.2 ⟨subd11_0_45, List.forall_mem_cons.2 ⟨subd11_0_46, List.forall_mem_cons.2 ⟨subd11_0_47, List.forall_mem_cons.2 ⟨subd11_0_48, List.forall_mem_cons.2 ⟨subd11_0_49, List.forall_mem_cons.2 ⟨subd11_0_50, List.forall_mem_cons.2 ⟨subd11_0_51, List.forall_mem_cons.2 ⟨subd11_0_52, List.forall_mem_cons.2 ⟨subd11_0_53, List.forall_mem_cons.2 ⟨subd11_0_54, List.forall_mem_cons.2 ⟨subd11_0_55, List.forall_mem_cons.2 ⟨subd11_0_56, List.forall_mem_cons.2 ⟨subd11_0_57, List.forall_mem_cons.2 ⟨subd11_0_58, List.forall_mem_cons.2 ⟨subd11_0_59, List.forall_mem_cons.2 ⟨subd11_0_60, List.forall_mem_cons.2 ⟨subd11_0_61, List.forall_mem_cons.2 ⟨subd11_0_62, List.forall_mem_cons.2 ⟨subd11_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd11_0_64 : subd11_0 [3, 4] = true := by decide +kernel
theorem subd11_0_65 : subd11_0 [4] = true := by decide +kernel
theorem sbd11_0_2 : ∀ q ∈ blkd11_0_2, subd11_0 q = true := by
  unfold blkd11_0_2
  exact List.forall_mem_cons.2 ⟨subd11_0_64, List.forall_mem_cons.2 ⟨subd11_0_65, List.forall_mem_nil _⟩⟩
theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C077
