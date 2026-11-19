import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd4_3 : ldCheck G d4_3.U d4_3.ms ldd4_3 = true := by decide +kernel
theorem pre_okd4_3 : subPre G cell4 d4_3 = true := by decide +kernel
theorem subd4_3_0 : subd4_3 [] = true := by decide +kernel
theorem sbd4_3_0 : ∀ q ∈ blkd4_3_0, subd4_3 q = true := by
  unfold blkd4_3_0
  exact List.forall_mem_cons.2 ⟨subd4_3_0, List.forall_mem_nil _⟩
theorem ld_okd4_4 : ldCheck G d4_4.U d4_4.ms ldd4_4 = true := by decide +kernel
theorem pre_okd4_4 : subPre G cell4 d4_4 = true := by decide +kernel
theorem subd4_4_0 : subd4_4 [] = true := by decide +kernel
theorem sbd4_4_0 : ∀ q ∈ blkd4_4_0, subd4_4 q = true := by
  unfold blkd4_4_0
  exact List.forall_mem_cons.2 ⟨subd4_4_0, List.forall_mem_nil _⟩
theorem ld_okd4_5 : ldCheck G d4_5.U d4_5.ms ldd4_5 = true := by decide +kernel
theorem pre_okd4_5 : subPre G cell4 d4_5 = true := by decide +kernel
theorem subd4_5_0 : subd4_5 [] = true := by decide +kernel
theorem sbd4_5_0 : ∀ q ∈ blkd4_5_0, subd4_5 q = true := by
  unfold blkd4_5_0
  exact List.forall_mem_cons.2 ⟨subd4_5_0, List.forall_mem_nil _⟩
theorem ld_okd4_6 : ldCheck G d4_6.U d4_6.ms ldd4_6 = true := by decide +kernel
theorem pre_okd4_6 : subPre G cell4 d4_6 = true := by decide +kernel
theorem subd4_6_0 : subd4_6 [-1] = true := by decide +kernel
theorem subd4_6_1 : subd4_6 [0] = true := by decide +kernel
theorem subd4_6_2 : subd4_6 [1] = true := by decide +kernel
theorem sbd4_6_0 : ∀ q ∈ blkd4_6_0, subd4_6 q = true := by
  unfold blkd4_6_0
  exact List.forall_mem_cons.2 ⟨subd4_6_0, List.forall_mem_cons.2 ⟨subd4_6_1, List.forall_mem_cons.2 ⟨subd4_6_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_7 : ldCheck G d4_7.U d4_7.ms ldd4_7 = true := by decide +kernel
theorem pre_okd4_7 : subPre G cell4 d4_7 = true := by decide +kernel
theorem subd4_7_0 : subd4_7 [-2] = true := by decide +kernel
theorem subd4_7_1 : subd4_7 [-1] = true := by decide +kernel
theorem subd4_7_2 : subd4_7 [0, -3] = true := by decide +kernel
theorem subd4_7_3 : subd4_7 [0, -2] = true := by decide +kernel
theorem subd4_7_4 : subd4_7 [0, -1] = true := by decide +kernel
theorem subd4_7_5 : subd4_7 [0, 0] = true := by decide +kernel
theorem subd4_7_6 : subd4_7 [0, 1] = true := by decide +kernel
theorem subd4_7_7 : subd4_7 [0, 2] = true := by decide +kernel
theorem subd4_7_8 : subd4_7 [1] = true := by decide +kernel
theorem subd4_7_9 : subd4_7 [2] = true := by decide +kernel
theorem sbd4_7_0 : ∀ q ∈ blkd4_7_0, subd4_7 q = true := by
  unfold blkd4_7_0
  exact List.forall_mem_cons.2 ⟨subd4_7_0, List.forall_mem_cons.2 ⟨subd4_7_1, List.forall_mem_cons.2 ⟨subd4_7_2, List.forall_mem_cons.2 ⟨subd4_7_3, List.forall_mem_cons.2 ⟨subd4_7_4, List.forall_mem_cons.2 ⟨subd4_7_5, List.forall_mem_cons.2 ⟨subd4_7_6, List.forall_mem_cons.2 ⟨subd4_7_7, List.forall_mem_cons.2 ⟨subd4_7_8, List.forall_mem_cons.2 ⟨subd4_7_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_8 : ldCheck G d4_8.U d4_8.ms ldd4_8 = true := by decide +kernel
theorem pre_okd4_8 : subPre G cell4 d4_8 = true := by decide +kernel
theorem subd4_8_0 : subd4_8 [-1, -2] = true := by decide +kernel
theorem subd4_8_1 : subd4_8 [-1, -1] = true := by decide +kernel
theorem subd4_8_2 : subd4_8 [-1, 0] = true := by decide +kernel
theorem subd4_8_3 : subd4_8 [0, -2] = true := by decide +kernel
theorem subd4_8_4 : subd4_8 [0, -1] = true := by decide +kernel
theorem subd4_8_5 : subd4_8 [0, 0, -9] = true := by decide +kernel
theorem subd4_8_6 : subd4_8 [0, 0, -8] = true := by decide +kernel
theorem subd4_8_7 : subd4_8 [0, 0, -7] = true := by decide +kernel
theorem subd4_8_8 : subd4_8 [0, 0, -6] = true := by decide +kernel
theorem subd4_8_9 : subd4_8 [0, 0, -5] = true := by decide +kernel
theorem subd4_8_10 : subd4_8 [0, 0, -4] = true := by decide +kernel
theorem subd4_8_11 : subd4_8 [0, 0, -3] = true := by decide +kernel
theorem subd4_8_12 : subd4_8 [0, 0, -2] = true := by decide +kernel
theorem subd4_8_13 : subd4_8 [0, 0, -1] = true := by decide +kernel
theorem subd4_8_14 : subd4_8 [0, 0, 0] = true := by decide +kernel
theorem subd4_8_15 : subd4_8 [0, 0, 1] = true := by decide +kernel
theorem subd4_8_16 : subd4_8 [0, 0, 2] = true := by decide +kernel
theorem subd4_8_17 : subd4_8 [0, 0, 3] = true := by decide +kernel
theorem subd4_8_18 : subd4_8 [0, 0, 4] = true := by decide +kernel
theorem subd4_8_19 : subd4_8 [0, 0, 5] = true := by decide +kernel
theorem subd4_8_20 : subd4_8 [0, 0, 6] = true := by decide +kernel
theorem subd4_8_21 : subd4_8 [0, 0, 7] = true := by decide +kernel
theorem subd4_8_22 : subd4_8 [0, 0, 8] = true := by decide +kernel
theorem subd4_8_23 : subd4_8 [0, 1] = true := by decide +kernel
theorem subd4_8_24 : subd4_8 [1, -1] = true := by decide +kernel
theorem subd4_8_25 : subd4_8 [1, 0] = true := by decide +kernel
theorem subd4_8_26 : subd4_8 [1, 1] = true := by decide +kernel
theorem sbd4_8_0 : ∀ q ∈ blkd4_8_0, subd4_8 q = true := by
  unfold blkd4_8_0
  exact List.forall_mem_cons.2 ⟨subd4_8_0, List.forall_mem_cons.2 ⟨subd4_8_1, List.forall_mem_cons.2 ⟨subd4_8_2, List.forall_mem_cons.2 ⟨subd4_8_3, List.forall_mem_cons.2 ⟨subd4_8_4, List.forall_mem_cons.2 ⟨subd4_8_5, List.forall_mem_cons.2 ⟨subd4_8_6, List.forall_mem_cons.2 ⟨subd4_8_7, List.forall_mem_cons.2 ⟨subd4_8_8, List.forall_mem_cons.2 ⟨subd4_8_9, List.forall_mem_cons.2 ⟨subd4_8_10, List.forall_mem_cons.2 ⟨subd4_8_11, List.forall_mem_cons.2 ⟨subd4_8_12, List.forall_mem_cons.2 ⟨subd4_8_13, List.forall_mem_cons.2 ⟨subd4_8_14, List.forall_mem_cons.2 ⟨subd4_8_15, List.forall_mem_cons.2 ⟨subd4_8_16, List.forall_mem_cons.2 ⟨subd4_8_17, List.forall_mem_cons.2 ⟨subd4_8_18, List.forall_mem_cons.2 ⟨subd4_8_19, List.forall_mem_cons.2 ⟨subd4_8_20, List.forall_mem_cons.2 ⟨subd4_8_21, List.forall_mem_cons.2 ⟨subd4_8_22, List.forall_mem_cons.2 ⟨subd4_8_23, List.forall_mem_cons.2 ⟨subd4_8_24, List.forall_mem_cons.2 ⟨subd4_8_25, List.forall_mem_cons.2 ⟨subd4_8_26, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd4_9 : ldCheck G d4_9.U d4_9.ms ldd4_9 = true := by decide +kernel
theorem pre_okd4_9 : subPre G cell4 d4_9 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
