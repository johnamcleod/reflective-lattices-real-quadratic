import ReflectZphi.Data.Cert5.C088.Base

namespace ReflectZphi.Data.Cert5.C088

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

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
theorem ld_okd4_8 : ldCheck G d4_8.U d4_8.ms ldd4_8 = true := by decide +kernel
theorem pre_okd4_8 : subPre G cell4 d4_8 = true := by decide +kernel
theorem subd4_8_0 : subd4_8 [] = true := by decide +kernel
theorem sbd4_8_0 : ∀ q ∈ blkd4_8_0, subd4_8 q = true := by
  unfold blkd4_8_0
  exact List.forall_mem_cons.2 ⟨subd4_8_0, List.forall_mem_nil _⟩
theorem ld_okd4_9 : ldCheck G d4_9.U d4_9.ms ldd4_9 = true := by decide +kernel
theorem pre_okd4_9 : subPre G cell4 d4_9 = true := by decide +kernel
theorem subd4_9_0 : subd4_9 [] = true := by decide +kernel
theorem sbd4_9_0 : ∀ q ∈ blkd4_9_0, subd4_9 q = true := by
  unfold blkd4_9_0
  exact List.forall_mem_cons.2 ⟨subd4_9_0, List.forall_mem_nil _⟩
theorem ld_okd4_10 : ldCheck G d4_10.U d4_10.ms ldd4_10 = true := by decide +kernel
theorem pre_okd4_10 : subPre G cell4 d4_10 = true := by decide +kernel
theorem subd4_10_0 : subd4_10 [] = true := by decide +kernel
theorem sbd4_10_0 : ∀ q ∈ blkd4_10_0, subd4_10 q = true := by
  unfold blkd4_10_0
  exact List.forall_mem_cons.2 ⟨subd4_10_0, List.forall_mem_nil _⟩
theorem ld_okd4_11 : ldCheck G d4_11.U d4_11.ms ldd4_11 = true := by decide +kernel
theorem pre_okd4_11 : subPre G cell4 d4_11 = true := by decide +kernel
theorem subd4_11_0 : subd4_11 [-1] = true := by decide +kernel
theorem subd4_11_1 : subd4_11 [0] = true := by decide +kernel
theorem subd4_11_2 : subd4_11 [1] = true := by decide +kernel
theorem sbd4_11_0 : ∀ q ∈ blkd4_11_0, subd4_11 q = true := by
  unfold blkd4_11_0
  exact List.forall_mem_cons.2 ⟨subd4_11_0, List.forall_mem_cons.2 ⟨subd4_11_1, List.forall_mem_cons.2 ⟨subd4_11_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd4_12 : ldCheck G d4_12.U d4_12.ms ldd4_12 = true := by decide +kernel
theorem pre_okd4_12 : subPre G cell4 d4_12 = true := by decide +kernel
theorem subd4_12_0 : subd4_12 [] = true := by decide +kernel
theorem sbd4_12_0 : ∀ q ∈ blkd4_12_0, subd4_12 q = true := by
  unfold blkd4_12_0
  exact List.forall_mem_cons.2 ⟨subd4_12_0, List.forall_mem_nil _⟩
theorem ld_okd4_13 : ldCheck G d4_13.U d4_13.ms ldd4_13 = true := by decide +kernel
theorem pre_okd4_13 : subPre G cell4 d4_13 = true := by decide +kernel
theorem subd4_13_0 : subd4_13 [] = true := by decide +kernel
theorem sbd4_13_0 : ∀ q ∈ blkd4_13_0, subd4_13 q = true := by
  unfold blkd4_13_0
  exact List.forall_mem_cons.2 ⟨subd4_13_0, List.forall_mem_nil _⟩
theorem ld_okd5_0 : ldCheck G d5_0.U d5_0.ms ldd5_0 = true := by decide +kernel
theorem pre_okd5_0 : subPre G cell5 d5_0 = true := by decide +kernel
theorem subd5_0_0 : subd5_0 [] = true := by decide +kernel
theorem sbd5_0_0 : ∀ q ∈ blkd5_0_0, subd5_0 q = true := by
  unfold blkd5_0_0
  exact List.forall_mem_cons.2 ⟨subd5_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C088
