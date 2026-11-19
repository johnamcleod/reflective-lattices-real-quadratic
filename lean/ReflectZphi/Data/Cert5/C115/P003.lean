import ReflectZphi.Data.Cert5.C115.Base

namespace ReflectZphi.Data.Cert5.C115

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd2_3 : ldCheck G d2_3.U d2_3.ms ldd2_3 = true := by decide +kernel
theorem pre_okd2_3 : subPre G cell2 d2_3 = true := by decide +kernel
theorem subd2_3_0 : subd2_3 [] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_nil _⟩
theorem ld_okd2_4 : ldCheck G d2_4.U d2_4.ms ldd2_4 = true := by decide +kernel
theorem pre_okd2_4 : subPre G cell2 d2_4 = true := by decide +kernel
theorem subd2_4_0 : subd2_4 [-2] = true := by decide +kernel
theorem subd2_4_1 : subd2_4 [-1] = true := by decide +kernel
theorem subd2_4_2 : subd2_4 [0] = true := by decide +kernel
theorem subd2_4_3 : subd2_4 [1] = true := by decide +kernel
theorem subd2_4_4 : subd2_4 [2] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_cons.2 ⟨subd2_4_1, List.forall_mem_cons.2 ⟨subd2_4_2, List.forall_mem_cons.2 ⟨subd2_4_3, List.forall_mem_cons.2 ⟨subd2_4_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd2_5 : ldCheck G d2_5.U d2_5.ms ldd2_5 = true := by decide +kernel
theorem pre_okd2_5 : subPre G cell2 d2_5 = true := by decide +kernel
theorem subd2_5_0 : subd2_5 [] = true := by decide +kernel
theorem sbd2_5_0 : ∀ q ∈ blkd2_5_0, subd2_5 q = true := by
  unfold blkd2_5_0
  exact List.forall_mem_cons.2 ⟨subd2_5_0, List.forall_mem_nil _⟩
theorem ld_okd2_6 : ldCheck G d2_6.U d2_6.ms ldd2_6 = true := by decide +kernel
theorem pre_okd2_6 : subPre G cell2 d2_6 = true := by decide +kernel
theorem subd2_6_0 : subd2_6 [] = true := by decide +kernel
theorem sbd2_6_0 : ∀ q ∈ blkd2_6_0, subd2_6 q = true := by
  unfold blkd2_6_0
  exact List.forall_mem_cons.2 ⟨subd2_6_0, List.forall_mem_nil _⟩
theorem ld_okd2_7 : ldCheck G d2_7.U d2_7.ms ldd2_7 = true := by decide +kernel
theorem pre_okd2_7 : subPre G cell2 d2_7 = true := by decide +kernel
theorem subd2_7_0 : subd2_7 [] = true := by decide +kernel
theorem sbd2_7_0 : ∀ q ∈ blkd2_7_0, subd2_7 q = true := by
  unfold blkd2_7_0
  exact List.forall_mem_cons.2 ⟨subd2_7_0, List.forall_mem_nil _⟩
theorem ld_okd2_8 : ldCheck G d2_8.U d2_8.ms ldd2_8 = true := by decide +kernel
theorem pre_okd2_8 : subPre G cell2 d2_8 = true := by decide +kernel
theorem subd2_8_0 : subd2_8 [] = true := by decide +kernel
theorem sbd2_8_0 : ∀ q ∈ blkd2_8_0, subd2_8 q = true := by
  unfold blkd2_8_0
  exact List.forall_mem_cons.2 ⟨subd2_8_0, List.forall_mem_nil _⟩
theorem ld_okd2_9 : ldCheck G d2_9.U d2_9.ms ldd2_9 = true := by decide +kernel
theorem pre_okd2_9 : subPre G cell2 d2_9 = true := by decide +kernel
theorem subd2_9_0 : subd2_9 [] = true := by decide +kernel
theorem sbd2_9_0 : ∀ q ∈ blkd2_9_0, subd2_9 q = true := by
  unfold blkd2_9_0
  exact List.forall_mem_cons.2 ⟨subd2_9_0, List.forall_mem_nil _⟩
theorem ld_okd2_10 : ldCheck G d2_10.U d2_10.ms ldd2_10 = true := by decide +kernel
theorem pre_okd2_10 : subPre G cell2 d2_10 = true := by decide +kernel
theorem subd2_10_0 : subd2_10 [] = true := by decide +kernel
theorem sbd2_10_0 : ∀ q ∈ blkd2_10_0, subd2_10 q = true := by
  unfold blkd2_10_0
  exact List.forall_mem_cons.2 ⟨subd2_10_0, List.forall_mem_nil _⟩
theorem ld_okd2_11 : ldCheck G d2_11.U d2_11.ms ldd2_11 = true := by decide +kernel
theorem pre_okd2_11 : subPre G cell2 d2_11 = true := by decide +kernel
theorem subd2_11_0 : subd2_11 [] = true := by decide +kernel
theorem sbd2_11_0 : ∀ q ∈ blkd2_11_0, subd2_11 q = true := by
  unfold blkd2_11_0
  exact List.forall_mem_cons.2 ⟨subd2_11_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C115
