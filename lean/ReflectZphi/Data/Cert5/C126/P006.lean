import ReflectZphi.Data.Cert5.C126.Base

namespace ReflectZphi.Data.Cert5.C126

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_nil _⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [-2] = true := by decide +kernel
theorem subd6_2_1 : subd6_2 [-1] = true := by decide +kernel
theorem subd6_2_2 : subd6_2 [0] = true := by decide +kernel
theorem subd6_2_3 : subd6_2 [1] = true := by decide +kernel
theorem subd6_2_4 : subd6_2 [2] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_cons.2 ⟨subd6_2_1, List.forall_mem_cons.2 ⟨subd6_2_2, List.forall_mem_cons.2 ⟨subd6_2_3, List.forall_mem_cons.2 ⟨subd6_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_nil _⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-1] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [0] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [1] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd6_5 : ldCheck G d6_5.U d6_5.ms ldd6_5 = true := by decide +kernel
theorem pre_okd6_5 : subPre G cell6 d6_5 = true := by decide +kernel
theorem subd6_5_0 : subd6_5 [-1] = true := by decide +kernel
theorem subd6_5_1 : subd6_5 [0] = true := by decide +kernel
theorem subd6_5_2 : subd6_5 [1] = true := by decide +kernel
theorem sbd6_5_0 : ∀ q ∈ blkd6_5_0, subd6_5 q = true := by
  unfold blkd6_5_0
  exact List.forall_mem_cons.2 ⟨subd6_5_0, List.forall_mem_cons.2 ⟨subd6_5_1, List.forall_mem_cons.2 ⟨subd6_5_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd6_6 : ldCheck G d6_6.U d6_6.ms ldd6_6 = true := by decide +kernel
theorem pre_okd6_6 : subPre G cell6 d6_6 = true := by decide +kernel
theorem subd6_6_0 : subd6_6 [-2] = true := by decide +kernel
theorem subd6_6_1 : subd6_6 [-1] = true := by decide +kernel
theorem subd6_6_2 : subd6_6 [0] = true := by decide +kernel
theorem subd6_6_3 : subd6_6 [1] = true := by decide +kernel
theorem subd6_6_4 : subd6_6 [2] = true := by decide +kernel
theorem sbd6_6_0 : ∀ q ∈ blkd6_6_0, subd6_6 q = true := by
  unfold blkd6_6_0
  exact List.forall_mem_cons.2 ⟨subd6_6_0, List.forall_mem_cons.2 ⟨subd6_6_1, List.forall_mem_cons.2 ⟨subd6_6_2, List.forall_mem_cons.2 ⟨subd6_6_3, List.forall_mem_cons.2 ⟨subd6_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd6_7 : ldCheck G d6_7.U d6_7.ms ldd6_7 = true := by decide +kernel
theorem pre_okd6_7 : subPre G cell6 d6_7 = true := by decide +kernel
theorem subd6_7_0 : subd6_7 [-2] = true := by decide +kernel
theorem subd6_7_1 : subd6_7 [-1] = true := by decide +kernel
theorem subd6_7_2 : subd6_7 [0] = true := by decide +kernel
theorem subd6_7_3 : subd6_7 [1] = true := by decide +kernel
theorem subd6_7_4 : subd6_7 [2] = true := by decide +kernel
theorem sbd6_7_0 : ∀ q ∈ blkd6_7_0, subd6_7 q = true := by
  unfold blkd6_7_0
  exact List.forall_mem_cons.2 ⟨subd6_7_0, List.forall_mem_cons.2 ⟨subd6_7_1, List.forall_mem_cons.2 ⟨subd6_7_2, List.forall_mem_cons.2 ⟨subd6_7_3, List.forall_mem_cons.2 ⟨subd6_7_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C126
