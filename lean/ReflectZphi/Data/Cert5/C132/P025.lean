import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd20_1 : ldCheck G d20_1.U d20_1.ms ldd20_1 = true := by decide +kernel
theorem pre_okd20_1 : subPre G cell20 d20_1 = true := by decide +kernel
theorem subd20_1_0 : subd20_1 [] = true := by decide +kernel
theorem sbd20_1_0 : ∀ q ∈ blkd20_1_0, subd20_1 q = true := by
  unfold blkd20_1_0
  exact List.forall_mem_cons.2 ⟨subd20_1_0, List.forall_mem_nil _⟩
theorem ld_okd20_2 : ldCheck G d20_2.U d20_2.ms ldd20_2 = true := by decide +kernel
theorem pre_okd20_2 : subPre G cell20 d20_2 = true := by decide +kernel
theorem subd20_2_0 : subd20_2 [] = true := by decide +kernel
theorem sbd20_2_0 : ∀ q ∈ blkd20_2_0, subd20_2 q = true := by
  unfold blkd20_2_0
  exact List.forall_mem_cons.2 ⟨subd20_2_0, List.forall_mem_nil _⟩
theorem ld_okd20_3 : ldCheck G d20_3.U d20_3.ms ldd20_3 = true := by decide +kernel
theorem pre_okd20_3 : subPre G cell20 d20_3 = true := by decide +kernel
theorem subd20_3_0 : subd20_3 [-1] = true := by decide +kernel
theorem subd20_3_1 : subd20_3 [0] = true := by decide +kernel
theorem subd20_3_2 : subd20_3 [1] = true := by decide +kernel
theorem sbd20_3_0 : ∀ q ∈ blkd20_3_0, subd20_3 q = true := by
  unfold blkd20_3_0
  exact List.forall_mem_cons.2 ⟨subd20_3_0, List.forall_mem_cons.2 ⟨subd20_3_1, List.forall_mem_cons.2 ⟨subd20_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd20_4 : ldCheck G d20_4.U d20_4.ms ldd20_4 = true := by decide +kernel
theorem pre_okd20_4 : subPre G cell20 d20_4 = true := by decide +kernel
theorem subd20_4_0 : subd20_4 [] = true := by decide +kernel
theorem sbd20_4_0 : ∀ q ∈ blkd20_4_0, subd20_4 q = true := by
  unfold blkd20_4_0
  exact List.forall_mem_cons.2 ⟨subd20_4_0, List.forall_mem_nil _⟩
theorem ld_okd20_5 : ldCheck G d20_5.U d20_5.ms ldd20_5 = true := by decide +kernel
theorem pre_okd20_5 : subPre G cell20 d20_5 = true := by decide +kernel
theorem subd20_5_0 : subd20_5 [-2] = true := by decide +kernel
theorem subd20_5_1 : subd20_5 [-1] = true := by decide +kernel
theorem subd20_5_2 : subd20_5 [0] = true := by decide +kernel
theorem subd20_5_3 : subd20_5 [1] = true := by decide +kernel
theorem subd20_5_4 : subd20_5 [2] = true := by decide +kernel
theorem sbd20_5_0 : ∀ q ∈ blkd20_5_0, subd20_5 q = true := by
  unfold blkd20_5_0
  exact List.forall_mem_cons.2 ⟨subd20_5_0, List.forall_mem_cons.2 ⟨subd20_5_1, List.forall_mem_cons.2 ⟨subd20_5_2, List.forall_mem_cons.2 ⟨subd20_5_3, List.forall_mem_cons.2 ⟨subd20_5_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd20_6 : ldCheck G d20_6.U d20_6.ms ldd20_6 = true := by decide +kernel
theorem pre_okd20_6 : subPre G cell20 d20_6 = true := by decide +kernel
theorem subd20_6_0 : subd20_6 [] = true := by decide +kernel
theorem sbd20_6_0 : ∀ q ∈ blkd20_6_0, subd20_6 q = true := by
  unfold blkd20_6_0
  exact List.forall_mem_cons.2 ⟨subd20_6_0, List.forall_mem_nil _⟩
theorem ld_okd20_7 : ldCheck G d20_7.U d20_7.ms ldd20_7 = true := by decide +kernel
theorem pre_okd20_7 : subPre G cell20 d20_7 = true := by decide +kernel
theorem subd20_7_0 : subd20_7 [] = true := by decide +kernel
theorem sbd20_7_0 : ∀ q ∈ blkd20_7_0, subd20_7 q = true := by
  unfold blkd20_7_0
  exact List.forall_mem_cons.2 ⟨subd20_7_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C132
