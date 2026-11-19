import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd18_0 : ldCheck G d18_0.U d18_0.ms ldd18_0 = true := by decide +kernel
theorem pre_okd18_0 : subPre G cell18 d18_0 = true := by decide +kernel
theorem subd18_0_0 : subd18_0 [] = true := by decide +kernel
theorem sbd18_0_0 : ∀ q ∈ blkd18_0_0, subd18_0 q = true := by
  unfold blkd18_0_0
  exact List.forall_mem_cons.2 ⟨subd18_0_0, List.forall_mem_nil _⟩
theorem ld_okd18_1 : ldCheck G d18_1.U d18_1.ms ldd18_1 = true := by decide +kernel
theorem pre_okd18_1 : subPre G cell18 d18_1 = true := by decide +kernel
theorem subd18_1_0 : subd18_1 [] = true := by decide +kernel
theorem sbd18_1_0 : ∀ q ∈ blkd18_1_0, subd18_1 q = true := by
  unfold blkd18_1_0
  exact List.forall_mem_cons.2 ⟨subd18_1_0, List.forall_mem_nil _⟩
theorem ld_okd18_2 : ldCheck G d18_2.U d18_2.ms ldd18_2 = true := by decide +kernel
theorem pre_okd18_2 : subPre G cell18 d18_2 = true := by decide +kernel
theorem subd18_2_0 : subd18_2 [] = true := by decide +kernel
theorem sbd18_2_0 : ∀ q ∈ blkd18_2_0, subd18_2 q = true := by
  unfold blkd18_2_0
  exact List.forall_mem_cons.2 ⟨subd18_2_0, List.forall_mem_nil _⟩
theorem ld_okd18_3 : ldCheck G d18_3.U d18_3.ms ldd18_3 = true := by decide +kernel
theorem pre_okd18_3 : subPre G cell18 d18_3 = true := by decide +kernel
theorem subd18_3_0 : subd18_3 [-1] = true := by decide +kernel
theorem subd18_3_1 : subd18_3 [0] = true := by decide +kernel
theorem subd18_3_2 : subd18_3 [1] = true := by decide +kernel
theorem sbd18_3_0 : ∀ q ∈ blkd18_3_0, subd18_3 q = true := by
  unfold blkd18_3_0
  exact List.forall_mem_cons.2 ⟨subd18_3_0, List.forall_mem_cons.2 ⟨subd18_3_1, List.forall_mem_cons.2 ⟨subd18_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd18_4 : ldCheck G d18_4.U d18_4.ms ldd18_4 = true := by decide +kernel
theorem pre_okd18_4 : subPre G cell18 d18_4 = true := by decide +kernel
theorem subd18_4_0 : subd18_4 [] = true := by decide +kernel
theorem sbd18_4_0 : ∀ q ∈ blkd18_4_0, subd18_4 q = true := by
  unfold blkd18_4_0
  exact List.forall_mem_cons.2 ⟨subd18_4_0, List.forall_mem_nil _⟩
theorem ld_okd18_5 : ldCheck G d18_5.U d18_5.ms ldd18_5 = true := by decide +kernel
theorem pre_okd18_5 : subPre G cell18 d18_5 = true := by decide +kernel
theorem subd18_5_0 : subd18_5 [] = true := by decide +kernel
theorem sbd18_5_0 : ∀ q ∈ blkd18_5_0, subd18_5 q = true := by
  unfold blkd18_5_0
  exact List.forall_mem_cons.2 ⟨subd18_5_0, List.forall_mem_nil _⟩
theorem ld_okd18_6 : ldCheck G d18_6.U d18_6.ms ldd18_6 = true := by decide +kernel
theorem pre_okd18_6 : subPre G cell18 d18_6 = true := by decide +kernel
theorem subd18_6_0 : subd18_6 [] = true := by decide +kernel
theorem sbd18_6_0 : ∀ q ∈ blkd18_6_0, subd18_6 q = true := by
  unfold blkd18_6_0
  exact List.forall_mem_cons.2 ⟨subd18_6_0, List.forall_mem_nil _⟩
theorem ld_okd18_7 : ldCheck G d18_7.U d18_7.ms ldd18_7 = true := by decide +kernel
theorem pre_okd18_7 : subPre G cell18 d18_7 = true := by decide +kernel
theorem subd18_7_0 : subd18_7 [] = true := by decide +kernel
theorem sbd18_7_0 : ∀ q ∈ blkd18_7_0, subd18_7 q = true := by
  unfold blkd18_7_0
  exact List.forall_mem_cons.2 ⟨subd18_7_0, List.forall_mem_nil _⟩
theorem ld_okd19_0 : ldCheck G d19_0.U d19_0.ms ldd19_0 = true := by decide +kernel
theorem pre_okd19_0 : subPre G cell19 d19_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C132
