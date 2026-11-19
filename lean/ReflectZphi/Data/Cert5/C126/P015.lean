import ReflectZphi.Data.Cert5.C126.Base

namespace ReflectZphi.Data.Cert5.C126

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd14_3 : ldCheck G d14_3.U d14_3.ms ldd14_3 = true := by decide +kernel
theorem pre_okd14_3 : subPre G cell14 d14_3 = true := by decide +kernel
theorem subd14_3_0 : subd14_3 [] = true := by decide +kernel
theorem sbd14_3_0 : ∀ q ∈ blkd14_3_0, subd14_3 q = true := by
  unfold blkd14_3_0
  exact List.forall_mem_cons.2 ⟨subd14_3_0, List.forall_mem_nil _⟩
theorem ld_okd14_4 : ldCheck G d14_4.U d14_4.ms ldd14_4 = true := by decide +kernel
theorem pre_okd14_4 : subPre G cell14 d14_4 = true := by decide +kernel
theorem subd14_4_0 : subd14_4 [] = true := by decide +kernel
theorem sbd14_4_0 : ∀ q ∈ blkd14_4_0, subd14_4 q = true := by
  unfold blkd14_4_0
  exact List.forall_mem_cons.2 ⟨subd14_4_0, List.forall_mem_nil _⟩
theorem ld_okd14_5 : ldCheck G d14_5.U d14_5.ms ldd14_5 = true := by decide +kernel
theorem pre_okd14_5 : subPre G cell14 d14_5 = true := by decide +kernel
theorem subd14_5_0 : subd14_5 [] = true := by decide +kernel
theorem sbd14_5_0 : ∀ q ∈ blkd14_5_0, subd14_5 q = true := by
  unfold blkd14_5_0
  exact List.forall_mem_cons.2 ⟨subd14_5_0, List.forall_mem_nil _⟩
theorem ld_okd14_6 : ldCheck G d14_6.U d14_6.ms ldd14_6 = true := by decide +kernel
theorem pre_okd14_6 : subPre G cell14 d14_6 = true := by decide +kernel
theorem subd14_6_0 : subd14_6 [] = true := by decide +kernel
theorem sbd14_6_0 : ∀ q ∈ blkd14_6_0, subd14_6 q = true := by
  unfold blkd14_6_0
  exact List.forall_mem_cons.2 ⟨subd14_6_0, List.forall_mem_nil _⟩
theorem ld_okd14_7 : ldCheck G d14_7.U d14_7.ms ldd14_7 = true := by decide +kernel
theorem pre_okd14_7 : subPre G cell14 d14_7 = true := by decide +kernel
theorem subd14_7_0 : subd14_7 [] = true := by decide +kernel
theorem sbd14_7_0 : ∀ q ∈ blkd14_7_0, subd14_7 q = true := by
  unfold blkd14_7_0
  exact List.forall_mem_cons.2 ⟨subd14_7_0, List.forall_mem_nil _⟩
theorem ld_okd15_0 : ldCheck G d15_0.U d15_0.ms ldd15_0 = true := by decide +kernel
theorem pre_okd15_0 : subPre G cell15 d15_0 = true := by decide +kernel
theorem subd15_0_0 : subd15_0 [] = true := by decide +kernel
theorem sbd15_0_0 : ∀ q ∈ blkd15_0_0, subd15_0 q = true := by
  unfold blkd15_0_0
  exact List.forall_mem_cons.2 ⟨subd15_0_0, List.forall_mem_nil _⟩
theorem ld_okd15_1 : ldCheck G d15_1.U d15_1.ms ldd15_1 = true := by decide +kernel
theorem pre_okd15_1 : subPre G cell15 d15_1 = true := by decide +kernel
theorem subd15_1_0 : subd15_1 [] = true := by decide +kernel
theorem sbd15_1_0 : ∀ q ∈ blkd15_1_0, subd15_1 q = true := by
  unfold blkd15_1_0
  exact List.forall_mem_cons.2 ⟨subd15_1_0, List.forall_mem_nil _⟩
theorem ld_okd15_2 : ldCheck G d15_2.U d15_2.ms ldd15_2 = true := by decide +kernel
theorem pre_okd15_2 : subPre G cell15 d15_2 = true := by decide +kernel
theorem subd15_2_0 : subd15_2 [] = true := by decide +kernel
theorem sbd15_2_0 : ∀ q ∈ blkd15_2_0, subd15_2 q = true := by
  unfold blkd15_2_0
  exact List.forall_mem_cons.2 ⟨subd15_2_0, List.forall_mem_nil _⟩
theorem ld_okd15_3 : ldCheck G d15_3.U d15_3.ms ldd15_3 = true := by decide +kernel
theorem pre_okd15_3 : subPre G cell15 d15_3 = true := by decide +kernel
theorem subd15_3_0 : subd15_3 [] = true := by decide +kernel
theorem sbd15_3_0 : ∀ q ∈ blkd15_3_0, subd15_3 q = true := by
  unfold blkd15_3_0
  exact List.forall_mem_cons.2 ⟨subd15_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C126
