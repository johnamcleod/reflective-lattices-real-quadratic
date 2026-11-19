import ReflectZphi.Data.Cert5.C126.Base

namespace ReflectZphi.Data.Cert5.C126

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd13_2 : ldCheck G d13_2.U d13_2.ms ldd13_2 = true := by decide +kernel
theorem pre_okd13_2 : subPre G cell13 d13_2 = true := by decide +kernel
theorem subd13_2_0 : subd13_2 [] = true := by decide +kernel
theorem sbd13_2_0 : ∀ q ∈ blkd13_2_0, subd13_2 q = true := by
  unfold blkd13_2_0
  exact List.forall_mem_cons.2 ⟨subd13_2_0, List.forall_mem_nil _⟩
theorem ld_okd13_3 : ldCheck G d13_3.U d13_3.ms ldd13_3 = true := by decide +kernel
theorem pre_okd13_3 : subPre G cell13 d13_3 = true := by decide +kernel
theorem subd13_3_0 : subd13_3 [] = true := by decide +kernel
theorem sbd13_3_0 : ∀ q ∈ blkd13_3_0, subd13_3 q = true := by
  unfold blkd13_3_0
  exact List.forall_mem_cons.2 ⟨subd13_3_0, List.forall_mem_nil _⟩
theorem ld_okd13_4 : ldCheck G d13_4.U d13_4.ms ldd13_4 = true := by decide +kernel
theorem pre_okd13_4 : subPre G cell13 d13_4 = true := by decide +kernel
theorem subd13_4_0 : subd13_4 [] = true := by decide +kernel
theorem sbd13_4_0 : ∀ q ∈ blkd13_4_0, subd13_4 q = true := by
  unfold blkd13_4_0
  exact List.forall_mem_cons.2 ⟨subd13_4_0, List.forall_mem_nil _⟩
theorem ld_okd13_5 : ldCheck G d13_5.U d13_5.ms ldd13_5 = true := by decide +kernel
theorem pre_okd13_5 : subPre G cell13 d13_5 = true := by decide +kernel
theorem subd13_5_0 : subd13_5 [] = true := by decide +kernel
theorem sbd13_5_0 : ∀ q ∈ blkd13_5_0, subd13_5 q = true := by
  unfold blkd13_5_0
  exact List.forall_mem_cons.2 ⟨subd13_5_0, List.forall_mem_nil _⟩
theorem ld_okd13_6 : ldCheck G d13_6.U d13_6.ms ldd13_6 = true := by decide +kernel
theorem pre_okd13_6 : subPre G cell13 d13_6 = true := by decide +kernel
theorem subd13_6_0 : subd13_6 [] = true := by decide +kernel
theorem sbd13_6_0 : ∀ q ∈ blkd13_6_0, subd13_6 q = true := by
  unfold blkd13_6_0
  exact List.forall_mem_cons.2 ⟨subd13_6_0, List.forall_mem_nil _⟩
theorem ld_okd13_7 : ldCheck G d13_7.U d13_7.ms ldd13_7 = true := by decide +kernel
theorem pre_okd13_7 : subPre G cell13 d13_7 = true := by decide +kernel
theorem subd13_7_0 : subd13_7 [] = true := by decide +kernel
theorem sbd13_7_0 : ∀ q ∈ blkd13_7_0, subd13_7 q = true := by
  unfold blkd13_7_0
  exact List.forall_mem_cons.2 ⟨subd13_7_0, List.forall_mem_nil _⟩
theorem ld_okd14_0 : ldCheck G d14_0.U d14_0.ms ldd14_0 = true := by decide +kernel
theorem pre_okd14_0 : subPre G cell14 d14_0 = true := by decide +kernel
theorem subd14_0_0 : subd14_0 [] = true := by decide +kernel
theorem sbd14_0_0 : ∀ q ∈ blkd14_0_0, subd14_0 q = true := by
  unfold blkd14_0_0
  exact List.forall_mem_cons.2 ⟨subd14_0_0, List.forall_mem_nil _⟩
theorem ld_okd14_1 : ldCheck G d14_1.U d14_1.ms ldd14_1 = true := by decide +kernel
theorem pre_okd14_1 : subPre G cell14 d14_1 = true := by decide +kernel
theorem subd14_1_0 : subd14_1 [] = true := by decide +kernel
theorem sbd14_1_0 : ∀ q ∈ blkd14_1_0, subd14_1 q = true := by
  unfold blkd14_1_0
  exact List.forall_mem_cons.2 ⟨subd14_1_0, List.forall_mem_nil _⟩
theorem ld_okd14_2 : ldCheck G d14_2.U d14_2.ms ldd14_2 = true := by decide +kernel
theorem pre_okd14_2 : subPre G cell14 d14_2 = true := by decide +kernel
theorem subd14_2_0 : subd14_2 [] = true := by decide +kernel
theorem sbd14_2_0 : ∀ q ∈ blkd14_2_0, subd14_2 q = true := by
  unfold blkd14_2_0
  exact List.forall_mem_cons.2 ⟨subd14_2_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C126
