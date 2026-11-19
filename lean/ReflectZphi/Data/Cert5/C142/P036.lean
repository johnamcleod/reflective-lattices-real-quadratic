import ReflectZphi.Data.Cert5.C142.Base

namespace ReflectZphi.Data.Cert5.C142

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd21_0 : ldCheck G d21_0.U d21_0.ms ldd21_0 = true := by decide +kernel
theorem pre_okd21_0 : subPre G cell21 d21_0 = true := by decide +kernel
theorem subd21_0_0 : subd21_0 [] = true := by decide +kernel
theorem sbd21_0_0 : ∀ q ∈ blkd21_0_0, subd21_0 q = true := by
  unfold blkd21_0_0
  exact List.forall_mem_cons.2 ⟨subd21_0_0, List.forall_mem_nil _⟩
theorem ld_okd21_1 : ldCheck G d21_1.U d21_1.ms ldd21_1 = true := by decide +kernel
theorem pre_okd21_1 : subPre G cell21 d21_1 = true := by decide +kernel
theorem subd21_1_0 : subd21_1 [] = true := by decide +kernel
theorem sbd21_1_0 : ∀ q ∈ blkd21_1_0, subd21_1 q = true := by
  unfold blkd21_1_0
  exact List.forall_mem_cons.2 ⟨subd21_1_0, List.forall_mem_nil _⟩
theorem ld_okd21_2 : ldCheck G d21_2.U d21_2.ms ldd21_2 = true := by decide +kernel
theorem pre_okd21_2 : subPre G cell21 d21_2 = true := by decide +kernel
theorem subd21_2_0 : subd21_2 [-1] = true := by decide +kernel
theorem subd21_2_1 : subd21_2 [0] = true := by decide +kernel
theorem subd21_2_2 : subd21_2 [1] = true := by decide +kernel
theorem sbd21_2_0 : ∀ q ∈ blkd21_2_0, subd21_2 q = true := by
  unfold blkd21_2_0
  exact List.forall_mem_cons.2 ⟨subd21_2_0, List.forall_mem_cons.2 ⟨subd21_2_1, List.forall_mem_cons.2 ⟨subd21_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd21_3 : ldCheck G d21_3.U d21_3.ms ldd21_3 = true := by decide +kernel
theorem pre_okd21_3 : subPre G cell21 d21_3 = true := by decide +kernel
theorem subd21_3_0 : subd21_3 [] = true := by decide +kernel
theorem sbd21_3_0 : ∀ q ∈ blkd21_3_0, subd21_3 q = true := by
  unfold blkd21_3_0
  exact List.forall_mem_cons.2 ⟨subd21_3_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C142
