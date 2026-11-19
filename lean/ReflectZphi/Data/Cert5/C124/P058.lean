import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem ld_okd11_1 : ldCheck G d11_1.U d11_1.ms ldd11_1 = true := by decide +kernel
theorem pre_okd11_1 : subPre G cell11 d11_1 = true := by decide +kernel
theorem subd11_1_0 : subd11_1 [] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_nil _⟩
theorem ld_okd11_2 : ldCheck G d11_2.U d11_2.ms ldd11_2 = true := by decide +kernel
theorem pre_okd11_2 : subPre G cell11 d11_2 = true := by decide +kernel
theorem subd11_2_0 : subd11_2 [] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_nil _⟩
theorem ld_okd11_3 : ldCheck G d11_3.U d11_3.ms ldd11_3 = true := by decide +kernel
theorem pre_okd11_3 : subPre G cell11 d11_3 = true := by decide +kernel
theorem subd11_3_0 : subd11_3 [] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_nil _⟩
theorem ld_okd11_4 : ldCheck G d11_4.U d11_4.ms ldd11_4 = true := by decide +kernel
theorem pre_okd11_4 : subPre G cell11 d11_4 = true := by decide +kernel
theorem subd11_4_0 : subd11_4 [] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_nil _⟩
theorem ld_okd11_5 : ldCheck G d11_5.U d11_5.ms ldd11_5 = true := by decide +kernel
theorem pre_okd11_5 : subPre G cell11 d11_5 = true := by decide +kernel
theorem subd11_5_0 : subd11_5 [] = true := by decide +kernel
theorem sbd11_5_0 : ∀ q ∈ blkd11_5_0, subd11_5 q = true := by
  unfold blkd11_5_0
  exact List.forall_mem_cons.2 ⟨subd11_5_0, List.forall_mem_nil _⟩
theorem ld_okd11_6 : ldCheck G d11_6.U d11_6.ms ldd11_6 = true := by decide +kernel
theorem pre_okd11_6 : subPre G cell11 d11_6 = true := by decide +kernel
theorem subd11_6_0 : subd11_6 [-2] = true := by decide +kernel
theorem subd11_6_1 : subd11_6 [-1] = true := by decide +kernel
theorem subd11_6_2 : subd11_6 [0] = true := by decide +kernel
theorem subd11_6_3 : subd11_6 [1] = true := by decide +kernel
theorem subd11_6_4 : subd11_6 [2] = true := by decide +kernel
theorem sbd11_6_0 : ∀ q ∈ blkd11_6_0, subd11_6 q = true := by
  unfold blkd11_6_0
  exact List.forall_mem_cons.2 ⟨subd11_6_0, List.forall_mem_cons.2 ⟨subd11_6_1, List.forall_mem_cons.2 ⟨subd11_6_2, List.forall_mem_cons.2 ⟨subd11_6_3, List.forall_mem_cons.2 ⟨subd11_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd11_7 : ldCheck G d11_7.U d11_7.ms ldd11_7 = true := by decide +kernel
theorem pre_okd11_7 : subPre G cell11 d11_7 = true := by decide +kernel
theorem subd11_7_0 : subd11_7 [-2] = true := by decide +kernel
theorem subd11_7_1 : subd11_7 [-1] = true := by decide +kernel
theorem subd11_7_2 : subd11_7 [0, -3] = true := by decide +kernel
theorem subd11_7_3 : subd11_7 [0, -2] = true := by decide +kernel
theorem subd11_7_4 : subd11_7 [0, -1] = true := by decide +kernel
theorem subd11_7_5 : subd11_7 [0, 0] = true := by decide +kernel
theorem subd11_7_6 : subd11_7 [0, 1] = true := by decide +kernel
theorem subd11_7_7 : subd11_7 [0, 2] = true := by decide +kernel
theorem subd11_7_8 : subd11_7 [1] = true := by decide +kernel
theorem subd11_7_9 : subd11_7 [2] = true := by decide +kernel
theorem sbd11_7_0 : ∀ q ∈ blkd11_7_0, subd11_7 q = true := by
  unfold blkd11_7_0
  exact List.forall_mem_cons.2 ⟨subd11_7_0, List.forall_mem_cons.2 ⟨subd11_7_1, List.forall_mem_cons.2 ⟨subd11_7_2, List.forall_mem_cons.2 ⟨subd11_7_3, List.forall_mem_cons.2 ⟨subd11_7_4, List.forall_mem_cons.2 ⟨subd11_7_5, List.forall_mem_cons.2 ⟨subd11_7_6, List.forall_mem_cons.2 ⟨subd11_7_7, List.forall_mem_cons.2 ⟨subd11_7_8, List.forall_mem_cons.2 ⟨subd11_7_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd11_8 : ldCheck G d11_8.U d11_8.ms ldd11_8 = true := by decide +kernel
theorem pre_okd11_8 : subPre G cell11 d11_8 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C124
