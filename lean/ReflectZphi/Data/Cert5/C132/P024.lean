import ReflectZphi.Data.Cert5.C132.Base

namespace ReflectZphi.Data.Cert5.C132

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_0_0 : subd19_0 [] = true := by decide +kernel
theorem sbd19_0_0 : ∀ q ∈ blkd19_0_0, subd19_0 q = true := by
  unfold blkd19_0_0
  exact List.forall_mem_cons.2 ⟨subd19_0_0, List.forall_mem_nil _⟩
theorem ld_okd19_1 : ldCheck G d19_1.U d19_1.ms ldd19_1 = true := by decide +kernel
theorem pre_okd19_1 : subPre G cell19 d19_1 = true := by decide +kernel
theorem subd19_1_0 : subd19_1 [] = true := by decide +kernel
theorem sbd19_1_0 : ∀ q ∈ blkd19_1_0, subd19_1 q = true := by
  unfold blkd19_1_0
  exact List.forall_mem_cons.2 ⟨subd19_1_0, List.forall_mem_nil _⟩
theorem ld_okd19_2 : ldCheck G d19_2.U d19_2.ms ldd19_2 = true := by decide +kernel
theorem pre_okd19_2 : subPre G cell19 d19_2 = true := by decide +kernel
theorem subd19_2_0 : subd19_2 [] = true := by decide +kernel
theorem sbd19_2_0 : ∀ q ∈ blkd19_2_0, subd19_2 q = true := by
  unfold blkd19_2_0
  exact List.forall_mem_cons.2 ⟨subd19_2_0, List.forall_mem_nil _⟩
theorem ld_okd19_3 : ldCheck G d19_3.U d19_3.ms ldd19_3 = true := by decide +kernel
theorem pre_okd19_3 : subPre G cell19 d19_3 = true := by decide +kernel
theorem subd19_3_0 : subd19_3 [-1] = true := by decide +kernel
theorem subd19_3_1 : subd19_3 [0] = true := by decide +kernel
theorem subd19_3_2 : subd19_3 [1] = true := by decide +kernel
theorem sbd19_3_0 : ∀ q ∈ blkd19_3_0, subd19_3 q = true := by
  unfold blkd19_3_0
  exact List.forall_mem_cons.2 ⟨subd19_3_0, List.forall_mem_cons.2 ⟨subd19_3_1, List.forall_mem_cons.2 ⟨subd19_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd19_4 : ldCheck G d19_4.U d19_4.ms ldd19_4 = true := by decide +kernel
theorem pre_okd19_4 : subPre G cell19 d19_4 = true := by decide +kernel
theorem subd19_4_0 : subd19_4 [] = true := by decide +kernel
theorem sbd19_4_0 : ∀ q ∈ blkd19_4_0, subd19_4 q = true := by
  unfold blkd19_4_0
  exact List.forall_mem_cons.2 ⟨subd19_4_0, List.forall_mem_nil _⟩
theorem ld_okd19_5 : ldCheck G d19_5.U d19_5.ms ldd19_5 = true := by decide +kernel
theorem pre_okd19_5 : subPre G cell19 d19_5 = true := by decide +kernel
theorem subd19_5_0 : subd19_5 [] = true := by decide +kernel
theorem sbd19_5_0 : ∀ q ∈ blkd19_5_0, subd19_5 q = true := by
  unfold blkd19_5_0
  exact List.forall_mem_cons.2 ⟨subd19_5_0, List.forall_mem_nil _⟩
theorem ld_okd19_6 : ldCheck G d19_6.U d19_6.ms ldd19_6 = true := by decide +kernel
theorem pre_okd19_6 : subPre G cell19 d19_6 = true := by decide +kernel
theorem subd19_6_0 : subd19_6 [] = true := by decide +kernel
theorem sbd19_6_0 : ∀ q ∈ blkd19_6_0, subd19_6 q = true := by
  unfold blkd19_6_0
  exact List.forall_mem_cons.2 ⟨subd19_6_0, List.forall_mem_nil _⟩
theorem ld_okd19_7 : ldCheck G d19_7.U d19_7.ms ldd19_7 = true := by decide +kernel
theorem pre_okd19_7 : subPre G cell19 d19_7 = true := by decide +kernel
theorem subd19_7_0 : subd19_7 [] = true := by decide +kernel
theorem sbd19_7_0 : ∀ q ∈ blkd19_7_0, subd19_7 q = true := by
  unfold blkd19_7_0
  exact List.forall_mem_cons.2 ⟨subd19_7_0, List.forall_mem_nil _⟩
theorem ld_okd20_0 : ldCheck G d20_0.U d20_0.ms ldd20_0 = true := by decide +kernel
theorem pre_okd20_0 : subPre G cell20 d20_0 = true := by decide +kernel
theorem subd20_0_0 : subd20_0 [] = true := by decide +kernel
theorem sbd20_0_0 : ∀ q ∈ blkd20_0_0, subd20_0 q = true := by
  unfold blkd20_0_0
  exact List.forall_mem_cons.2 ⟨subd20_0_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C132
