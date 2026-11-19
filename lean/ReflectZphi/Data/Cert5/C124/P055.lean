import ReflectZphi.Data.Cert5.C124.Base

namespace ReflectZphi.Data.Cert5.C124

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_14_64 : subd9_14 [2, 2] = true := by decide +kernel
theorem subd9_14_65 : subd9_14 [2, 3] = true := by decide +kernel
theorem subd9_14_66 : subd9_14 [2, 4] = true := by decide +kernel
theorem subd9_14_67 : subd9_14 [3, -5] = true := by decide +kernel
theorem subd9_14_68 : subd9_14 [3, -4] = true := by decide +kernel
theorem subd9_14_69 : subd9_14 [3, -3] = true := by decide +kernel
theorem subd9_14_70 : subd9_14 [3, -2] = true := by decide +kernel
theorem subd9_14_71 : subd9_14 [3, -1] = true := by decide +kernel
theorem subd9_14_72 : subd9_14 [3, 0] = true := by decide +kernel
theorem subd9_14_73 : subd9_14 [3, 1] = true := by decide +kernel
theorem subd9_14_74 : subd9_14 [3, 2] = true := by decide +kernel
theorem subd9_14_75 : subd9_14 [3, 3] = true := by decide +kernel
theorem subd9_14_76 : subd9_14 [4, -4] = true := by decide +kernel
theorem subd9_14_77 : subd9_14 [4, -3] = true := by decide +kernel
theorem subd9_14_78 : subd9_14 [4, -2] = true := by decide +kernel
theorem subd9_14_79 : subd9_14 [4, -1] = true := by decide +kernel
theorem subd9_14_80 : subd9_14 [4, 0] = true := by decide +kernel
theorem subd9_14_81 : subd9_14 [4, 1] = true := by decide +kernel
theorem subd9_14_82 : subd9_14 [4, 2] = true := by decide +kernel
theorem subd9_14_83 : subd9_14 [5] = true := by decide +kernel
theorem sbd9_14_2 : ∀ q ∈ blkd9_14_2, subd9_14 q = true := by
  unfold blkd9_14_2
  exact List.forall_mem_cons.2 ⟨subd9_14_64, List.forall_mem_cons.2 ⟨subd9_14_65, List.forall_mem_cons.2 ⟨subd9_14_66, List.forall_mem_cons.2 ⟨subd9_14_67, List.forall_mem_cons.2 ⟨subd9_14_68, List.forall_mem_cons.2 ⟨subd9_14_69, List.forall_mem_cons.2 ⟨subd9_14_70, List.forall_mem_cons.2 ⟨subd9_14_71, List.forall_mem_cons.2 ⟨subd9_14_72, List.forall_mem_cons.2 ⟨subd9_14_73, List.forall_mem_cons.2 ⟨subd9_14_74, List.forall_mem_cons.2 ⟨subd9_14_75, List.forall_mem_cons.2 ⟨subd9_14_76, List.forall_mem_cons.2 ⟨subd9_14_77, List.forall_mem_cons.2 ⟨subd9_14_78, List.forall_mem_cons.2 ⟨subd9_14_79, List.forall_mem_cons.2 ⟨subd9_14_80, List.forall_mem_cons.2 ⟨subd9_14_81, List.forall_mem_cons.2 ⟨subd9_14_82, List.forall_mem_cons.2 ⟨subd9_14_83, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd10_0 : ldCheck G d10_0.U d10_0.ms ldd10_0 = true := by decide +kernel
theorem pre_okd10_0 : subPre G cell10 d10_0 = true := by decide +kernel
theorem subd10_0_0 : subd10_0 [] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_nil _⟩
theorem ld_okd10_1 : ldCheck G d10_1.U d10_1.ms ldd10_1 = true := by decide +kernel
theorem pre_okd10_1 : subPre G cell10 d10_1 = true := by decide +kernel
theorem subd10_1_0 : subd10_1 [-2] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [-1] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [0] = true := by decide +kernel
theorem subd10_1_3 : subd10_1 [1] = true := by decide +kernel
theorem subd10_1_4 : subd10_1 [2] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_cons.2 ⟨subd10_1_3, List.forall_mem_cons.2 ⟨subd10_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem ld_okd10_2 : ldCheck G d10_2.U d10_2.ms ldd10_2 = true := by decide +kernel
theorem pre_okd10_2 : subPre G cell10 d10_2 = true := by decide +kernel
theorem subd10_2_0 : subd10_2 [] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_nil _⟩
theorem ld_okd10_3 : ldCheck G d10_3.U d10_3.ms ldd10_3 = true := by decide +kernel
theorem pre_okd10_3 : subPre G cell10 d10_3 = true := by decide +kernel
theorem subd10_3_0 : subd10_3 [] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_nil _⟩
theorem ld_okd10_4 : ldCheck G d10_4.U d10_4.ms ldd10_4 = true := by decide +kernel
theorem pre_okd10_4 : subPre G cell10 d10_4 = true := by decide +kernel
theorem subd10_4_0 : subd10_4 [] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_nil _⟩
theorem ld_okd10_5 : ldCheck G d10_5.U d10_5.ms ldd10_5 = true := by decide +kernel
theorem pre_okd10_5 : subPre G cell10 d10_5 = true := by decide +kernel
theorem subd10_5_0 : subd10_5 [] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_nil _⟩
theorem ld_okd10_6 : ldCheck G d10_6.U d10_6.ms ldd10_6 = true := by decide +kernel
theorem pre_okd10_6 : subPre G cell10 d10_6 = true := by decide +kernel
theorem subd10_6_0 : subd10_6 [-2] = true := by decide +kernel
theorem subd10_6_1 : subd10_6 [-1] = true := by decide +kernel
theorem subd10_6_2 : subd10_6 [0] = true := by decide +kernel
theorem subd10_6_3 : subd10_6 [1] = true := by decide +kernel
theorem subd10_6_4 : subd10_6 [2] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_cons.2 ⟨subd10_6_1, List.forall_mem_cons.2 ⟨subd10_6_2, List.forall_mem_cons.2 ⟨subd10_6_3, List.forall_mem_cons.2 ⟨subd10_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C124
