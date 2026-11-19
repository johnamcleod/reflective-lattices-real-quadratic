import ReflectZphi.Data.Cert5.C064.Base

namespace ReflectZphi.Data.Cert5.C064

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd0_0_0 : subd0_0 [] = true := by decide +kernel
theorem sbd0_0_0 : ∀ q ∈ blkd0_0_0, subd0_0 q = true := by
  unfold blkd0_0_0
  exact List.forall_mem_cons.2 ⟨subd0_0_0, List.forall_mem_nil _⟩
theorem subd0_1_0 : subd0_1 [] = true := by decide +kernel
theorem sbd0_1_0 : ∀ q ∈ blkd0_1_0, subd0_1 q = true := by
  unfold blkd0_1_0
  exact List.forall_mem_cons.2 ⟨subd0_1_0, List.forall_mem_nil _⟩
theorem subd0_2_0 : subd0_2 [] = true := by decide +kernel
theorem sbd0_2_0 : ∀ q ∈ blkd0_2_0, subd0_2 q = true := by
  unfold blkd0_2_0
  exact List.forall_mem_cons.2 ⟨subd0_2_0, List.forall_mem_nil _⟩
theorem subd0_3_0 : subd0_3 [] = true := by decide +kernel
theorem sbd0_3_0 : ∀ q ∈ blkd0_3_0, subd0_3 q = true := by
  unfold blkd0_3_0
  exact List.forall_mem_cons.2 ⟨subd0_3_0, List.forall_mem_nil _⟩
theorem subd0_4_0 : subd0_4 [] = true := by decide +kernel
theorem sbd0_4_0 : ∀ q ∈ blkd0_4_0, subd0_4 q = true := by
  unfold blkd0_4_0
  exact List.forall_mem_cons.2 ⟨subd0_4_0, List.forall_mem_nil _⟩
theorem subd0_5_0 : subd0_5 [] = true := by decide +kernel
theorem sbd0_5_0 : ∀ q ∈ blkd0_5_0, subd0_5 q = true := by
  unfold blkd0_5_0
  exact List.forall_mem_cons.2 ⟨subd0_5_0, List.forall_mem_nil _⟩
theorem subd0_6_0 : subd0_6 [-1] = true := by decide +kernel
theorem subd0_6_1 : subd0_6 [0] = true := by decide +kernel
theorem subd0_6_2 : subd0_6 [1] = true := by decide +kernel
theorem sbd0_6_0 : ∀ q ∈ blkd0_6_0, subd0_6 q = true := by
  unfold blkd0_6_0
  exact List.forall_mem_cons.2 ⟨subd0_6_0, List.forall_mem_cons.2 ⟨subd0_6_1, List.forall_mem_cons.2 ⟨subd0_6_2, List.forall_mem_nil _⟩⟩⟩
theorem subd1_0_0 : subd1_0 [] = true := by decide +kernel
theorem sbd1_0_0 : ∀ q ∈ blkd1_0_0, subd1_0 q = true := by
  unfold blkd1_0_0
  exact List.forall_mem_cons.2 ⟨subd1_0_0, List.forall_mem_nil _⟩
theorem subd1_1_0 : subd1_1 [-1] = true := by decide +kernel
theorem subd1_1_1 : subd1_1 [0] = true := by decide +kernel
theorem subd1_1_2 : subd1_1 [1] = true := by decide +kernel
theorem sbd1_1_0 : ∀ q ∈ blkd1_1_0, subd1_1 q = true := by
  unfold blkd1_1_0
  exact List.forall_mem_cons.2 ⟨subd1_1_0, List.forall_mem_cons.2 ⟨subd1_1_1, List.forall_mem_cons.2 ⟨subd1_1_2, List.forall_mem_nil _⟩⟩⟩
theorem subd1_2_0 : subd1_2 [-2] = true := by decide +kernel
theorem subd1_2_1 : subd1_2 [-1] = true := by decide +kernel
theorem subd1_2_2 : subd1_2 [0] = true := by decide +kernel
theorem subd1_2_3 : subd1_2 [1] = true := by decide +kernel
theorem subd1_2_4 : subd1_2 [2] = true := by decide +kernel
theorem sbd1_2_0 : ∀ q ∈ blkd1_2_0, subd1_2 q = true := by
  unfold blkd1_2_0
  exact List.forall_mem_cons.2 ⟨subd1_2_0, List.forall_mem_cons.2 ⟨subd1_2_1, List.forall_mem_cons.2 ⟨subd1_2_2, List.forall_mem_cons.2 ⟨subd1_2_3, List.forall_mem_cons.2 ⟨subd1_2_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd1_3_0 : subd1_3 [-2] = true := by decide +kernel
theorem subd1_3_1 : subd1_3 [-1] = true := by decide +kernel
theorem subd1_3_2 : subd1_3 [0] = true := by decide +kernel
theorem subd1_3_3 : subd1_3 [1] = true := by decide +kernel
theorem subd1_3_4 : subd1_3 [2] = true := by decide +kernel
theorem sbd1_3_0 : ∀ q ∈ blkd1_3_0, subd1_3 q = true := by
  unfold blkd1_3_0
  exact List.forall_mem_cons.2 ⟨subd1_3_0, List.forall_mem_cons.2 ⟨subd1_3_1, List.forall_mem_cons.2 ⟨subd1_3_2, List.forall_mem_cons.2 ⟨subd1_3_3, List.forall_mem_cons.2 ⟨subd1_3_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd1_4_0 : subd1_4 [] = true := by decide +kernel
theorem sbd1_4_0 : ∀ q ∈ blkd1_4_0, subd1_4 q = true := by
  unfold blkd1_4_0
  exact List.forall_mem_cons.2 ⟨subd1_4_0, List.forall_mem_nil _⟩
theorem subd1_5_0 : subd1_5 [-1] = true := by decide +kernel
theorem subd1_5_1 : subd1_5 [0] = true := by decide +kernel
theorem subd1_5_2 : subd1_5 [1] = true := by decide +kernel
theorem sbd1_5_0 : ∀ q ∈ blkd1_5_0, subd1_5 q = true := by
  unfold blkd1_5_0
  exact List.forall_mem_cons.2 ⟨subd1_5_0, List.forall_mem_cons.2 ⟨subd1_5_1, List.forall_mem_cons.2 ⟨subd1_5_2, List.forall_mem_nil _⟩⟩⟩
theorem subd1_6_0 : subd1_6 [-2] = true := by decide +kernel
theorem subd1_6_1 : subd1_6 [-1] = true := by decide +kernel
theorem subd1_6_2 : subd1_6 [0] = true := by decide +kernel
theorem subd1_6_3 : subd1_6 [1] = true := by decide +kernel
theorem subd1_6_4 : subd1_6 [2] = true := by decide +kernel
theorem sbd1_6_0 : ∀ q ∈ blkd1_6_0, subd1_6 q = true := by
  unfold blkd1_6_0
  exact List.forall_mem_cons.2 ⟨subd1_6_0, List.forall_mem_cons.2 ⟨subd1_6_1, List.forall_mem_cons.2 ⟨subd1_6_2, List.forall_mem_cons.2 ⟨subd1_6_3, List.forall_mem_cons.2 ⟨subd1_6_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd2_0_0 : subd2_0 [] = true := by decide +kernel
theorem sbd2_0_0 : ∀ q ∈ blkd2_0_0, subd2_0 q = true := by
  unfold blkd2_0_0
  exact List.forall_mem_cons.2 ⟨subd2_0_0, List.forall_mem_nil _⟩
theorem subd2_1_0 : subd2_1 [] = true := by decide +kernel
theorem sbd2_1_0 : ∀ q ∈ blkd2_1_0, subd2_1 q = true := by
  unfold blkd2_1_0
  exact List.forall_mem_cons.2 ⟨subd2_1_0, List.forall_mem_nil _⟩
theorem subd2_2_0 : subd2_2 [] = true := by decide +kernel
theorem sbd2_2_0 : ∀ q ∈ blkd2_2_0, subd2_2 q = true := by
  unfold blkd2_2_0
  exact List.forall_mem_cons.2 ⟨subd2_2_0, List.forall_mem_nil _⟩
theorem subd2_3_0 : subd2_3 [] = true := by decide +kernel
theorem sbd2_3_0 : ∀ q ∈ blkd2_3_0, subd2_3 q = true := by
  unfold blkd2_3_0
  exact List.forall_mem_cons.2 ⟨subd2_3_0, List.forall_mem_nil _⟩
theorem subd2_4_0 : subd2_4 [] = true := by decide +kernel
theorem sbd2_4_0 : ∀ q ∈ blkd2_4_0, subd2_4 q = true := by
  unfold blkd2_4_0
  exact List.forall_mem_cons.2 ⟨subd2_4_0, List.forall_mem_nil _⟩
theorem subd2_5_0 : subd2_5 [] = true := by decide +kernel
theorem sbd2_5_0 : ∀ q ∈ blkd2_5_0, subd2_5 q = true := by
  unfold blkd2_5_0
  exact List.forall_mem_cons.2 ⟨subd2_5_0, List.forall_mem_nil _⟩
theorem subd2_6_0 : subd2_6 [] = true := by decide +kernel
theorem sbd2_6_0 : ∀ q ∈ blkd2_6_0, subd2_6 q = true := by
  unfold blkd2_6_0
  exact List.forall_mem_cons.2 ⟨subd2_6_0, List.forall_mem_nil _⟩
theorem subd3_0_0 : subd3_0 [] = true := by decide +kernel
theorem sbd3_0_0 : ∀ q ∈ blkd3_0_0, subd3_0 q = true := by
  unfold blkd3_0_0
  exact List.forall_mem_cons.2 ⟨subd3_0_0, List.forall_mem_nil _⟩
theorem subd3_1_0 : subd3_1 [] = true := by decide +kernel
theorem sbd3_1_0 : ∀ q ∈ blkd3_1_0, subd3_1 q = true := by
  unfold blkd3_1_0
  exact List.forall_mem_cons.2 ⟨subd3_1_0, List.forall_mem_nil _⟩
theorem subd3_2_0 : subd3_2 [] = true := by decide +kernel
theorem sbd3_2_0 : ∀ q ∈ blkd3_2_0, subd3_2 q = true := by
  unfold blkd3_2_0
  exact List.forall_mem_cons.2 ⟨subd3_2_0, List.forall_mem_nil _⟩
theorem subd3_3_0 : subd3_3 [] = true := by decide +kernel
theorem sbd3_3_0 : ∀ q ∈ blkd3_3_0, subd3_3 q = true := by
  unfold blkd3_3_0
  exact List.forall_mem_cons.2 ⟨subd3_3_0, List.forall_mem_nil _⟩
theorem subd3_4_0 : subd3_4 [] = true := by decide +kernel
theorem sbd3_4_0 : ∀ q ∈ blkd3_4_0, subd3_4 q = true := by
  unfold blkd3_4_0
  exact List.forall_mem_cons.2 ⟨subd3_4_0, List.forall_mem_nil _⟩
theorem subd3_5_0 : subd3_5 [] = true := by decide +kernel
theorem sbd3_5_0 : ∀ q ∈ blkd3_5_0, subd3_5 q = true := by
  unfold blkd3_5_0
  exact List.forall_mem_cons.2 ⟨subd3_5_0, List.forall_mem_nil _⟩
theorem subd3_6_0 : subd3_6 [] = true := by decide +kernel
theorem sbd3_6_0 : ∀ q ∈ blkd3_6_0, subd3_6 q = true := by
  unfold blkd3_6_0
  exact List.forall_mem_cons.2 ⟨subd3_6_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C064
