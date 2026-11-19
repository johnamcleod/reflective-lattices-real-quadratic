import ReflectZphi.Data.Cert5.C075.Base

namespace ReflectZphi.Data.Cert5.C075

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_0 : subd9_1 [-2] = true := by decide +kernel
theorem subd9_1_1 : subd9_1 [-1] = true := by decide +kernel
theorem subd9_1_2 : subd9_1 [0, -3] = true := by decide +kernel
theorem subd9_1_3 : subd9_1 [0, -2] = true := by decide +kernel
theorem subd9_1_4 : subd9_1 [0, -1] = true := by decide +kernel
theorem subd9_1_5 : subd9_1 [0, 0] = true := by decide +kernel
theorem subd9_1_6 : subd9_1 [0, 1] = true := by decide +kernel
theorem subd9_1_7 : subd9_1 [0, 2] = true := by decide +kernel
theorem subd9_1_8 : subd9_1 [1] = true := by decide +kernel
theorem subd9_1_9 : subd9_1 [2] = true := by decide +kernel
theorem sbd9_1_0 : ∀ q ∈ blkd9_1_0, subd9_1 q = true := by
  unfold blkd9_1_0
  exact List.forall_mem_cons.2 ⟨subd9_1_0, List.forall_mem_cons.2 ⟨subd9_1_1, List.forall_mem_cons.2 ⟨subd9_1_2, List.forall_mem_cons.2 ⟨subd9_1_3, List.forall_mem_cons.2 ⟨subd9_1_4, List.forall_mem_cons.2 ⟨subd9_1_5, List.forall_mem_cons.2 ⟨subd9_1_6, List.forall_mem_cons.2 ⟨subd9_1_7, List.forall_mem_cons.2 ⟨subd9_1_8, List.forall_mem_cons.2 ⟨subd9_1_9, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_0 : subd9_2 [] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_nil _⟩
theorem subd9_3_0 : subd9_3 [] = true := by decide +kernel
theorem sbd9_3_0 : ∀ q ∈ blkd9_3_0, subd9_3 q = true := by
  unfold blkd9_3_0
  exact List.forall_mem_cons.2 ⟨subd9_3_0, List.forall_mem_nil _⟩
theorem subd9_4_0 : subd9_4 [] = true := by decide +kernel
theorem sbd9_4_0 : ∀ q ∈ blkd9_4_0, subd9_4 q = true := by
  unfold blkd9_4_0
  exact List.forall_mem_cons.2 ⟨subd9_4_0, List.forall_mem_nil _⟩
theorem subd9_5_0 : subd9_5 [] = true := by decide +kernel
theorem sbd9_5_0 : ∀ q ∈ blkd9_5_0, subd9_5 q = true := by
  unfold blkd9_5_0
  exact List.forall_mem_cons.2 ⟨subd9_5_0, List.forall_mem_nil _⟩
theorem subd9_6_0 : subd9_6 [] = true := by decide +kernel
theorem sbd9_6_0 : ∀ q ∈ blkd9_6_0, subd9_6 q = true := by
  unfold blkd9_6_0
  exact List.forall_mem_cons.2 ⟨subd9_6_0, List.forall_mem_nil _⟩
theorem subd10_0_0 : subd10_0 [-1] = true := by decide +kernel
theorem subd10_0_1 : subd10_0 [0, -2] = true := by decide +kernel
theorem subd10_0_2 : subd10_0 [0, -1] = true := by decide +kernel
theorem subd10_0_3 : subd10_0 [0, 0] = true := by decide +kernel
theorem subd10_0_4 : subd10_0 [0, 1] = true := by decide +kernel
theorem subd10_0_5 : subd10_0 [1] = true := by decide +kernel
theorem sbd10_0_0 : ∀ q ∈ blkd10_0_0, subd10_0 q = true := by
  unfold blkd10_0_0
  exact List.forall_mem_cons.2 ⟨subd10_0_0, List.forall_mem_cons.2 ⟨subd10_0_1, List.forall_mem_cons.2 ⟨subd10_0_2, List.forall_mem_cons.2 ⟨subd10_0_3, List.forall_mem_cons.2 ⟨subd10_0_4, List.forall_mem_cons.2 ⟨subd10_0_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩
theorem subd10_1_0 : subd10_1 [-1] = true := by decide +kernel
theorem subd10_1_1 : subd10_1 [0] = true := by decide +kernel
theorem subd10_1_2 : subd10_1 [1] = true := by decide +kernel
theorem sbd10_1_0 : ∀ q ∈ blkd10_1_0, subd10_1 q = true := by
  unfold blkd10_1_0
  exact List.forall_mem_cons.2 ⟨subd10_1_0, List.forall_mem_cons.2 ⟨subd10_1_1, List.forall_mem_cons.2 ⟨subd10_1_2, List.forall_mem_nil _⟩⟩⟩
theorem subd10_2_0 : subd10_2 [] = true := by decide +kernel
theorem sbd10_2_0 : ∀ q ∈ blkd10_2_0, subd10_2 q = true := by
  unfold blkd10_2_0
  exact List.forall_mem_cons.2 ⟨subd10_2_0, List.forall_mem_nil _⟩
theorem subd10_3_0 : subd10_3 [] = true := by decide +kernel
theorem sbd10_3_0 : ∀ q ∈ blkd10_3_0, subd10_3 q = true := by
  unfold blkd10_3_0
  exact List.forall_mem_cons.2 ⟨subd10_3_0, List.forall_mem_nil _⟩
theorem subd10_4_0 : subd10_4 [] = true := by decide +kernel
theorem sbd10_4_0 : ∀ q ∈ blkd10_4_0, subd10_4 q = true := by
  unfold blkd10_4_0
  exact List.forall_mem_cons.2 ⟨subd10_4_0, List.forall_mem_nil _⟩
theorem subd10_5_0 : subd10_5 [] = true := by decide +kernel
theorem sbd10_5_0 : ∀ q ∈ blkd10_5_0, subd10_5 q = true := by
  unfold blkd10_5_0
  exact List.forall_mem_cons.2 ⟨subd10_5_0, List.forall_mem_nil _⟩
theorem subd10_6_0 : subd10_6 [] = true := by decide +kernel
theorem sbd10_6_0 : ∀ q ∈ blkd10_6_0, subd10_6 q = true := by
  unfold blkd10_6_0
  exact List.forall_mem_cons.2 ⟨subd10_6_0, List.forall_mem_nil _⟩
theorem subd11_0_0 : subd11_0 [-1] = true := by decide +kernel
theorem subd11_0_1 : subd11_0 [0] = true := by decide +kernel
theorem subd11_0_2 : subd11_0 [1] = true := by decide +kernel
theorem sbd11_0_0 : ∀ q ∈ blkd11_0_0, subd11_0 q = true := by
  unfold blkd11_0_0
  exact List.forall_mem_cons.2 ⟨subd11_0_0, List.forall_mem_cons.2 ⟨subd11_0_1, List.forall_mem_cons.2 ⟨subd11_0_2, List.forall_mem_nil _⟩⟩⟩
theorem subd11_1_0 : subd11_1 [-2] = true := by decide +kernel
theorem subd11_1_1 : subd11_1 [-1] = true := by decide +kernel
theorem subd11_1_2 : subd11_1 [0] = true := by decide +kernel
theorem subd11_1_3 : subd11_1 [1] = true := by decide +kernel
theorem subd11_1_4 : subd11_1 [2] = true := by decide +kernel
theorem sbd11_1_0 : ∀ q ∈ blkd11_1_0, subd11_1 q = true := by
  unfold blkd11_1_0
  exact List.forall_mem_cons.2 ⟨subd11_1_0, List.forall_mem_cons.2 ⟨subd11_1_1, List.forall_mem_cons.2 ⟨subd11_1_2, List.forall_mem_cons.2 ⟨subd11_1_3, List.forall_mem_cons.2 ⟨subd11_1_4, List.forall_mem_nil _⟩⟩⟩⟩⟩
theorem subd11_2_0 : subd11_2 [] = true := by decide +kernel
theorem sbd11_2_0 : ∀ q ∈ blkd11_2_0, subd11_2 q = true := by
  unfold blkd11_2_0
  exact List.forall_mem_cons.2 ⟨subd11_2_0, List.forall_mem_nil _⟩
theorem subd11_3_0 : subd11_3 [] = true := by decide +kernel
theorem sbd11_3_0 : ∀ q ∈ blkd11_3_0, subd11_3 q = true := by
  unfold blkd11_3_0
  exact List.forall_mem_cons.2 ⟨subd11_3_0, List.forall_mem_nil _⟩
theorem subd11_4_0 : subd11_4 [] = true := by decide +kernel
theorem sbd11_4_0 : ∀ q ∈ blkd11_4_0, subd11_4 q = true := by
  unfold blkd11_4_0
  exact List.forall_mem_cons.2 ⟨subd11_4_0, List.forall_mem_nil _⟩
theorem subd11_5_0 : subd11_5 [] = true := by decide +kernel
theorem sbd11_5_0 : ∀ q ∈ blkd11_5_0, subd11_5 q = true := by
  unfold blkd11_5_0
  exact List.forall_mem_cons.2 ⟨subd11_5_0, List.forall_mem_nil _⟩
theorem subd11_6_0 : subd11_6 [] = true := by decide +kernel
theorem sbd11_6_0 : ∀ q ∈ blkd11_6_0, subd11_6 q = true := by
  unfold blkd11_6_0
  exact List.forall_mem_cons.2 ⟨subd11_6_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C075
