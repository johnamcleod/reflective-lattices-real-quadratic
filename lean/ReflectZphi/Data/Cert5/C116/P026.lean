import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd7_1_4448 : subd7_1 [5, 7, 3] = true := by decide +kernel
theorem subd7_1_4449 : subd7_1 [5, 7, 4] = true := by decide +kernel
theorem subd7_1_4450 : subd7_1 [5, 7, 5] = true := by decide +kernel
theorem subd7_1_4451 : subd7_1 [5, 7, 6] = true := by decide +kernel
theorem subd7_1_4452 : subd7_1 [5, 7, 7] = true := by decide +kernel
theorem subd7_1_4453 : subd7_1 [5, 7, 8] = true := by decide +kernel
theorem subd7_1_4454 : subd7_1 [5, 7, 9] = true := by decide +kernel
theorem subd7_1_4455 : subd7_1 [5, 7, 10] = true := by decide +kernel
theorem subd7_1_4456 : subd7_1 [5, 8] = true := by decide +kernel
theorem subd7_1_4457 : subd7_1 [5, 9] = true := by decide +kernel
theorem subd7_1_4458 : subd7_1 [6, -7] = true := by decide +kernel
theorem subd7_1_4459 : subd7_1 [6, -6] = true := by decide +kernel
theorem subd7_1_4460 : subd7_1 [6, -5] = true := by decide +kernel
theorem subd7_1_4461 : subd7_1 [6, -4, -7] = true := by decide +kernel
theorem subd7_1_4462 : subd7_1 [6, -4, -6] = true := by decide +kernel
theorem subd7_1_4463 : subd7_1 [6, -4, -5] = true := by decide +kernel
theorem subd7_1_4464 : subd7_1 [6, -4, -4] = true := by decide +kernel
theorem subd7_1_4465 : subd7_1 [6, -4, -3] = true := by decide +kernel
theorem subd7_1_4466 : subd7_1 [6, -4, -2] = true := by decide +kernel
theorem subd7_1_4467 : subd7_1 [6, -4, -1] = true := by decide +kernel
theorem subd7_1_4468 : subd7_1 [6, -4, 0] = true := by decide +kernel
theorem subd7_1_4469 : subd7_1 [6, -4, 1] = true := by decide +kernel
theorem subd7_1_4470 : subd7_1 [6, -4, 2] = true := by decide +kernel
theorem subd7_1_4471 : subd7_1 [6, -4, 3] = true := by decide +kernel
theorem subd7_1_4472 : subd7_1 [6, -4, 4] = true := by decide +kernel
theorem subd7_1_4473 : subd7_1 [6, -4, 5] = true := by decide +kernel
theorem subd7_1_4474 : subd7_1 [6, -4, 6] = true := by decide +kernel
theorem subd7_1_4475 : subd7_1 [6, -4, 7] = true := by decide +kernel
theorem subd7_1_4476 : subd7_1 [6, -4, 8] = true := by decide +kernel
theorem subd7_1_4477 : subd7_1 [6, -3, -8] = true := by decide +kernel
theorem subd7_1_4478 : subd7_1 [6, -3, -7] = true := by decide +kernel
theorem subd7_1_4479 : subd7_1 [6, -3, -6] = true := by decide +kernel
theorem sbd7_1_139 : ∀ q ∈ blkd7_1_139, subd7_1 q = true := by
  unfold blkd7_1_139
  exact List.forall_mem_cons.2 ⟨subd7_1_4448, List.forall_mem_cons.2 ⟨subd7_1_4449, List.forall_mem_cons.2 ⟨subd7_1_4450, List.forall_mem_cons.2 ⟨subd7_1_4451, List.forall_mem_cons.2 ⟨subd7_1_4452, List.forall_mem_cons.2 ⟨subd7_1_4453, List.forall_mem_cons.2 ⟨subd7_1_4454, List.forall_mem_cons.2 ⟨subd7_1_4455, List.forall_mem_cons.2 ⟨subd7_1_4456, List.forall_mem_cons.2 ⟨subd7_1_4457, List.forall_mem_cons.2 ⟨subd7_1_4458, List.forall_mem_cons.2 ⟨subd7_1_4459, List.forall_mem_cons.2 ⟨subd7_1_4460, List.forall_mem_cons.2 ⟨subd7_1_4461, List.forall_mem_cons.2 ⟨subd7_1_4462, List.forall_mem_cons.2 ⟨subd7_1_4463, List.forall_mem_cons.2 ⟨subd7_1_4464, List.forall_mem_cons.2 ⟨subd7_1_4465, List.forall_mem_cons.2 ⟨subd7_1_4466, List.forall_mem_cons.2 ⟨subd7_1_4467, List.forall_mem_cons.2 ⟨subd7_1_4468, List.forall_mem_cons.2 ⟨subd7_1_4469, List.forall_mem_cons.2 ⟨subd7_1_4470, List.forall_mem_cons.2 ⟨subd7_1_4471, List.forall_mem_cons.2 ⟨subd7_1_4472, List.forall_mem_cons.2 ⟨subd7_1_4473, List.forall_mem_cons.2 ⟨subd7_1_4474, List.forall_mem_cons.2 ⟨subd7_1_4475, List.forall_mem_cons.2 ⟨subd7_1_4476, List.forall_mem_cons.2 ⟨subd7_1_4477, List.forall_mem_cons.2 ⟨subd7_1_4478, List.forall_mem_cons.2 ⟨subd7_1_4479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4480 : subd7_1 [6, -3, -5] = true := by decide +kernel
theorem subd7_1_4481 : subd7_1 [6, -3, -4] = true := by decide +kernel
theorem subd7_1_4482 : subd7_1 [6, -3, -3] = true := by decide +kernel
theorem subd7_1_4483 : subd7_1 [6, -3, -2] = true := by decide +kernel
theorem subd7_1_4484 : subd7_1 [6, -3, -1] = true := by decide +kernel
theorem subd7_1_4485 : subd7_1 [6, -3, 0] = true := by decide +kernel
theorem subd7_1_4486 : subd7_1 [6, -3, 1] = true := by decide +kernel
theorem subd7_1_4487 : subd7_1 [6, -3, 2] = true := by decide +kernel
theorem subd7_1_4488 : subd7_1 [6, -3, 3] = true := by decide +kernel
theorem subd7_1_4489 : subd7_1 [6, -3, 4] = true := by decide +kernel
theorem subd7_1_4490 : subd7_1 [6, -3, 5] = true := by decide +kernel
theorem subd7_1_4491 : subd7_1 [6, -3, 6] = true := by decide +kernel
theorem subd7_1_4492 : subd7_1 [6, -3, 7] = true := by decide +kernel
theorem subd7_1_4493 : subd7_1 [6, -3, 8] = true := by decide +kernel
theorem subd7_1_4494 : subd7_1 [6, -3, 9] = true := by decide +kernel
theorem subd7_1_4495 : subd7_1 [6, -2, -8] = true := by decide +kernel
theorem subd7_1_4496 : subd7_1 [6, -2, -7] = true := by decide +kernel
theorem subd7_1_4497 : subd7_1 [6, -2, -6] = true := by decide +kernel
theorem subd7_1_4498 : subd7_1 [6, -2, -5] = true := by decide +kernel
theorem subd7_1_4499 : subd7_1 [6, -2, -4] = true := by decide +kernel
theorem subd7_1_4500 : subd7_1 [6, -2, -3] = true := by decide +kernel
theorem subd7_1_4501 : subd7_1 [6, -2, -2] = true := by decide +kernel
theorem subd7_1_4502 : subd7_1 [6, -2, -1] = true := by decide +kernel
theorem subd7_1_4503 : subd7_1 [6, -2, 0] = true := by decide +kernel
theorem subd7_1_4504 : subd7_1 [6, -2, 1] = true := by decide +kernel
theorem subd7_1_4505 : subd7_1 [6, -2, 2] = true := by decide +kernel
theorem subd7_1_4506 : subd7_1 [6, -2, 3] = true := by decide +kernel
theorem subd7_1_4507 : subd7_1 [6, -2, 4] = true := by decide +kernel
theorem subd7_1_4508 : subd7_1 [6, -2, 5] = true := by decide +kernel
theorem subd7_1_4509 : subd7_1 [6, -2, 6] = true := by decide +kernel
theorem subd7_1_4510 : subd7_1 [6, -2, 7] = true := by decide +kernel
theorem subd7_1_4511 : subd7_1 [6, -2, 8] = true := by decide +kernel
theorem sbd7_1_140 : ∀ q ∈ blkd7_1_140, subd7_1 q = true := by
  unfold blkd7_1_140
  exact List.forall_mem_cons.2 ⟨subd7_1_4480, List.forall_mem_cons.2 ⟨subd7_1_4481, List.forall_mem_cons.2 ⟨subd7_1_4482, List.forall_mem_cons.2 ⟨subd7_1_4483, List.forall_mem_cons.2 ⟨subd7_1_4484, List.forall_mem_cons.2 ⟨subd7_1_4485, List.forall_mem_cons.2 ⟨subd7_1_4486, List.forall_mem_cons.2 ⟨subd7_1_4487, List.forall_mem_cons.2 ⟨subd7_1_4488, List.forall_mem_cons.2 ⟨subd7_1_4489, List.forall_mem_cons.2 ⟨subd7_1_4490, List.forall_mem_cons.2 ⟨subd7_1_4491, List.forall_mem_cons.2 ⟨subd7_1_4492, List.forall_mem_cons.2 ⟨subd7_1_4493, List.forall_mem_cons.2 ⟨subd7_1_4494, List.forall_mem_cons.2 ⟨subd7_1_4495, List.forall_mem_cons.2 ⟨subd7_1_4496, List.forall_mem_cons.2 ⟨subd7_1_4497, List.forall_mem_cons.2 ⟨subd7_1_4498, List.forall_mem_cons.2 ⟨subd7_1_4499, List.forall_mem_cons.2 ⟨subd7_1_4500, List.forall_mem_cons.2 ⟨subd7_1_4501, List.forall_mem_cons.2 ⟨subd7_1_4502, List.forall_mem_cons.2 ⟨subd7_1_4503, List.forall_mem_cons.2 ⟨subd7_1_4504, List.forall_mem_cons.2 ⟨subd7_1_4505, List.forall_mem_cons.2 ⟨subd7_1_4506, List.forall_mem_cons.2 ⟨subd7_1_4507, List.forall_mem_cons.2 ⟨subd7_1_4508, List.forall_mem_cons.2 ⟨subd7_1_4509, List.forall_mem_cons.2 ⟨subd7_1_4510, List.forall_mem_cons.2 ⟨subd7_1_4511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4512 : subd7_1 [6, -2, 9] = true := by decide +kernel
theorem subd7_1_4513 : subd7_1 [6, -2, 10] = true := by decide +kernel
theorem subd7_1_4514 : subd7_1 [6, -1, -8] = true := by decide +kernel
theorem subd7_1_4515 : subd7_1 [6, -1, -7] = true := by decide +kernel
theorem subd7_1_4516 : subd7_1 [6, -1, -6] = true := by decide +kernel
theorem subd7_1_4517 : subd7_1 [6, -1, -5] = true := by decide +kernel
theorem subd7_1_4518 : subd7_1 [6, -1, -4] = true := by decide +kernel
theorem subd7_1_4519 : subd7_1 [6, -1, -3] = true := by decide +kernel
theorem subd7_1_4520 : subd7_1 [6, -1, -2] = true := by decide +kernel
theorem subd7_1_4521 : subd7_1 [6, -1, -1] = true := by decide +kernel
theorem subd7_1_4522 : subd7_1 [6, -1, 0] = true := by decide +kernel
theorem subd7_1_4523 : subd7_1 [6, -1, 1] = true := by decide +kernel
theorem subd7_1_4524 : subd7_1 [6, -1, 2] = true := by decide +kernel
theorem subd7_1_4525 : subd7_1 [6, -1, 3] = true := by decide +kernel
theorem subd7_1_4526 : subd7_1 [6, -1, 4] = true := by decide +kernel
theorem subd7_1_4527 : subd7_1 [6, -1, 5] = true := by decide +kernel
theorem subd7_1_4528 : subd7_1 [6, -1, 6] = true := by decide +kernel
theorem subd7_1_4529 : subd7_1 [6, -1, 7] = true := by decide +kernel
theorem subd7_1_4530 : subd7_1 [6, -1, 8] = true := by decide +kernel
theorem subd7_1_4531 : subd7_1 [6, -1, 9] = true := by decide +kernel
theorem subd7_1_4532 : subd7_1 [6, -1, 10] = true := by decide +kernel
theorem subd7_1_4533 : subd7_1 [6, -1, 11] = true := by decide +kernel
theorem subd7_1_4534 : subd7_1 [6, 0, -9] = true := by decide +kernel
theorem subd7_1_4535 : subd7_1 [6, 0, -8] = true := by decide +kernel
theorem subd7_1_4536 : subd7_1 [6, 0, -7] = true := by decide +kernel
theorem subd7_1_4537 : subd7_1 [6, 0, -6] = true := by decide +kernel
theorem subd7_1_4538 : subd7_1 [6, 0, -5] = true := by decide +kernel
theorem subd7_1_4539 : subd7_1 [6, 0, -4] = true := by decide +kernel
theorem subd7_1_4540 : subd7_1 [6, 0, -3] = true := by decide +kernel
theorem subd7_1_4541 : subd7_1 [6, 0, -2] = true := by decide +kernel
theorem subd7_1_4542 : subd7_1 [6, 0, -1] = true := by decide +kernel
theorem subd7_1_4543 : subd7_1 [6, 0, 0] = true := by decide +kernel
theorem sbd7_1_141 : ∀ q ∈ blkd7_1_141, subd7_1 q = true := by
  unfold blkd7_1_141
  exact List.forall_mem_cons.2 ⟨subd7_1_4512, List.forall_mem_cons.2 ⟨subd7_1_4513, List.forall_mem_cons.2 ⟨subd7_1_4514, List.forall_mem_cons.2 ⟨subd7_1_4515, List.forall_mem_cons.2 ⟨subd7_1_4516, List.forall_mem_cons.2 ⟨subd7_1_4517, List.forall_mem_cons.2 ⟨subd7_1_4518, List.forall_mem_cons.2 ⟨subd7_1_4519, List.forall_mem_cons.2 ⟨subd7_1_4520, List.forall_mem_cons.2 ⟨subd7_1_4521, List.forall_mem_cons.2 ⟨subd7_1_4522, List.forall_mem_cons.2 ⟨subd7_1_4523, List.forall_mem_cons.2 ⟨subd7_1_4524, List.forall_mem_cons.2 ⟨subd7_1_4525, List.forall_mem_cons.2 ⟨subd7_1_4526, List.forall_mem_cons.2 ⟨subd7_1_4527, List.forall_mem_cons.2 ⟨subd7_1_4528, List.forall_mem_cons.2 ⟨subd7_1_4529, List.forall_mem_cons.2 ⟨subd7_1_4530, List.forall_mem_cons.2 ⟨subd7_1_4531, List.forall_mem_cons.2 ⟨subd7_1_4532, List.forall_mem_cons.2 ⟨subd7_1_4533, List.forall_mem_cons.2 ⟨subd7_1_4534, List.forall_mem_cons.2 ⟨subd7_1_4535, List.forall_mem_cons.2 ⟨subd7_1_4536, List.forall_mem_cons.2 ⟨subd7_1_4537, List.forall_mem_cons.2 ⟨subd7_1_4538, List.forall_mem_cons.2 ⟨subd7_1_4539, List.forall_mem_cons.2 ⟨subd7_1_4540, List.forall_mem_cons.2 ⟨subd7_1_4541, List.forall_mem_cons.2 ⟨subd7_1_4542, List.forall_mem_cons.2 ⟨subd7_1_4543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4544 : subd7_1 [6, 0, 1] = true := by decide +kernel
theorem subd7_1_4545 : subd7_1 [6, 0, 2] = true := by decide +kernel
theorem subd7_1_4546 : subd7_1 [6, 0, 3] = true := by decide +kernel
theorem subd7_1_4547 : subd7_1 [6, 0, 4] = true := by decide +kernel
theorem subd7_1_4548 : subd7_1 [6, 0, 5] = true := by decide +kernel
theorem subd7_1_4549 : subd7_1 [6, 0, 6] = true := by decide +kernel
theorem subd7_1_4550 : subd7_1 [6, 0, 7] = true := by decide +kernel
theorem subd7_1_4551 : subd7_1 [6, 0, 8] = true := by decide +kernel
theorem subd7_1_4552 : subd7_1 [6, 0, 9] = true := by decide +kernel
theorem subd7_1_4553 : subd7_1 [6, 0, 10] = true := by decide +kernel
theorem subd7_1_4554 : subd7_1 [6, 0, 11] = true := by decide +kernel
theorem subd7_1_4555 : subd7_1 [6, 1, -8] = true := by decide +kernel
theorem subd7_1_4556 : subd7_1 [6, 1, -7] = true := by decide +kernel
theorem subd7_1_4557 : subd7_1 [6, 1, -6] = true := by decide +kernel
theorem subd7_1_4558 : subd7_1 [6, 1, -5] = true := by decide +kernel
theorem subd7_1_4559 : subd7_1 [6, 1, -4] = true := by decide +kernel
theorem subd7_1_4560 : subd7_1 [6, 1, -3] = true := by decide +kernel
theorem subd7_1_4561 : subd7_1 [6, 1, -2] = true := by decide +kernel
theorem subd7_1_4562 : subd7_1 [6, 1, -1] = true := by decide +kernel
theorem subd7_1_4563 : subd7_1 [6, 1, 0] = true := by decide +kernel
theorem subd7_1_4564 : subd7_1 [6, 1, 1] = true := by decide +kernel
theorem subd7_1_4565 : subd7_1 [6, 1, 2] = true := by decide +kernel
theorem subd7_1_4566 : subd7_1 [6, 1, 3] = true := by decide +kernel
theorem subd7_1_4567 : subd7_1 [6, 1, 4] = true := by decide +kernel
theorem subd7_1_4568 : subd7_1 [6, 1, 5] = true := by decide +kernel
theorem subd7_1_4569 : subd7_1 [6, 1, 6] = true := by decide +kernel
theorem subd7_1_4570 : subd7_1 [6, 1, 7] = true := by decide +kernel
theorem subd7_1_4571 : subd7_1 [6, 1, 8] = true := by decide +kernel
theorem subd7_1_4572 : subd7_1 [6, 1, 9] = true := by decide +kernel
theorem subd7_1_4573 : subd7_1 [6, 1, 10] = true := by decide +kernel
theorem subd7_1_4574 : subd7_1 [6, 1, 11] = true := by decide +kernel
theorem subd7_1_4575 : subd7_1 [6, 1, 12] = true := by decide +kernel
theorem sbd7_1_142 : ∀ q ∈ blkd7_1_142, subd7_1 q = true := by
  unfold blkd7_1_142
  exact List.forall_mem_cons.2 ⟨subd7_1_4544, List.forall_mem_cons.2 ⟨subd7_1_4545, List.forall_mem_cons.2 ⟨subd7_1_4546, List.forall_mem_cons.2 ⟨subd7_1_4547, List.forall_mem_cons.2 ⟨subd7_1_4548, List.forall_mem_cons.2 ⟨subd7_1_4549, List.forall_mem_cons.2 ⟨subd7_1_4550, List.forall_mem_cons.2 ⟨subd7_1_4551, List.forall_mem_cons.2 ⟨subd7_1_4552, List.forall_mem_cons.2 ⟨subd7_1_4553, List.forall_mem_cons.2 ⟨subd7_1_4554, List.forall_mem_cons.2 ⟨subd7_1_4555, List.forall_mem_cons.2 ⟨subd7_1_4556, List.forall_mem_cons.2 ⟨subd7_1_4557, List.forall_mem_cons.2 ⟨subd7_1_4558, List.forall_mem_cons.2 ⟨subd7_1_4559, List.forall_mem_cons.2 ⟨subd7_1_4560, List.forall_mem_cons.2 ⟨subd7_1_4561, List.forall_mem_cons.2 ⟨subd7_1_4562, List.forall_mem_cons.2 ⟨subd7_1_4563, List.forall_mem_cons.2 ⟨subd7_1_4564, List.forall_mem_cons.2 ⟨subd7_1_4565, List.forall_mem_cons.2 ⟨subd7_1_4566, List.forall_mem_cons.2 ⟨subd7_1_4567, List.forall_mem_cons.2 ⟨subd7_1_4568, List.forall_mem_cons.2 ⟨subd7_1_4569, List.forall_mem_cons.2 ⟨subd7_1_4570, List.forall_mem_cons.2 ⟨subd7_1_4571, List.forall_mem_cons.2 ⟨subd7_1_4572, List.forall_mem_cons.2 ⟨subd7_1_4573, List.forall_mem_cons.2 ⟨subd7_1_4574, List.forall_mem_cons.2 ⟨subd7_1_4575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4576 : subd7_1 [6, 2, -8] = true := by decide +kernel
theorem subd7_1_4577 : subd7_1 [6, 2, -7] = true := by decide +kernel
theorem subd7_1_4578 : subd7_1 [6, 2, -6] = true := by decide +kernel
theorem subd7_1_4579 : subd7_1 [6, 2, -5] = true := by decide +kernel
theorem subd7_1_4580 : subd7_1 [6, 2, -4] = true := by decide +kernel
theorem subd7_1_4581 : subd7_1 [6, 2, -3] = true := by decide +kernel
theorem subd7_1_4582 : subd7_1 [6, 2, -2] = true := by decide +kernel
theorem subd7_1_4583 : subd7_1 [6, 2, -1] = true := by decide +kernel
theorem subd7_1_4584 : subd7_1 [6, 2, 0] = true := by decide +kernel
theorem subd7_1_4585 : subd7_1 [6, 2, 1] = true := by decide +kernel
theorem subd7_1_4586 : subd7_1 [6, 2, 2] = true := by decide +kernel
theorem subd7_1_4587 : subd7_1 [6, 2, 3] = true := by decide +kernel
theorem subd7_1_4588 : subd7_1 [6, 2, 4] = true := by decide +kernel
theorem subd7_1_4589 : subd7_1 [6, 2, 5] = true := by decide +kernel
theorem subd7_1_4590 : subd7_1 [6, 2, 6] = true := by decide +kernel
theorem subd7_1_4591 : subd7_1 [6, 2, 7] = true := by decide +kernel
theorem subd7_1_4592 : subd7_1 [6, 2, 8] = true := by decide +kernel
theorem subd7_1_4593 : subd7_1 [6, 2, 9] = true := by decide +kernel
theorem subd7_1_4594 : subd7_1 [6, 2, 10] = true := by decide +kernel
theorem subd7_1_4595 : subd7_1 [6, 2, 11] = true := by decide +kernel
theorem subd7_1_4596 : subd7_1 [6, 2, 12] = true := by decide +kernel
theorem subd7_1_4597 : subd7_1 [6, 3, -8] = true := by decide +kernel
theorem subd7_1_4598 : subd7_1 [6, 3, -7] = true := by decide +kernel
theorem subd7_1_4599 : subd7_1 [6, 3, -6] = true := by decide +kernel
theorem subd7_1_4600 : subd7_1 [6, 3, -5] = true := by decide +kernel
theorem subd7_1_4601 : subd7_1 [6, 3, -4] = true := by decide +kernel
theorem subd7_1_4602 : subd7_1 [6, 3, -3] = true := by decide +kernel
theorem subd7_1_4603 : subd7_1 [6, 3, -2] = true := by decide +kernel
theorem subd7_1_4604 : subd7_1 [6, 3, -1] = true := by decide +kernel
theorem subd7_1_4605 : subd7_1 [6, 3, 0] = true := by decide +kernel
theorem subd7_1_4606 : subd7_1 [6, 3, 1] = true := by decide +kernel
theorem subd7_1_4607 : subd7_1 [6, 3, 2] = true := by decide +kernel
theorem sbd7_1_143 : ∀ q ∈ blkd7_1_143, subd7_1 q = true := by
  unfold blkd7_1_143
  exact List.forall_mem_cons.2 ⟨subd7_1_4576, List.forall_mem_cons.2 ⟨subd7_1_4577, List.forall_mem_cons.2 ⟨subd7_1_4578, List.forall_mem_cons.2 ⟨subd7_1_4579, List.forall_mem_cons.2 ⟨subd7_1_4580, List.forall_mem_cons.2 ⟨subd7_1_4581, List.forall_mem_cons.2 ⟨subd7_1_4582, List.forall_mem_cons.2 ⟨subd7_1_4583, List.forall_mem_cons.2 ⟨subd7_1_4584, List.forall_mem_cons.2 ⟨subd7_1_4585, List.forall_mem_cons.2 ⟨subd7_1_4586, List.forall_mem_cons.2 ⟨subd7_1_4587, List.forall_mem_cons.2 ⟨subd7_1_4588, List.forall_mem_cons.2 ⟨subd7_1_4589, List.forall_mem_cons.2 ⟨subd7_1_4590, List.forall_mem_cons.2 ⟨subd7_1_4591, List.forall_mem_cons.2 ⟨subd7_1_4592, List.forall_mem_cons.2 ⟨subd7_1_4593, List.forall_mem_cons.2 ⟨subd7_1_4594, List.forall_mem_cons.2 ⟨subd7_1_4595, List.forall_mem_cons.2 ⟨subd7_1_4596, List.forall_mem_cons.2 ⟨subd7_1_4597, List.forall_mem_cons.2 ⟨subd7_1_4598, List.forall_mem_cons.2 ⟨subd7_1_4599, List.forall_mem_cons.2 ⟨subd7_1_4600, List.forall_mem_cons.2 ⟨subd7_1_4601, List.forall_mem_cons.2 ⟨subd7_1_4602, List.forall_mem_cons.2 ⟨subd7_1_4603, List.forall_mem_cons.2 ⟨subd7_1_4604, List.forall_mem_cons.2 ⟨subd7_1_4605, List.forall_mem_cons.2 ⟨subd7_1_4606, List.forall_mem_cons.2 ⟨subd7_1_4607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4608 : subd7_1 [6, 3, 3] = true := by decide +kernel
theorem subd7_1_4609 : subd7_1 [6, 3, 4] = true := by decide +kernel
theorem subd7_1_4610 : subd7_1 [6, 3, 5] = true := by decide +kernel
theorem subd7_1_4611 : subd7_1 [6, 3, 6] = true := by decide +kernel
theorem subd7_1_4612 : subd7_1 [6, 3, 7] = true := by decide +kernel
theorem subd7_1_4613 : subd7_1 [6, 3, 8] = true := by decide +kernel
theorem subd7_1_4614 : subd7_1 [6, 3, 9] = true := by decide +kernel
theorem subd7_1_4615 : subd7_1 [6, 3, 10] = true := by decide +kernel
theorem subd7_1_4616 : subd7_1 [6, 3, 11] = true := by decide +kernel
theorem subd7_1_4617 : subd7_1 [6, 3, 12] = true := by decide +kernel
theorem subd7_1_4618 : subd7_1 [6, 4, -7] = true := by decide +kernel
theorem subd7_1_4619 : subd7_1 [6, 4, -6] = true := by decide +kernel
theorem subd7_1_4620 : subd7_1 [6, 4, -5] = true := by decide +kernel
theorem subd7_1_4621 : subd7_1 [6, 4, -4] = true := by decide +kernel
theorem subd7_1_4622 : subd7_1 [6, 4, -3] = true := by decide +kernel
theorem subd7_1_4623 : subd7_1 [6, 4, -2] = true := by decide +kernel
theorem subd7_1_4624 : subd7_1 [6, 4, -1] = true := by decide +kernel
theorem subd7_1_4625 : subd7_1 [6, 4, 0] = true := by decide +kernel
theorem subd7_1_4626 : subd7_1 [6, 4, 1] = true := by decide +kernel
theorem subd7_1_4627 : subd7_1 [6, 4, 2] = true := by decide +kernel
theorem subd7_1_4628 : subd7_1 [6, 4, 3] = true := by decide +kernel
theorem subd7_1_4629 : subd7_1 [6, 4, 4] = true := by decide +kernel
theorem subd7_1_4630 : subd7_1 [6, 4, 5] = true := by decide +kernel
theorem subd7_1_4631 : subd7_1 [6, 4, 6] = true := by decide +kernel
theorem subd7_1_4632 : subd7_1 [6, 4, 7] = true := by decide +kernel
theorem subd7_1_4633 : subd7_1 [6, 4, 8] = true := by decide +kernel
theorem subd7_1_4634 : subd7_1 [6, 4, 9] = true := by decide +kernel
theorem subd7_1_4635 : subd7_1 [6, 4, 10] = true := by decide +kernel
theorem subd7_1_4636 : subd7_1 [6, 4, 11] = true := by decide +kernel
theorem subd7_1_4637 : subd7_1 [6, 5, -6] = true := by decide +kernel
theorem subd7_1_4638 : subd7_1 [6, 5, -5] = true := by decide +kernel
theorem subd7_1_4639 : subd7_1 [6, 5, -4] = true := by decide +kernel
theorem sbd7_1_144 : ∀ q ∈ blkd7_1_144, subd7_1 q = true := by
  unfold blkd7_1_144
  exact List.forall_mem_cons.2 ⟨subd7_1_4608, List.forall_mem_cons.2 ⟨subd7_1_4609, List.forall_mem_cons.2 ⟨subd7_1_4610, List.forall_mem_cons.2 ⟨subd7_1_4611, List.forall_mem_cons.2 ⟨subd7_1_4612, List.forall_mem_cons.2 ⟨subd7_1_4613, List.forall_mem_cons.2 ⟨subd7_1_4614, List.forall_mem_cons.2 ⟨subd7_1_4615, List.forall_mem_cons.2 ⟨subd7_1_4616, List.forall_mem_cons.2 ⟨subd7_1_4617, List.forall_mem_cons.2 ⟨subd7_1_4618, List.forall_mem_cons.2 ⟨subd7_1_4619, List.forall_mem_cons.2 ⟨subd7_1_4620, List.forall_mem_cons.2 ⟨subd7_1_4621, List.forall_mem_cons.2 ⟨subd7_1_4622, List.forall_mem_cons.2 ⟨subd7_1_4623, List.forall_mem_cons.2 ⟨subd7_1_4624, List.forall_mem_cons.2 ⟨subd7_1_4625, List.forall_mem_cons.2 ⟨subd7_1_4626, List.forall_mem_cons.2 ⟨subd7_1_4627, List.forall_mem_cons.2 ⟨subd7_1_4628, List.forall_mem_cons.2 ⟨subd7_1_4629, List.forall_mem_cons.2 ⟨subd7_1_4630, List.forall_mem_cons.2 ⟨subd7_1_4631, List.forall_mem_cons.2 ⟨subd7_1_4632, List.forall_mem_cons.2 ⟨subd7_1_4633, List.forall_mem_cons.2 ⟨subd7_1_4634, List.forall_mem_cons.2 ⟨subd7_1_4635, List.forall_mem_cons.2 ⟨subd7_1_4636, List.forall_mem_cons.2 ⟨subd7_1_4637, List.forall_mem_cons.2 ⟨subd7_1_4638, List.forall_mem_cons.2 ⟨subd7_1_4639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4640 : subd7_1 [6, 5, -3] = true := by decide +kernel
theorem subd7_1_4641 : subd7_1 [6, 5, -2] = true := by decide +kernel
theorem subd7_1_4642 : subd7_1 [6, 5, -1] = true := by decide +kernel
theorem subd7_1_4643 : subd7_1 [6, 5, 0] = true := by decide +kernel
theorem subd7_1_4644 : subd7_1 [6, 5, 1] = true := by decide +kernel
theorem subd7_1_4645 : subd7_1 [6, 5, 2] = true := by decide +kernel
theorem subd7_1_4646 : subd7_1 [6, 5, 3] = true := by decide +kernel
theorem subd7_1_4647 : subd7_1 [6, 5, 4] = true := by decide +kernel
theorem subd7_1_4648 : subd7_1 [6, 5, 5] = true := by decide +kernel
theorem subd7_1_4649 : subd7_1 [6, 5, 6] = true := by decide +kernel
theorem subd7_1_4650 : subd7_1 [6, 5, 7] = true := by decide +kernel
theorem subd7_1_4651 : subd7_1 [6, 5, 8] = true := by decide +kernel
theorem subd7_1_4652 : subd7_1 [6, 5, 9] = true := by decide +kernel
theorem subd7_1_4653 : subd7_1 [6, 5, 10] = true := by decide +kernel
theorem subd7_1_4654 : subd7_1 [6, 5, 11] = true := by decide +kernel
theorem subd7_1_4655 : subd7_1 [6, 6, -5] = true := by decide +kernel
theorem subd7_1_4656 : subd7_1 [6, 6, -4] = true := by decide +kernel
theorem subd7_1_4657 : subd7_1 [6, 6, -3] = true := by decide +kernel
theorem subd7_1_4658 : subd7_1 [6, 6, -2] = true := by decide +kernel
theorem subd7_1_4659 : subd7_1 [6, 6, -1] = true := by decide +kernel
theorem subd7_1_4660 : subd7_1 [6, 6, 0] = true := by decide +kernel
theorem subd7_1_4661 : subd7_1 [6, 6, 1] = true := by decide +kernel
theorem subd7_1_4662 : subd7_1 [6, 6, 2] = true := by decide +kernel
theorem subd7_1_4663 : subd7_1 [6, 6, 3] = true := by decide +kernel
theorem subd7_1_4664 : subd7_1 [6, 6, 4] = true := by decide +kernel
theorem subd7_1_4665 : subd7_1 [6, 6, 5] = true := by decide +kernel
theorem subd7_1_4666 : subd7_1 [6, 6, 6] = true := by decide +kernel
theorem subd7_1_4667 : subd7_1 [6, 6, 7] = true := by decide +kernel
theorem subd7_1_4668 : subd7_1 [6, 6, 8] = true := by decide +kernel
theorem subd7_1_4669 : subd7_1 [6, 6, 9] = true := by decide +kernel
theorem subd7_1_4670 : subd7_1 [6, 6, 10] = true := by decide +kernel
theorem subd7_1_4671 : subd7_1 [6, 7, -4] = true := by decide +kernel
theorem sbd7_1_145 : ∀ q ∈ blkd7_1_145, subd7_1 q = true := by
  unfold blkd7_1_145
  exact List.forall_mem_cons.2 ⟨subd7_1_4640, List.forall_mem_cons.2 ⟨subd7_1_4641, List.forall_mem_cons.2 ⟨subd7_1_4642, List.forall_mem_cons.2 ⟨subd7_1_4643, List.forall_mem_cons.2 ⟨subd7_1_4644, List.forall_mem_cons.2 ⟨subd7_1_4645, List.forall_mem_cons.2 ⟨subd7_1_4646, List.forall_mem_cons.2 ⟨subd7_1_4647, List.forall_mem_cons.2 ⟨subd7_1_4648, List.forall_mem_cons.2 ⟨subd7_1_4649, List.forall_mem_cons.2 ⟨subd7_1_4650, List.forall_mem_cons.2 ⟨subd7_1_4651, List.forall_mem_cons.2 ⟨subd7_1_4652, List.forall_mem_cons.2 ⟨subd7_1_4653, List.forall_mem_cons.2 ⟨subd7_1_4654, List.forall_mem_cons.2 ⟨subd7_1_4655, List.forall_mem_cons.2 ⟨subd7_1_4656, List.forall_mem_cons.2 ⟨subd7_1_4657, List.forall_mem_cons.2 ⟨subd7_1_4658, List.forall_mem_cons.2 ⟨subd7_1_4659, List.forall_mem_cons.2 ⟨subd7_1_4660, List.forall_mem_cons.2 ⟨subd7_1_4661, List.forall_mem_cons.2 ⟨subd7_1_4662, List.forall_mem_cons.2 ⟨subd7_1_4663, List.forall_mem_cons.2 ⟨subd7_1_4664, List.forall_mem_cons.2 ⟨subd7_1_4665, List.forall_mem_cons.2 ⟨subd7_1_4666, List.forall_mem_cons.2 ⟨subd7_1_4667, List.forall_mem_cons.2 ⟨subd7_1_4668, List.forall_mem_cons.2 ⟨subd7_1_4669, List.forall_mem_cons.2 ⟨subd7_1_4670, List.forall_mem_cons.2 ⟨subd7_1_4671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4672 : subd7_1 [6, 7, -3] = true := by decide +kernel
theorem subd7_1_4673 : subd7_1 [6, 7, -2] = true := by decide +kernel
theorem subd7_1_4674 : subd7_1 [6, 7, -1] = true := by decide +kernel
theorem subd7_1_4675 : subd7_1 [6, 7, 0] = true := by decide +kernel
theorem subd7_1_4676 : subd7_1 [6, 7, 1] = true := by decide +kernel
theorem subd7_1_4677 : subd7_1 [6, 7, 2] = true := by decide +kernel
theorem subd7_1_4678 : subd7_1 [6, 7, 3] = true := by decide +kernel
theorem subd7_1_4679 : subd7_1 [6, 7, 4] = true := by decide +kernel
theorem subd7_1_4680 : subd7_1 [6, 7, 5] = true := by decide +kernel
theorem subd7_1_4681 : subd7_1 [6, 7, 6] = true := by decide +kernel
theorem subd7_1_4682 : subd7_1 [6, 7, 7] = true := by decide +kernel
theorem subd7_1_4683 : subd7_1 [6, 7, 8] = true := by decide +kernel
theorem subd7_1_4684 : subd7_1 [6, 7, 9] = true := by decide +kernel
theorem subd7_1_4685 : subd7_1 [6, 8] = true := by decide +kernel
theorem subd7_1_4686 : subd7_1 [7, -6] = true := by decide +kernel
theorem subd7_1_4687 : subd7_1 [7, -5] = true := by decide +kernel
theorem subd7_1_4688 : subd7_1 [7, -4] = true := by decide +kernel
theorem subd7_1_4689 : subd7_1 [7, -3, -5] = true := by decide +kernel
theorem subd7_1_4690 : subd7_1 [7, -3, -4] = true := by decide +kernel
theorem subd7_1_4691 : subd7_1 [7, -3, -3] = true := by decide +kernel
theorem subd7_1_4692 : subd7_1 [7, -3, -2] = true := by decide +kernel
theorem subd7_1_4693 : subd7_1 [7, -3, -1] = true := by decide +kernel
theorem subd7_1_4694 : subd7_1 [7, -3, 0] = true := by decide +kernel
theorem subd7_1_4695 : subd7_1 [7, -3, 1] = true := by decide +kernel
theorem subd7_1_4696 : subd7_1 [7, -3, 2] = true := by decide +kernel
theorem subd7_1_4697 : subd7_1 [7, -3, 3] = true := by decide +kernel
theorem subd7_1_4698 : subd7_1 [7, -3, 4] = true := by decide +kernel
theorem subd7_1_4699 : subd7_1 [7, -3, 5] = true := by decide +kernel
theorem subd7_1_4700 : subd7_1 [7, -3, 6] = true := by decide +kernel
theorem subd7_1_4701 : subd7_1 [7, -3, 7] = true := by decide +kernel
theorem subd7_1_4702 : subd7_1 [7, -3, 8] = true := by decide +kernel
theorem subd7_1_4703 : subd7_1 [7, -2, -6] = true := by decide +kernel
theorem sbd7_1_146 : ∀ q ∈ blkd7_1_146, subd7_1 q = true := by
  unfold blkd7_1_146
  exact List.forall_mem_cons.2 ⟨subd7_1_4672, List.forall_mem_cons.2 ⟨subd7_1_4673, List.forall_mem_cons.2 ⟨subd7_1_4674, List.forall_mem_cons.2 ⟨subd7_1_4675, List.forall_mem_cons.2 ⟨subd7_1_4676, List.forall_mem_cons.2 ⟨subd7_1_4677, List.forall_mem_cons.2 ⟨subd7_1_4678, List.forall_mem_cons.2 ⟨subd7_1_4679, List.forall_mem_cons.2 ⟨subd7_1_4680, List.forall_mem_cons.2 ⟨subd7_1_4681, List.forall_mem_cons.2 ⟨subd7_1_4682, List.forall_mem_cons.2 ⟨subd7_1_4683, List.forall_mem_cons.2 ⟨subd7_1_4684, List.forall_mem_cons.2 ⟨subd7_1_4685, List.forall_mem_cons.2 ⟨subd7_1_4686, List.forall_mem_cons.2 ⟨subd7_1_4687, List.forall_mem_cons.2 ⟨subd7_1_4688, List.forall_mem_cons.2 ⟨subd7_1_4689, List.forall_mem_cons.2 ⟨subd7_1_4690, List.forall_mem_cons.2 ⟨subd7_1_4691, List.forall_mem_cons.2 ⟨subd7_1_4692, List.forall_mem_cons.2 ⟨subd7_1_4693, List.forall_mem_cons.2 ⟨subd7_1_4694, List.forall_mem_cons.2 ⟨subd7_1_4695, List.forall_mem_cons.2 ⟨subd7_1_4696, List.forall_mem_cons.2 ⟨subd7_1_4697, List.forall_mem_cons.2 ⟨subd7_1_4698, List.forall_mem_cons.2 ⟨subd7_1_4699, List.forall_mem_cons.2 ⟨subd7_1_4700, List.forall_mem_cons.2 ⟨subd7_1_4701, List.forall_mem_cons.2 ⟨subd7_1_4702, List.forall_mem_cons.2 ⟨subd7_1_4703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4704 : subd7_1 [7, -2, -5] = true := by decide +kernel
theorem subd7_1_4705 : subd7_1 [7, -2, -4] = true := by decide +kernel
theorem subd7_1_4706 : subd7_1 [7, -2, -3] = true := by decide +kernel
theorem subd7_1_4707 : subd7_1 [7, -2, -2] = true := by decide +kernel
theorem subd7_1_4708 : subd7_1 [7, -2, -1] = true := by decide +kernel
theorem subd7_1_4709 : subd7_1 [7, -2, 0] = true := by decide +kernel
theorem subd7_1_4710 : subd7_1 [7, -2, 1] = true := by decide +kernel
theorem subd7_1_4711 : subd7_1 [7, -2, 2] = true := by decide +kernel
theorem subd7_1_4712 : subd7_1 [7, -2, 3] = true := by decide +kernel
theorem subd7_1_4713 : subd7_1 [7, -2, 4] = true := by decide +kernel
theorem subd7_1_4714 : subd7_1 [7, -2, 5] = true := by decide +kernel
theorem subd7_1_4715 : subd7_1 [7, -2, 6] = true := by decide +kernel
theorem subd7_1_4716 : subd7_1 [7, -2, 7] = true := by decide +kernel
theorem subd7_1_4717 : subd7_1 [7, -2, 8] = true := by decide +kernel
theorem subd7_1_4718 : subd7_1 [7, -2, 9] = true := by decide +kernel
theorem subd7_1_4719 : subd7_1 [7, -1, -7] = true := by decide +kernel
theorem subd7_1_4720 : subd7_1 [7, -1, -6] = true := by decide +kernel
theorem subd7_1_4721 : subd7_1 [7, -1, -5] = true := by decide +kernel
theorem subd7_1_4722 : subd7_1 [7, -1, -4] = true := by decide +kernel
theorem subd7_1_4723 : subd7_1 [7, -1, -3] = true := by decide +kernel
theorem subd7_1_4724 : subd7_1 [7, -1, -2] = true := by decide +kernel
theorem subd7_1_4725 : subd7_1 [7, -1, -1] = true := by decide +kernel
theorem subd7_1_4726 : subd7_1 [7, -1, 0] = true := by decide +kernel
theorem subd7_1_4727 : subd7_1 [7, -1, 1] = true := by decide +kernel
theorem subd7_1_4728 : subd7_1 [7, -1, 2] = true := by decide +kernel
theorem subd7_1_4729 : subd7_1 [7, -1, 3] = true := by decide +kernel
theorem subd7_1_4730 : subd7_1 [7, -1, 4] = true := by decide +kernel
theorem subd7_1_4731 : subd7_1 [7, -1, 5] = true := by decide +kernel
theorem subd7_1_4732 : subd7_1 [7, -1, 6] = true := by decide +kernel
theorem subd7_1_4733 : subd7_1 [7, -1, 7] = true := by decide +kernel
theorem subd7_1_4734 : subd7_1 [7, -1, 8] = true := by decide +kernel
theorem subd7_1_4735 : subd7_1 [7, -1, 9] = true := by decide +kernel
theorem sbd7_1_147 : ∀ q ∈ blkd7_1_147, subd7_1 q = true := by
  unfold blkd7_1_147
  exact List.forall_mem_cons.2 ⟨subd7_1_4704, List.forall_mem_cons.2 ⟨subd7_1_4705, List.forall_mem_cons.2 ⟨subd7_1_4706, List.forall_mem_cons.2 ⟨subd7_1_4707, List.forall_mem_cons.2 ⟨subd7_1_4708, List.forall_mem_cons.2 ⟨subd7_1_4709, List.forall_mem_cons.2 ⟨subd7_1_4710, List.forall_mem_cons.2 ⟨subd7_1_4711, List.forall_mem_cons.2 ⟨subd7_1_4712, List.forall_mem_cons.2 ⟨subd7_1_4713, List.forall_mem_cons.2 ⟨subd7_1_4714, List.forall_mem_cons.2 ⟨subd7_1_4715, List.forall_mem_cons.2 ⟨subd7_1_4716, List.forall_mem_cons.2 ⟨subd7_1_4717, List.forall_mem_cons.2 ⟨subd7_1_4718, List.forall_mem_cons.2 ⟨subd7_1_4719, List.forall_mem_cons.2 ⟨subd7_1_4720, List.forall_mem_cons.2 ⟨subd7_1_4721, List.forall_mem_cons.2 ⟨subd7_1_4722, List.forall_mem_cons.2 ⟨subd7_1_4723, List.forall_mem_cons.2 ⟨subd7_1_4724, List.forall_mem_cons.2 ⟨subd7_1_4725, List.forall_mem_cons.2 ⟨subd7_1_4726, List.forall_mem_cons.2 ⟨subd7_1_4727, List.forall_mem_cons.2 ⟨subd7_1_4728, List.forall_mem_cons.2 ⟨subd7_1_4729, List.forall_mem_cons.2 ⟨subd7_1_4730, List.forall_mem_cons.2 ⟨subd7_1_4731, List.forall_mem_cons.2 ⟨subd7_1_4732, List.forall_mem_cons.2 ⟨subd7_1_4733, List.forall_mem_cons.2 ⟨subd7_1_4734, List.forall_mem_cons.2 ⟨subd7_1_4735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4736 : subd7_1 [7, -1, 10] = true := by decide +kernel
theorem subd7_1_4737 : subd7_1 [7, 0, -7] = true := by decide +kernel
theorem subd7_1_4738 : subd7_1 [7, 0, -6] = true := by decide +kernel
theorem subd7_1_4739 : subd7_1 [7, 0, -5] = true := by decide +kernel
theorem subd7_1_4740 : subd7_1 [7, 0, -4] = true := by decide +kernel
theorem subd7_1_4741 : subd7_1 [7, 0, -3] = true := by decide +kernel
theorem subd7_1_4742 : subd7_1 [7, 0, -2] = true := by decide +kernel
theorem subd7_1_4743 : subd7_1 [7, 0, -1] = true := by decide +kernel
theorem subd7_1_4744 : subd7_1 [7, 0, 0] = true := by decide +kernel
theorem subd7_1_4745 : subd7_1 [7, 0, 1] = true := by decide +kernel
theorem subd7_1_4746 : subd7_1 [7, 0, 2] = true := by decide +kernel
theorem subd7_1_4747 : subd7_1 [7, 0, 3] = true := by decide +kernel
theorem subd7_1_4748 : subd7_1 [7, 0, 4] = true := by decide +kernel
theorem subd7_1_4749 : subd7_1 [7, 0, 5] = true := by decide +kernel
theorem subd7_1_4750 : subd7_1 [7, 0, 6] = true := by decide +kernel
theorem subd7_1_4751 : subd7_1 [7, 0, 7] = true := by decide +kernel
theorem subd7_1_4752 : subd7_1 [7, 0, 8] = true := by decide +kernel
theorem subd7_1_4753 : subd7_1 [7, 0, 9] = true := by decide +kernel
theorem subd7_1_4754 : subd7_1 [7, 0, 10] = true := by decide +kernel
theorem subd7_1_4755 : subd7_1 [7, 1, -7] = true := by decide +kernel
theorem subd7_1_4756 : subd7_1 [7, 1, -6] = true := by decide +kernel
theorem subd7_1_4757 : subd7_1 [7, 1, -5] = true := by decide +kernel
theorem subd7_1_4758 : subd7_1 [7, 1, -4] = true := by decide +kernel
theorem subd7_1_4759 : subd7_1 [7, 1, -3] = true := by decide +kernel
theorem subd7_1_4760 : subd7_1 [7, 1, -2] = true := by decide +kernel
theorem subd7_1_4761 : subd7_1 [7, 1, -1] = true := by decide +kernel
theorem subd7_1_4762 : subd7_1 [7, 1, 0] = true := by decide +kernel
theorem subd7_1_4763 : subd7_1 [7, 1, 1] = true := by decide +kernel
theorem subd7_1_4764 : subd7_1 [7, 1, 2] = true := by decide +kernel
theorem subd7_1_4765 : subd7_1 [7, 1, 3] = true := by decide +kernel
theorem subd7_1_4766 : subd7_1 [7, 1, 4] = true := by decide +kernel
theorem subd7_1_4767 : subd7_1 [7, 1, 5] = true := by decide +kernel
theorem sbd7_1_148 : ∀ q ∈ blkd7_1_148, subd7_1 q = true := by
  unfold blkd7_1_148
  exact List.forall_mem_cons.2 ⟨subd7_1_4736, List.forall_mem_cons.2 ⟨subd7_1_4737, List.forall_mem_cons.2 ⟨subd7_1_4738, List.forall_mem_cons.2 ⟨subd7_1_4739, List.forall_mem_cons.2 ⟨subd7_1_4740, List.forall_mem_cons.2 ⟨subd7_1_4741, List.forall_mem_cons.2 ⟨subd7_1_4742, List.forall_mem_cons.2 ⟨subd7_1_4743, List.forall_mem_cons.2 ⟨subd7_1_4744, List.forall_mem_cons.2 ⟨subd7_1_4745, List.forall_mem_cons.2 ⟨subd7_1_4746, List.forall_mem_cons.2 ⟨subd7_1_4747, List.forall_mem_cons.2 ⟨subd7_1_4748, List.forall_mem_cons.2 ⟨subd7_1_4749, List.forall_mem_cons.2 ⟨subd7_1_4750, List.forall_mem_cons.2 ⟨subd7_1_4751, List.forall_mem_cons.2 ⟨subd7_1_4752, List.forall_mem_cons.2 ⟨subd7_1_4753, List.forall_mem_cons.2 ⟨subd7_1_4754, List.forall_mem_cons.2 ⟨subd7_1_4755, List.forall_mem_cons.2 ⟨subd7_1_4756, List.forall_mem_cons.2 ⟨subd7_1_4757, List.forall_mem_cons.2 ⟨subd7_1_4758, List.forall_mem_cons.2 ⟨subd7_1_4759, List.forall_mem_cons.2 ⟨subd7_1_4760, List.forall_mem_cons.2 ⟨subd7_1_4761, List.forall_mem_cons.2 ⟨subd7_1_4762, List.forall_mem_cons.2 ⟨subd7_1_4763, List.forall_mem_cons.2 ⟨subd7_1_4764, List.forall_mem_cons.2 ⟨subd7_1_4765, List.forall_mem_cons.2 ⟨subd7_1_4766, List.forall_mem_cons.2 ⟨subd7_1_4767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4768 : subd7_1 [7, 1, 6] = true := by decide +kernel
theorem subd7_1_4769 : subd7_1 [7, 1, 7] = true := by decide +kernel
theorem subd7_1_4770 : subd7_1 [7, 1, 8] = true := by decide +kernel
theorem subd7_1_4771 : subd7_1 [7, 1, 9] = true := by decide +kernel
theorem subd7_1_4772 : subd7_1 [7, 1, 10] = true := by decide +kernel
theorem subd7_1_4773 : subd7_1 [7, 1, 11] = true := by decide +kernel
theorem subd7_1_4774 : subd7_1 [7, 2, -7] = true := by decide +kernel
theorem subd7_1_4775 : subd7_1 [7, 2, -6] = true := by decide +kernel
theorem subd7_1_4776 : subd7_1 [7, 2, -5] = true := by decide +kernel
theorem subd7_1_4777 : subd7_1 [7, 2, -4] = true := by decide +kernel
theorem subd7_1_4778 : subd7_1 [7, 2, -3] = true := by decide +kernel
theorem subd7_1_4779 : subd7_1 [7, 2, -2] = true := by decide +kernel
theorem subd7_1_4780 : subd7_1 [7, 2, -1] = true := by decide +kernel
theorem subd7_1_4781 : subd7_1 [7, 2, 0] = true := by decide +kernel
theorem subd7_1_4782 : subd7_1 [7, 2, 1] = true := by decide +kernel
theorem subd7_1_4783 : subd7_1 [7, 2, 2] = true := by decide +kernel
theorem subd7_1_4784 : subd7_1 [7, 2, 3] = true := by decide +kernel
theorem subd7_1_4785 : subd7_1 [7, 2, 4] = true := by decide +kernel
theorem subd7_1_4786 : subd7_1 [7, 2, 5] = true := by decide +kernel
theorem subd7_1_4787 : subd7_1 [7, 2, 6] = true := by decide +kernel
theorem subd7_1_4788 : subd7_1 [7, 2, 7] = true := by decide +kernel
theorem subd7_1_4789 : subd7_1 [7, 2, 8] = true := by decide +kernel
theorem subd7_1_4790 : subd7_1 [7, 2, 9] = true := by decide +kernel
theorem subd7_1_4791 : subd7_1 [7, 2, 10] = true := by decide +kernel
theorem subd7_1_4792 : subd7_1 [7, 2, 11] = true := by decide +kernel
theorem subd7_1_4793 : subd7_1 [7, 3, -6] = true := by decide +kernel
theorem subd7_1_4794 : subd7_1 [7, 3, -5] = true := by decide +kernel
theorem subd7_1_4795 : subd7_1 [7, 3, -4] = true := by decide +kernel
theorem subd7_1_4796 : subd7_1 [7, 3, -3] = true := by decide +kernel
theorem subd7_1_4797 : subd7_1 [7, 3, -2] = true := by decide +kernel
theorem subd7_1_4798 : subd7_1 [7, 3, -1] = true := by decide +kernel
theorem subd7_1_4799 : subd7_1 [7, 3, 0] = true := by decide +kernel
theorem sbd7_1_149 : ∀ q ∈ blkd7_1_149, subd7_1 q = true := by
  unfold blkd7_1_149
  exact List.forall_mem_cons.2 ⟨subd7_1_4768, List.forall_mem_cons.2 ⟨subd7_1_4769, List.forall_mem_cons.2 ⟨subd7_1_4770, List.forall_mem_cons.2 ⟨subd7_1_4771, List.forall_mem_cons.2 ⟨subd7_1_4772, List.forall_mem_cons.2 ⟨subd7_1_4773, List.forall_mem_cons.2 ⟨subd7_1_4774, List.forall_mem_cons.2 ⟨subd7_1_4775, List.forall_mem_cons.2 ⟨subd7_1_4776, List.forall_mem_cons.2 ⟨subd7_1_4777, List.forall_mem_cons.2 ⟨subd7_1_4778, List.forall_mem_cons.2 ⟨subd7_1_4779, List.forall_mem_cons.2 ⟨subd7_1_4780, List.forall_mem_cons.2 ⟨subd7_1_4781, List.forall_mem_cons.2 ⟨subd7_1_4782, List.forall_mem_cons.2 ⟨subd7_1_4783, List.forall_mem_cons.2 ⟨subd7_1_4784, List.forall_mem_cons.2 ⟨subd7_1_4785, List.forall_mem_cons.2 ⟨subd7_1_4786, List.forall_mem_cons.2 ⟨subd7_1_4787, List.forall_mem_cons.2 ⟨subd7_1_4788, List.forall_mem_cons.2 ⟨subd7_1_4789, List.forall_mem_cons.2 ⟨subd7_1_4790, List.forall_mem_cons.2 ⟨subd7_1_4791, List.forall_mem_cons.2 ⟨subd7_1_4792, List.forall_mem_cons.2 ⟨subd7_1_4793, List.forall_mem_cons.2 ⟨subd7_1_4794, List.forall_mem_cons.2 ⟨subd7_1_4795, List.forall_mem_cons.2 ⟨subd7_1_4796, List.forall_mem_cons.2 ⟨subd7_1_4797, List.forall_mem_cons.2 ⟨subd7_1_4798, List.forall_mem_cons.2 ⟨subd7_1_4799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4800 : subd7_1 [7, 3, 1] = true := by decide +kernel
theorem subd7_1_4801 : subd7_1 [7, 3, 2] = true := by decide +kernel
theorem subd7_1_4802 : subd7_1 [7, 3, 3] = true := by decide +kernel
theorem subd7_1_4803 : subd7_1 [7, 3, 4] = true := by decide +kernel
theorem subd7_1_4804 : subd7_1 [7, 3, 5] = true := by decide +kernel
theorem subd7_1_4805 : subd7_1 [7, 3, 6] = true := by decide +kernel
theorem subd7_1_4806 : subd7_1 [7, 3, 7] = true := by decide +kernel
theorem subd7_1_4807 : subd7_1 [7, 3, 8] = true := by decide +kernel
theorem subd7_1_4808 : subd7_1 [7, 3, 9] = true := by decide +kernel
theorem subd7_1_4809 : subd7_1 [7, 3, 10] = true := by decide +kernel
theorem subd7_1_4810 : subd7_1 [7, 3, 11] = true := by decide +kernel
theorem subd7_1_4811 : subd7_1 [7, 4, -5] = true := by decide +kernel
theorem subd7_1_4812 : subd7_1 [7, 4, -4] = true := by decide +kernel
theorem subd7_1_4813 : subd7_1 [7, 4, -3] = true := by decide +kernel
theorem subd7_1_4814 : subd7_1 [7, 4, -2] = true := by decide +kernel
theorem subd7_1_4815 : subd7_1 [7, 4, -1] = true := by decide +kernel
theorem subd7_1_4816 : subd7_1 [7, 4, 0] = true := by decide +kernel
theorem subd7_1_4817 : subd7_1 [7, 4, 1] = true := by decide +kernel
theorem subd7_1_4818 : subd7_1 [7, 4, 2] = true := by decide +kernel
theorem subd7_1_4819 : subd7_1 [7, 4, 3] = true := by decide +kernel
theorem subd7_1_4820 : subd7_1 [7, 4, 4] = true := by decide +kernel
theorem subd7_1_4821 : subd7_1 [7, 4, 5] = true := by decide +kernel
theorem subd7_1_4822 : subd7_1 [7, 4, 6] = true := by decide +kernel
theorem subd7_1_4823 : subd7_1 [7, 4, 7] = true := by decide +kernel
theorem subd7_1_4824 : subd7_1 [7, 4, 8] = true := by decide +kernel
theorem subd7_1_4825 : subd7_1 [7, 4, 9] = true := by decide +kernel
theorem subd7_1_4826 : subd7_1 [7, 4, 10] = true := by decide +kernel
theorem subd7_1_4827 : subd7_1 [7, 5, -5] = true := by decide +kernel
theorem subd7_1_4828 : subd7_1 [7, 5, -4] = true := by decide +kernel
theorem subd7_1_4829 : subd7_1 [7, 5, -3] = true := by decide +kernel
theorem subd7_1_4830 : subd7_1 [7, 5, -2] = true := by decide +kernel
theorem subd7_1_4831 : subd7_1 [7, 5, -1] = true := by decide +kernel
theorem sbd7_1_150 : ∀ q ∈ blkd7_1_150, subd7_1 q = true := by
  unfold blkd7_1_150
  exact List.forall_mem_cons.2 ⟨subd7_1_4800, List.forall_mem_cons.2 ⟨subd7_1_4801, List.forall_mem_cons.2 ⟨subd7_1_4802, List.forall_mem_cons.2 ⟨subd7_1_4803, List.forall_mem_cons.2 ⟨subd7_1_4804, List.forall_mem_cons.2 ⟨subd7_1_4805, List.forall_mem_cons.2 ⟨subd7_1_4806, List.forall_mem_cons.2 ⟨subd7_1_4807, List.forall_mem_cons.2 ⟨subd7_1_4808, List.forall_mem_cons.2 ⟨subd7_1_4809, List.forall_mem_cons.2 ⟨subd7_1_4810, List.forall_mem_cons.2 ⟨subd7_1_4811, List.forall_mem_cons.2 ⟨subd7_1_4812, List.forall_mem_cons.2 ⟨subd7_1_4813, List.forall_mem_cons.2 ⟨subd7_1_4814, List.forall_mem_cons.2 ⟨subd7_1_4815, List.forall_mem_cons.2 ⟨subd7_1_4816, List.forall_mem_cons.2 ⟨subd7_1_4817, List.forall_mem_cons.2 ⟨subd7_1_4818, List.forall_mem_cons.2 ⟨subd7_1_4819, List.forall_mem_cons.2 ⟨subd7_1_4820, List.forall_mem_cons.2 ⟨subd7_1_4821, List.forall_mem_cons.2 ⟨subd7_1_4822, List.forall_mem_cons.2 ⟨subd7_1_4823, List.forall_mem_cons.2 ⟨subd7_1_4824, List.forall_mem_cons.2 ⟨subd7_1_4825, List.forall_mem_cons.2 ⟨subd7_1_4826, List.forall_mem_cons.2 ⟨subd7_1_4827, List.forall_mem_cons.2 ⟨subd7_1_4828, List.forall_mem_cons.2 ⟨subd7_1_4829, List.forall_mem_cons.2 ⟨subd7_1_4830, List.forall_mem_cons.2 ⟨subd7_1_4831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4832 : subd7_1 [7, 5, 0] = true := by decide +kernel
theorem subd7_1_4833 : subd7_1 [7, 5, 1] = true := by decide +kernel
theorem subd7_1_4834 : subd7_1 [7, 5, 2] = true := by decide +kernel
theorem subd7_1_4835 : subd7_1 [7, 5, 3] = true := by decide +kernel
theorem subd7_1_4836 : subd7_1 [7, 5, 4] = true := by decide +kernel
theorem subd7_1_4837 : subd7_1 [7, 5, 5] = true := by decide +kernel
theorem subd7_1_4838 : subd7_1 [7, 5, 6] = true := by decide +kernel
theorem subd7_1_4839 : subd7_1 [7, 5, 7] = true := by decide +kernel
theorem subd7_1_4840 : subd7_1 [7, 5, 8] = true := by decide +kernel
theorem subd7_1_4841 : subd7_1 [7, 5, 9] = true := by decide +kernel
theorem subd7_1_4842 : subd7_1 [7, 5, 10] = true := by decide +kernel
theorem subd7_1_4843 : subd7_1 [7, 6] = true := by decide +kernel
theorem subd7_1_4844 : subd7_1 [7, 7] = true := by decide +kernel
theorem subd7_1_4845 : subd7_1 [8, -4] = true := by decide +kernel
theorem subd7_1_4846 : subd7_1 [8, -3] = true := by decide +kernel
theorem subd7_1_4847 : subd7_1 [8, -2] = true := by decide +kernel
theorem subd7_1_4848 : subd7_1 [8, -1] = true := by decide +kernel
theorem subd7_1_4849 : subd7_1 [8, 0, -4] = true := by decide +kernel
theorem subd7_1_4850 : subd7_1 [8, 0, -3] = true := by decide +kernel
theorem subd7_1_4851 : subd7_1 [8, 0, -2] = true := by decide +kernel
theorem subd7_1_4852 : subd7_1 [8, 0, -1] = true := by decide +kernel
theorem subd7_1_4853 : subd7_1 [8, 0, 0] = true := by decide +kernel
theorem subd7_1_4854 : subd7_1 [8, 0, 1] = true := by decide +kernel
theorem subd7_1_4855 : subd7_1 [8, 0, 2] = true := by decide +kernel
theorem subd7_1_4856 : subd7_1 [8, 0, 3] = true := by decide +kernel
theorem subd7_1_4857 : subd7_1 [8, 0, 4] = true := by decide +kernel
theorem subd7_1_4858 : subd7_1 [8, 0, 5] = true := by decide +kernel
theorem subd7_1_4859 : subd7_1 [8, 0, 6] = true := by decide +kernel
theorem subd7_1_4860 : subd7_1 [8, 0, 7] = true := by decide +kernel
theorem subd7_1_4861 : subd7_1 [8, 0, 8] = true := by decide +kernel
theorem subd7_1_4862 : subd7_1 [8, 0, 9] = true := by decide +kernel
theorem subd7_1_4863 : subd7_1 [8, 1, -5] = true := by decide +kernel
theorem sbd7_1_151 : ∀ q ∈ blkd7_1_151, subd7_1 q = true := by
  unfold blkd7_1_151
  exact List.forall_mem_cons.2 ⟨subd7_1_4832, List.forall_mem_cons.2 ⟨subd7_1_4833, List.forall_mem_cons.2 ⟨subd7_1_4834, List.forall_mem_cons.2 ⟨subd7_1_4835, List.forall_mem_cons.2 ⟨subd7_1_4836, List.forall_mem_cons.2 ⟨subd7_1_4837, List.forall_mem_cons.2 ⟨subd7_1_4838, List.forall_mem_cons.2 ⟨subd7_1_4839, List.forall_mem_cons.2 ⟨subd7_1_4840, List.forall_mem_cons.2 ⟨subd7_1_4841, List.forall_mem_cons.2 ⟨subd7_1_4842, List.forall_mem_cons.2 ⟨subd7_1_4843, List.forall_mem_cons.2 ⟨subd7_1_4844, List.forall_mem_cons.2 ⟨subd7_1_4845, List.forall_mem_cons.2 ⟨subd7_1_4846, List.forall_mem_cons.2 ⟨subd7_1_4847, List.forall_mem_cons.2 ⟨subd7_1_4848, List.forall_mem_cons.2 ⟨subd7_1_4849, List.forall_mem_cons.2 ⟨subd7_1_4850, List.forall_mem_cons.2 ⟨subd7_1_4851, List.forall_mem_cons.2 ⟨subd7_1_4852, List.forall_mem_cons.2 ⟨subd7_1_4853, List.forall_mem_cons.2 ⟨subd7_1_4854, List.forall_mem_cons.2 ⟨subd7_1_4855, List.forall_mem_cons.2 ⟨subd7_1_4856, List.forall_mem_cons.2 ⟨subd7_1_4857, List.forall_mem_cons.2 ⟨subd7_1_4858, List.forall_mem_cons.2 ⟨subd7_1_4859, List.forall_mem_cons.2 ⟨subd7_1_4860, List.forall_mem_cons.2 ⟨subd7_1_4861, List.forall_mem_cons.2 ⟨subd7_1_4862, List.forall_mem_cons.2 ⟨subd7_1_4863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_1_4864 : subd7_1 [8, 1, -4] = true := by decide +kernel
theorem subd7_1_4865 : subd7_1 [8, 1, -3] = true := by decide +kernel
theorem subd7_1_4866 : subd7_1 [8, 1, -2] = true := by decide +kernel
theorem subd7_1_4867 : subd7_1 [8, 1, -1] = true := by decide +kernel
theorem subd7_1_4868 : subd7_1 [8, 1, 0] = true := by decide +kernel
theorem subd7_1_4869 : subd7_1 [8, 1, 1] = true := by decide +kernel
theorem subd7_1_4870 : subd7_1 [8, 1, 2] = true := by decide +kernel
theorem subd7_1_4871 : subd7_1 [8, 1, 3] = true := by decide +kernel
theorem subd7_1_4872 : subd7_1 [8, 1, 4] = true := by decide +kernel
theorem subd7_1_4873 : subd7_1 [8, 1, 5] = true := by decide +kernel
theorem subd7_1_4874 : subd7_1 [8, 1, 6] = true := by decide +kernel
theorem subd7_1_4875 : subd7_1 [8, 1, 7] = true := by decide +kernel
theorem subd7_1_4876 : subd7_1 [8, 1, 8] = true := by decide +kernel
theorem subd7_1_4877 : subd7_1 [8, 1, 9] = true := by decide +kernel
theorem subd7_1_4878 : subd7_1 [8, 2, -4] = true := by decide +kernel
theorem subd7_1_4879 : subd7_1 [8, 2, -3] = true := by decide +kernel
theorem subd7_1_4880 : subd7_1 [8, 2, -2] = true := by decide +kernel
theorem subd7_1_4881 : subd7_1 [8, 2, -1] = true := by decide +kernel
theorem subd7_1_4882 : subd7_1 [8, 2, 0] = true := by decide +kernel
theorem subd7_1_4883 : subd7_1 [8, 2, 1] = true := by decide +kernel
theorem subd7_1_4884 : subd7_1 [8, 2, 2] = true := by decide +kernel
theorem subd7_1_4885 : subd7_1 [8, 2, 3] = true := by decide +kernel
theorem subd7_1_4886 : subd7_1 [8, 2, 4] = true := by decide +kernel
theorem subd7_1_4887 : subd7_1 [8, 2, 5] = true := by decide +kernel
theorem subd7_1_4888 : subd7_1 [8, 2, 6] = true := by decide +kernel
theorem subd7_1_4889 : subd7_1 [8, 2, 7] = true := by decide +kernel
theorem subd7_1_4890 : subd7_1 [8, 2, 8] = true := by decide +kernel
theorem subd7_1_4891 : subd7_1 [8, 2, 9] = true := by decide +kernel
theorem subd7_1_4892 : subd7_1 [8, 3, -4] = true := by decide +kernel
theorem subd7_1_4893 : subd7_1 [8, 3, -3] = true := by decide +kernel
theorem subd7_1_4894 : subd7_1 [8, 3, -2] = true := by decide +kernel
theorem subd7_1_4895 : subd7_1 [8, 3, -1] = true := by decide +kernel
theorem sbd7_1_152 : ∀ q ∈ blkd7_1_152, subd7_1 q = true := by
  unfold blkd7_1_152
  exact List.forall_mem_cons.2 ⟨subd7_1_4864, List.forall_mem_cons.2 ⟨subd7_1_4865, List.forall_mem_cons.2 ⟨subd7_1_4866, List.forall_mem_cons.2 ⟨subd7_1_4867, List.forall_mem_cons.2 ⟨subd7_1_4868, List.forall_mem_cons.2 ⟨subd7_1_4869, List.forall_mem_cons.2 ⟨subd7_1_4870, List.forall_mem_cons.2 ⟨subd7_1_4871, List.forall_mem_cons.2 ⟨subd7_1_4872, List.forall_mem_cons.2 ⟨subd7_1_4873, List.forall_mem_cons.2 ⟨subd7_1_4874, List.forall_mem_cons.2 ⟨subd7_1_4875, List.forall_mem_cons.2 ⟨subd7_1_4876, List.forall_mem_cons.2 ⟨subd7_1_4877, List.forall_mem_cons.2 ⟨subd7_1_4878, List.forall_mem_cons.2 ⟨subd7_1_4879, List.forall_mem_cons.2 ⟨subd7_1_4880, List.forall_mem_cons.2 ⟨subd7_1_4881, List.forall_mem_cons.2 ⟨subd7_1_4882, List.forall_mem_cons.2 ⟨subd7_1_4883, List.forall_mem_cons.2 ⟨subd7_1_4884, List.forall_mem_cons.2 ⟨subd7_1_4885, List.forall_mem_cons.2 ⟨subd7_1_4886, List.forall_mem_cons.2 ⟨subd7_1_4887, List.forall_mem_cons.2 ⟨subd7_1_4888, List.forall_mem_cons.2 ⟨subd7_1_4889, List.forall_mem_cons.2 ⟨subd7_1_4890, List.forall_mem_cons.2 ⟨subd7_1_4891, List.forall_mem_cons.2 ⟨subd7_1_4892, List.forall_mem_cons.2 ⟨subd7_1_4893, List.forall_mem_cons.2 ⟨subd7_1_4894, List.forall_mem_cons.2 ⟨subd7_1_4895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
