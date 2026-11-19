import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_1_512 : subd5_1 [1, 3, 3] = true := by decide +kernel
theorem subd5_1_513 : subd5_1 [1, 3, 4] = true := by decide +kernel
theorem subd5_1_514 : subd5_1 [1, 3, 5] = true := by decide +kernel
theorem subd5_1_515 : subd5_1 [1, 3, 6] = true := by decide +kernel
theorem subd5_1_516 : subd5_1 [1, 4] = true := by decide +kernel
theorem subd5_1_517 : subd5_1 [1, 5] = true := by decide +kernel
theorem subd5_1_518 : subd5_1 [1, 6] = true := by decide +kernel
theorem subd5_1_519 : subd5_1 [1, 7] = true := by decide +kernel
theorem subd5_1_520 : subd5_1 [2, -7] = true := by decide +kernel
theorem subd5_1_521 : subd5_1 [2, -6] = true := by decide +kernel
theorem subd5_1_522 : subd5_1 [2, -5] = true := by decide +kernel
theorem subd5_1_523 : subd5_1 [2, -4] = true := by decide +kernel
theorem subd5_1_524 : subd5_1 [2, -3] = true := by decide +kernel
theorem subd5_1_525 : subd5_1 [2, -2] = true := by decide +kernel
theorem subd5_1_526 : subd5_1 [2, -1, -8] = true := by decide +kernel
theorem subd5_1_527 : subd5_1 [2, -1, -7] = true := by decide +kernel
theorem subd5_1_528 : subd5_1 [2, -1, -6] = true := by decide +kernel
theorem subd5_1_529 : subd5_1 [2, -1, -5] = true := by decide +kernel
theorem subd5_1_530 : subd5_1 [2, -1, -4] = true := by decide +kernel
theorem subd5_1_531 : subd5_1 [2, -1, -3] = true := by decide +kernel
theorem subd5_1_532 : subd5_1 [2, -1, -2] = true := by decide +kernel
theorem subd5_1_533 : subd5_1 [2, -1, -1] = true := by decide +kernel
theorem subd5_1_534 : subd5_1 [2, -1, 0] = true := by decide +kernel
theorem subd5_1_535 : subd5_1 [2, -1, 1] = true := by decide +kernel
theorem subd5_1_536 : subd5_1 [2, -1, 2] = true := by decide +kernel
theorem subd5_1_537 : subd5_1 [2, -1, 3] = true := by decide +kernel
theorem subd5_1_538 : subd5_1 [2, -1, 4] = true := by decide +kernel
theorem subd5_1_539 : subd5_1 [2, -1, 5] = true := by decide +kernel
theorem subd5_1_540 : subd5_1 [2, -1, 6] = true := by decide +kernel
theorem subd5_1_541 : subd5_1 [2, 0, -9] = true := by decide +kernel
theorem subd5_1_542 : subd5_1 [2, 0, -8] = true := by decide +kernel
theorem subd5_1_543 : subd5_1 [2, 0, -7] = true := by decide +kernel
theorem sbd5_1_16 : ∀ q ∈ blkd5_1_16, subd5_1 q = true := by
  unfold blkd5_1_16
  exact List.forall_mem_cons.2 ⟨subd5_1_512, List.forall_mem_cons.2 ⟨subd5_1_513, List.forall_mem_cons.2 ⟨subd5_1_514, List.forall_mem_cons.2 ⟨subd5_1_515, List.forall_mem_cons.2 ⟨subd5_1_516, List.forall_mem_cons.2 ⟨subd5_1_517, List.forall_mem_cons.2 ⟨subd5_1_518, List.forall_mem_cons.2 ⟨subd5_1_519, List.forall_mem_cons.2 ⟨subd5_1_520, List.forall_mem_cons.2 ⟨subd5_1_521, List.forall_mem_cons.2 ⟨subd5_1_522, List.forall_mem_cons.2 ⟨subd5_1_523, List.forall_mem_cons.2 ⟨subd5_1_524, List.forall_mem_cons.2 ⟨subd5_1_525, List.forall_mem_cons.2 ⟨subd5_1_526, List.forall_mem_cons.2 ⟨subd5_1_527, List.forall_mem_cons.2 ⟨subd5_1_528, List.forall_mem_cons.2 ⟨subd5_1_529, List.forall_mem_cons.2 ⟨subd5_1_530, List.forall_mem_cons.2 ⟨subd5_1_531, List.forall_mem_cons.2 ⟨subd5_1_532, List.forall_mem_cons.2 ⟨subd5_1_533, List.forall_mem_cons.2 ⟨subd5_1_534, List.forall_mem_cons.2 ⟨subd5_1_535, List.forall_mem_cons.2 ⟨subd5_1_536, List.forall_mem_cons.2 ⟨subd5_1_537, List.forall_mem_cons.2 ⟨subd5_1_538, List.forall_mem_cons.2 ⟨subd5_1_539, List.forall_mem_cons.2 ⟨subd5_1_540, List.forall_mem_cons.2 ⟨subd5_1_541, List.forall_mem_cons.2 ⟨subd5_1_542, List.forall_mem_cons.2 ⟨subd5_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_544 : subd5_1 [2, 0, -6] = true := by decide +kernel
theorem subd5_1_545 : subd5_1 [2, 0, -5] = true := by decide +kernel
theorem subd5_1_546 : subd5_1 [2, 0, -4] = true := by decide +kernel
theorem subd5_1_547 : subd5_1 [2, 0, -3] = true := by decide +kernel
theorem subd5_1_548 : subd5_1 [2, 0, -2] = true := by decide +kernel
theorem subd5_1_549 : subd5_1 [2, 0, -1] = true := by decide +kernel
theorem subd5_1_550 : subd5_1 [2, 0, 0] = true := by decide +kernel
theorem subd5_1_551 : subd5_1 [2, 0, 1] = true := by decide +kernel
theorem subd5_1_552 : subd5_1 [2, 0, 2] = true := by decide +kernel
theorem subd5_1_553 : subd5_1 [2, 0, 3] = true := by decide +kernel
theorem subd5_1_554 : subd5_1 [2, 0, 4] = true := by decide +kernel
theorem subd5_1_555 : subd5_1 [2, 0, 5] = true := by decide +kernel
theorem subd5_1_556 : subd5_1 [2, 0, 6] = true := by decide +kernel
theorem subd5_1_557 : subd5_1 [2, 1, -9] = true := by decide +kernel
theorem subd5_1_558 : subd5_1 [2, 1, -8] = true := by decide +kernel
theorem subd5_1_559 : subd5_1 [2, 1, -7] = true := by decide +kernel
theorem subd5_1_560 : subd5_1 [2, 1, -6] = true := by decide +kernel
theorem subd5_1_561 : subd5_1 [2, 1, -5] = true := by decide +kernel
theorem subd5_1_562 : subd5_1 [2, 1, -4] = true := by decide +kernel
theorem subd5_1_563 : subd5_1 [2, 1, -3] = true := by decide +kernel
theorem subd5_1_564 : subd5_1 [2, 1, -2] = true := by decide +kernel
theorem subd5_1_565 : subd5_1 [2, 1, -1] = true := by decide +kernel
theorem subd5_1_566 : subd5_1 [2, 1, 0] = true := by decide +kernel
theorem subd5_1_567 : subd5_1 [2, 1, 1] = true := by decide +kernel
theorem subd5_1_568 : subd5_1 [2, 1, 2] = true := by decide +kernel
theorem subd5_1_569 : subd5_1 [2, 1, 3] = true := by decide +kernel
theorem subd5_1_570 : subd5_1 [2, 1, 4] = true := by decide +kernel
theorem subd5_1_571 : subd5_1 [2, 1, 5] = true := by decide +kernel
theorem subd5_1_572 : subd5_1 [2, 1, 6] = true := by decide +kernel
theorem subd5_1_573 : subd5_1 [2, 2, -9] = true := by decide +kernel
theorem subd5_1_574 : subd5_1 [2, 2, -8] = true := by decide +kernel
theorem subd5_1_575 : subd5_1 [2, 2, -7] = true := by decide +kernel
theorem sbd5_1_17 : ∀ q ∈ blkd5_1_17, subd5_1 q = true := by
  unfold blkd5_1_17
  exact List.forall_mem_cons.2 ⟨subd5_1_544, List.forall_mem_cons.2 ⟨subd5_1_545, List.forall_mem_cons.2 ⟨subd5_1_546, List.forall_mem_cons.2 ⟨subd5_1_547, List.forall_mem_cons.2 ⟨subd5_1_548, List.forall_mem_cons.2 ⟨subd5_1_549, List.forall_mem_cons.2 ⟨subd5_1_550, List.forall_mem_cons.2 ⟨subd5_1_551, List.forall_mem_cons.2 ⟨subd5_1_552, List.forall_mem_cons.2 ⟨subd5_1_553, List.forall_mem_cons.2 ⟨subd5_1_554, List.forall_mem_cons.2 ⟨subd5_1_555, List.forall_mem_cons.2 ⟨subd5_1_556, List.forall_mem_cons.2 ⟨subd5_1_557, List.forall_mem_cons.2 ⟨subd5_1_558, List.forall_mem_cons.2 ⟨subd5_1_559, List.forall_mem_cons.2 ⟨subd5_1_560, List.forall_mem_cons.2 ⟨subd5_1_561, List.forall_mem_cons.2 ⟨subd5_1_562, List.forall_mem_cons.2 ⟨subd5_1_563, List.forall_mem_cons.2 ⟨subd5_1_564, List.forall_mem_cons.2 ⟨subd5_1_565, List.forall_mem_cons.2 ⟨subd5_1_566, List.forall_mem_cons.2 ⟨subd5_1_567, List.forall_mem_cons.2 ⟨subd5_1_568, List.forall_mem_cons.2 ⟨subd5_1_569, List.forall_mem_cons.2 ⟨subd5_1_570, List.forall_mem_cons.2 ⟨subd5_1_571, List.forall_mem_cons.2 ⟨subd5_1_572, List.forall_mem_cons.2 ⟨subd5_1_573, List.forall_mem_cons.2 ⟨subd5_1_574, List.forall_mem_cons.2 ⟨subd5_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_576 : subd5_1 [2, 2, -6] = true := by decide +kernel
theorem subd5_1_577 : subd5_1 [2, 2, -5] = true := by decide +kernel
theorem subd5_1_578 : subd5_1 [2, 2, -4] = true := by decide +kernel
theorem subd5_1_579 : subd5_1 [2, 2, -3] = true := by decide +kernel
theorem subd5_1_580 : subd5_1 [2, 2, -2] = true := by decide +kernel
theorem subd5_1_581 : subd5_1 [2, 2, -1] = true := by decide +kernel
theorem subd5_1_582 : subd5_1 [2, 2, 0] = true := by decide +kernel
theorem subd5_1_583 : subd5_1 [2, 2, 1] = true := by decide +kernel
theorem subd5_1_584 : subd5_1 [2, 2, 2] = true := by decide +kernel
theorem subd5_1_585 : subd5_1 [2, 2, 3] = true := by decide +kernel
theorem subd5_1_586 : subd5_1 [2, 2, 4] = true := by decide +kernel
theorem subd5_1_587 : subd5_1 [2, 2, 5] = true := by decide +kernel
theorem subd5_1_588 : subd5_1 [2, 2, 6] = true := by decide +kernel
theorem subd5_1_589 : subd5_1 [2, 3] = true := by decide +kernel
theorem subd5_1_590 : subd5_1 [2, 4] = true := by decide +kernel
theorem subd5_1_591 : subd5_1 [2, 5] = true := by decide +kernel
theorem subd5_1_592 : subd5_1 [2, 6] = true := by decide +kernel
theorem subd5_1_593 : subd5_1 [2, 7] = true := by decide +kernel
theorem subd5_1_594 : subd5_1 [3, -6] = true := by decide +kernel
theorem subd5_1_595 : subd5_1 [3, -5] = true := by decide +kernel
theorem subd5_1_596 : subd5_1 [3, -4] = true := by decide +kernel
theorem subd5_1_597 : subd5_1 [3, -3] = true := by decide +kernel
theorem subd5_1_598 : subd5_1 [3, -2] = true := by decide +kernel
theorem subd5_1_599 : subd5_1 [3, -1, -8] = true := by decide +kernel
theorem subd5_1_600 : subd5_1 [3, -1, -7] = true := by decide +kernel
theorem subd5_1_601 : subd5_1 [3, -1, -6] = true := by decide +kernel
theorem subd5_1_602 : subd5_1 [3, -1, -5] = true := by decide +kernel
theorem subd5_1_603 : subd5_1 [3, -1, -4] = true := by decide +kernel
theorem subd5_1_604 : subd5_1 [3, -1, -3] = true := by decide +kernel
theorem subd5_1_605 : subd5_1 [3, -1, -2] = true := by decide +kernel
theorem subd5_1_606 : subd5_1 [3, -1, -1] = true := by decide +kernel
theorem subd5_1_607 : subd5_1 [3, -1, 0] = true := by decide +kernel
theorem sbd5_1_18 : ∀ q ∈ blkd5_1_18, subd5_1 q = true := by
  unfold blkd5_1_18
  exact List.forall_mem_cons.2 ⟨subd5_1_576, List.forall_mem_cons.2 ⟨subd5_1_577, List.forall_mem_cons.2 ⟨subd5_1_578, List.forall_mem_cons.2 ⟨subd5_1_579, List.forall_mem_cons.2 ⟨subd5_1_580, List.forall_mem_cons.2 ⟨subd5_1_581, List.forall_mem_cons.2 ⟨subd5_1_582, List.forall_mem_cons.2 ⟨subd5_1_583, List.forall_mem_cons.2 ⟨subd5_1_584, List.forall_mem_cons.2 ⟨subd5_1_585, List.forall_mem_cons.2 ⟨subd5_1_586, List.forall_mem_cons.2 ⟨subd5_1_587, List.forall_mem_cons.2 ⟨subd5_1_588, List.forall_mem_cons.2 ⟨subd5_1_589, List.forall_mem_cons.2 ⟨subd5_1_590, List.forall_mem_cons.2 ⟨subd5_1_591, List.forall_mem_cons.2 ⟨subd5_1_592, List.forall_mem_cons.2 ⟨subd5_1_593, List.forall_mem_cons.2 ⟨subd5_1_594, List.forall_mem_cons.2 ⟨subd5_1_595, List.forall_mem_cons.2 ⟨subd5_1_596, List.forall_mem_cons.2 ⟨subd5_1_597, List.forall_mem_cons.2 ⟨subd5_1_598, List.forall_mem_cons.2 ⟨subd5_1_599, List.forall_mem_cons.2 ⟨subd5_1_600, List.forall_mem_cons.2 ⟨subd5_1_601, List.forall_mem_cons.2 ⟨subd5_1_602, List.forall_mem_cons.2 ⟨subd5_1_603, List.forall_mem_cons.2 ⟨subd5_1_604, List.forall_mem_cons.2 ⟨subd5_1_605, List.forall_mem_cons.2 ⟨subd5_1_606, List.forall_mem_cons.2 ⟨subd5_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_608 : subd5_1 [3, -1, 1] = true := by decide +kernel
theorem subd5_1_609 : subd5_1 [3, -1, 2] = true := by decide +kernel
theorem subd5_1_610 : subd5_1 [3, -1, 3] = true := by decide +kernel
theorem subd5_1_611 : subd5_1 [3, -1, 4] = true := by decide +kernel
theorem subd5_1_612 : subd5_1 [3, -1, 5] = true := by decide +kernel
theorem subd5_1_613 : subd5_1 [3, -1, 6] = true := by decide +kernel
theorem subd5_1_614 : subd5_1 [3, 0, -9] = true := by decide +kernel
theorem subd5_1_615 : subd5_1 [3, 0, -8] = true := by decide +kernel
theorem subd5_1_616 : subd5_1 [3, 0, -7] = true := by decide +kernel
theorem subd5_1_617 : subd5_1 [3, 0, -6] = true := by decide +kernel
theorem subd5_1_618 : subd5_1 [3, 0, -5] = true := by decide +kernel
theorem subd5_1_619 : subd5_1 [3, 0, -4] = true := by decide +kernel
theorem subd5_1_620 : subd5_1 [3, 0, -3] = true := by decide +kernel
theorem subd5_1_621 : subd5_1 [3, 0, -2] = true := by decide +kernel
theorem subd5_1_622 : subd5_1 [3, 0, -1] = true := by decide +kernel
theorem subd5_1_623 : subd5_1 [3, 0, 0] = true := by decide +kernel
theorem subd5_1_624 : subd5_1 [3, 0, 1] = true := by decide +kernel
theorem subd5_1_625 : subd5_1 [3, 0, 2] = true := by decide +kernel
theorem subd5_1_626 : subd5_1 [3, 0, 3] = true := by decide +kernel
theorem subd5_1_627 : subd5_1 [3, 0, 4] = true := by decide +kernel
theorem subd5_1_628 : subd5_1 [3, 0, 5] = true := by decide +kernel
theorem subd5_1_629 : subd5_1 [3, 0, 6] = true := by decide +kernel
theorem subd5_1_630 : subd5_1 [3, 1, -9] = true := by decide +kernel
theorem subd5_1_631 : subd5_1 [3, 1, -8] = true := by decide +kernel
theorem subd5_1_632 : subd5_1 [3, 1, -7] = true := by decide +kernel
theorem subd5_1_633 : subd5_1 [3, 1, -6] = true := by decide +kernel
theorem subd5_1_634 : subd5_1 [3, 1, -5] = true := by decide +kernel
theorem subd5_1_635 : subd5_1 [3, 1, -4] = true := by decide +kernel
theorem subd5_1_636 : subd5_1 [3, 1, -3] = true := by decide +kernel
theorem subd5_1_637 : subd5_1 [3, 1, -2] = true := by decide +kernel
theorem subd5_1_638 : subd5_1 [3, 1, -1] = true := by decide +kernel
theorem subd5_1_639 : subd5_1 [3, 1, 0] = true := by decide +kernel
theorem sbd5_1_19 : ∀ q ∈ blkd5_1_19, subd5_1 q = true := by
  unfold blkd5_1_19
  exact List.forall_mem_cons.2 ⟨subd5_1_608, List.forall_mem_cons.2 ⟨subd5_1_609, List.forall_mem_cons.2 ⟨subd5_1_610, List.forall_mem_cons.2 ⟨subd5_1_611, List.forall_mem_cons.2 ⟨subd5_1_612, List.forall_mem_cons.2 ⟨subd5_1_613, List.forall_mem_cons.2 ⟨subd5_1_614, List.forall_mem_cons.2 ⟨subd5_1_615, List.forall_mem_cons.2 ⟨subd5_1_616, List.forall_mem_cons.2 ⟨subd5_1_617, List.forall_mem_cons.2 ⟨subd5_1_618, List.forall_mem_cons.2 ⟨subd5_1_619, List.forall_mem_cons.2 ⟨subd5_1_620, List.forall_mem_cons.2 ⟨subd5_1_621, List.forall_mem_cons.2 ⟨subd5_1_622, List.forall_mem_cons.2 ⟨subd5_1_623, List.forall_mem_cons.2 ⟨subd5_1_624, List.forall_mem_cons.2 ⟨subd5_1_625, List.forall_mem_cons.2 ⟨subd5_1_626, List.forall_mem_cons.2 ⟨subd5_1_627, List.forall_mem_cons.2 ⟨subd5_1_628, List.forall_mem_cons.2 ⟨subd5_1_629, List.forall_mem_cons.2 ⟨subd5_1_630, List.forall_mem_cons.2 ⟨subd5_1_631, List.forall_mem_cons.2 ⟨subd5_1_632, List.forall_mem_cons.2 ⟨subd5_1_633, List.forall_mem_cons.2 ⟨subd5_1_634, List.forall_mem_cons.2 ⟨subd5_1_635, List.forall_mem_cons.2 ⟨subd5_1_636, List.forall_mem_cons.2 ⟨subd5_1_637, List.forall_mem_cons.2 ⟨subd5_1_638, List.forall_mem_cons.2 ⟨subd5_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_640 : subd5_1 [3, 1, 1] = true := by decide +kernel
theorem subd5_1_641 : subd5_1 [3, 1, 2] = true := by decide +kernel
theorem subd5_1_642 : subd5_1 [3, 1, 3] = true := by decide +kernel
theorem subd5_1_643 : subd5_1 [3, 1, 4] = true := by decide +kernel
theorem subd5_1_644 : subd5_1 [3, 1, 5] = true := by decide +kernel
theorem subd5_1_645 : subd5_1 [3, 1, 6] = true := by decide +kernel
theorem subd5_1_646 : subd5_1 [3, 2, -9] = true := by decide +kernel
theorem subd5_1_647 : subd5_1 [3, 2, -8] = true := by decide +kernel
theorem subd5_1_648 : subd5_1 [3, 2, -7] = true := by decide +kernel
theorem subd5_1_649 : subd5_1 [3, 2, -6] = true := by decide +kernel
theorem subd5_1_650 : subd5_1 [3, 2, -5] = true := by decide +kernel
theorem subd5_1_651 : subd5_1 [3, 2, -4] = true := by decide +kernel
theorem subd5_1_652 : subd5_1 [3, 2, -3] = true := by decide +kernel
theorem subd5_1_653 : subd5_1 [3, 2, -2] = true := by decide +kernel
theorem subd5_1_654 : subd5_1 [3, 2, -1] = true := by decide +kernel
theorem subd5_1_655 : subd5_1 [3, 2, 0] = true := by decide +kernel
theorem subd5_1_656 : subd5_1 [3, 2, 1] = true := by decide +kernel
theorem subd5_1_657 : subd5_1 [3, 2, 2] = true := by decide +kernel
theorem subd5_1_658 : subd5_1 [3, 2, 3] = true := by decide +kernel
theorem subd5_1_659 : subd5_1 [3, 2, 4] = true := by decide +kernel
theorem subd5_1_660 : subd5_1 [3, 2, 5] = true := by decide +kernel
theorem subd5_1_661 : subd5_1 [3, 3] = true := by decide +kernel
theorem subd5_1_662 : subd5_1 [3, 4] = true := by decide +kernel
theorem subd5_1_663 : subd5_1 [3, 5] = true := by decide +kernel
theorem subd5_1_664 : subd5_1 [3, 6] = true := by decide +kernel
theorem subd5_1_665 : subd5_1 [3, 7] = true := by decide +kernel
theorem subd5_1_666 : subd5_1 [4, -6] = true := by decide +kernel
theorem subd5_1_667 : subd5_1 [4, -5] = true := by decide +kernel
theorem subd5_1_668 : subd5_1 [4, -4] = true := by decide +kernel
theorem subd5_1_669 : subd5_1 [4, -3] = true := by decide +kernel
theorem subd5_1_670 : subd5_1 [4, -2] = true := by decide +kernel
theorem subd5_1_671 : subd5_1 [4, -1] = true := by decide +kernel
theorem sbd5_1_20 : ∀ q ∈ blkd5_1_20, subd5_1 q = true := by
  unfold blkd5_1_20
  exact List.forall_mem_cons.2 ⟨subd5_1_640, List.forall_mem_cons.2 ⟨subd5_1_641, List.forall_mem_cons.2 ⟨subd5_1_642, List.forall_mem_cons.2 ⟨subd5_1_643, List.forall_mem_cons.2 ⟨subd5_1_644, List.forall_mem_cons.2 ⟨subd5_1_645, List.forall_mem_cons.2 ⟨subd5_1_646, List.forall_mem_cons.2 ⟨subd5_1_647, List.forall_mem_cons.2 ⟨subd5_1_648, List.forall_mem_cons.2 ⟨subd5_1_649, List.forall_mem_cons.2 ⟨subd5_1_650, List.forall_mem_cons.2 ⟨subd5_1_651, List.forall_mem_cons.2 ⟨subd5_1_652, List.forall_mem_cons.2 ⟨subd5_1_653, List.forall_mem_cons.2 ⟨subd5_1_654, List.forall_mem_cons.2 ⟨subd5_1_655, List.forall_mem_cons.2 ⟨subd5_1_656, List.forall_mem_cons.2 ⟨subd5_1_657, List.forall_mem_cons.2 ⟨subd5_1_658, List.forall_mem_cons.2 ⟨subd5_1_659, List.forall_mem_cons.2 ⟨subd5_1_660, List.forall_mem_cons.2 ⟨subd5_1_661, List.forall_mem_cons.2 ⟨subd5_1_662, List.forall_mem_cons.2 ⟨subd5_1_663, List.forall_mem_cons.2 ⟨subd5_1_664, List.forall_mem_cons.2 ⟨subd5_1_665, List.forall_mem_cons.2 ⟨subd5_1_666, List.forall_mem_cons.2 ⟨subd5_1_667, List.forall_mem_cons.2 ⟨subd5_1_668, List.forall_mem_cons.2 ⟨subd5_1_669, List.forall_mem_cons.2 ⟨subd5_1_670, List.forall_mem_cons.2 ⟨subd5_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_672 : subd5_1 [4, 0] = true := by decide +kernel
theorem subd5_1_673 : subd5_1 [4, 1] = true := by decide +kernel
theorem subd5_1_674 : subd5_1 [4, 2] = true := by decide +kernel
theorem subd5_1_675 : subd5_1 [4, 3] = true := by decide +kernel
theorem subd5_1_676 : subd5_1 [4, 4] = true := by decide +kernel
theorem subd5_1_677 : subd5_1 [4, 5] = true := by decide +kernel
theorem subd5_1_678 : subd5_1 [4, 6] = true := by decide +kernel
theorem subd5_1_679 : subd5_1 [4, 7] = true := by decide +kernel
theorem subd5_1_680 : subd5_1 [5, -5] = true := by decide +kernel
theorem subd5_1_681 : subd5_1 [5, -4] = true := by decide +kernel
theorem subd5_1_682 : subd5_1 [5, -3] = true := by decide +kernel
theorem subd5_1_683 : subd5_1 [5, -2] = true := by decide +kernel
theorem subd5_1_684 : subd5_1 [5, -1] = true := by decide +kernel
theorem subd5_1_685 : subd5_1 [5, 0] = true := by decide +kernel
theorem subd5_1_686 : subd5_1 [5, 1] = true := by decide +kernel
theorem subd5_1_687 : subd5_1 [5, 2] = true := by decide +kernel
theorem subd5_1_688 : subd5_1 [5, 3] = true := by decide +kernel
theorem subd5_1_689 : subd5_1 [5, 4] = true := by decide +kernel
theorem subd5_1_690 : subd5_1 [5, 5] = true := by decide +kernel
theorem subd5_1_691 : subd5_1 [5, 6] = true := by decide +kernel
theorem subd5_1_692 : subd5_1 [6, -4] = true := by decide +kernel
theorem subd5_1_693 : subd5_1 [6, -3] = true := by decide +kernel
theorem subd5_1_694 : subd5_1 [6, -2] = true := by decide +kernel
theorem subd5_1_695 : subd5_1 [6, -1] = true := by decide +kernel
theorem subd5_1_696 : subd5_1 [6, 0] = true := by decide +kernel
theorem subd5_1_697 : subd5_1 [6, 1] = true := by decide +kernel
theorem subd5_1_698 : subd5_1 [6, 2] = true := by decide +kernel
theorem subd5_1_699 : subd5_1 [6, 3] = true := by decide +kernel
theorem subd5_1_700 : subd5_1 [6, 4] = true := by decide +kernel
theorem subd5_1_701 : subd5_1 [6, 5] = true := by decide +kernel
theorem subd5_1_702 : subd5_1 [6, 6] = true := by decide +kernel
theorem subd5_1_703 : subd5_1 [7, -3] = true := by decide +kernel
theorem sbd5_1_21 : ∀ q ∈ blkd5_1_21, subd5_1 q = true := by
  unfold blkd5_1_21
  exact List.forall_mem_cons.2 ⟨subd5_1_672, List.forall_mem_cons.2 ⟨subd5_1_673, List.forall_mem_cons.2 ⟨subd5_1_674, List.forall_mem_cons.2 ⟨subd5_1_675, List.forall_mem_cons.2 ⟨subd5_1_676, List.forall_mem_cons.2 ⟨subd5_1_677, List.forall_mem_cons.2 ⟨subd5_1_678, List.forall_mem_cons.2 ⟨subd5_1_679, List.forall_mem_cons.2 ⟨subd5_1_680, List.forall_mem_cons.2 ⟨subd5_1_681, List.forall_mem_cons.2 ⟨subd5_1_682, List.forall_mem_cons.2 ⟨subd5_1_683, List.forall_mem_cons.2 ⟨subd5_1_684, List.forall_mem_cons.2 ⟨subd5_1_685, List.forall_mem_cons.2 ⟨subd5_1_686, List.forall_mem_cons.2 ⟨subd5_1_687, List.forall_mem_cons.2 ⟨subd5_1_688, List.forall_mem_cons.2 ⟨subd5_1_689, List.forall_mem_cons.2 ⟨subd5_1_690, List.forall_mem_cons.2 ⟨subd5_1_691, List.forall_mem_cons.2 ⟨subd5_1_692, List.forall_mem_cons.2 ⟨subd5_1_693, List.forall_mem_cons.2 ⟨subd5_1_694, List.forall_mem_cons.2 ⟨subd5_1_695, List.forall_mem_cons.2 ⟨subd5_1_696, List.forall_mem_cons.2 ⟨subd5_1_697, List.forall_mem_cons.2 ⟨subd5_1_698, List.forall_mem_cons.2 ⟨subd5_1_699, List.forall_mem_cons.2 ⟨subd5_1_700, List.forall_mem_cons.2 ⟨subd5_1_701, List.forall_mem_cons.2 ⟨subd5_1_702, List.forall_mem_cons.2 ⟨subd5_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_1_704 : subd5_1 [7, -2] = true := by decide +kernel
theorem subd5_1_705 : subd5_1 [7, -1] = true := by decide +kernel
theorem subd5_1_706 : subd5_1 [7, 0] = true := by decide +kernel
theorem subd5_1_707 : subd5_1 [7, 1] = true := by decide +kernel
theorem subd5_1_708 : subd5_1 [7, 2] = true := by decide +kernel
theorem subd5_1_709 : subd5_1 [7, 3] = true := by decide +kernel
theorem subd5_1_710 : subd5_1 [7, 4] = true := by decide +kernel
theorem subd5_1_711 : subd5_1 [7, 5] = true := by decide +kernel
theorem subd5_1_712 : subd5_1 [8] = true := by decide +kernel
theorem sbd5_1_22 : ∀ q ∈ blkd5_1_22, subd5_1 q = true := by
  unfold blkd5_1_22
  exact List.forall_mem_cons.2 ⟨subd5_1_704, List.forall_mem_cons.2 ⟨subd5_1_705, List.forall_mem_cons.2 ⟨subd5_1_706, List.forall_mem_cons.2 ⟨subd5_1_707, List.forall_mem_cons.2 ⟨subd5_1_708, List.forall_mem_cons.2 ⟨subd5_1_709, List.forall_mem_cons.2 ⟨subd5_1_710, List.forall_mem_cons.2 ⟨subd5_1_711, List.forall_mem_cons.2 ⟨subd5_1_712, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_0 : ldCheck G d6_0.U d6_0.ms ldd6_0 = true := by decide +kernel
theorem pre_okd6_0 : subPre G cell6 d6_0 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C116
