import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd5_0_512 : subd5_0 [0, 0, 1] = true := by decide +kernel
theorem subd5_0_513 : subd5_0 [0, 0, 2] = true := by decide +kernel
theorem subd5_0_514 : subd5_0 [0, 0, 3] = true := by decide +kernel
theorem subd5_0_515 : subd5_0 [0, 0, 4] = true := by decide +kernel
theorem subd5_0_516 : subd5_0 [0, 0, 5] = true := by decide +kernel
theorem subd5_0_517 : subd5_0 [0, 0, 6] = true := by decide +kernel
theorem subd5_0_518 : subd5_0 [0, 0, 7] = true := by decide +kernel
theorem subd5_0_519 : subd5_0 [0, 0, 8] = true := by decide +kernel
theorem subd5_0_520 : subd5_0 [0, 0, 9] = true := by decide +kernel
theorem subd5_0_521 : subd5_0 [0, 1, -10] = true := by decide +kernel
theorem subd5_0_522 : subd5_0 [0, 1, -9] = true := by decide +kernel
theorem subd5_0_523 : subd5_0 [0, 1, -8] = true := by decide +kernel
theorem subd5_0_524 : subd5_0 [0, 1, -7] = true := by decide +kernel
theorem subd5_0_525 : subd5_0 [0, 1, -6] = true := by decide +kernel
theorem subd5_0_526 : subd5_0 [0, 1, -5] = true := by decide +kernel
theorem subd5_0_527 : subd5_0 [0, 1, -4] = true := by decide +kernel
theorem subd5_0_528 : subd5_0 [0, 1, -3] = true := by decide +kernel
theorem subd5_0_529 : subd5_0 [0, 1, -2] = true := by decide +kernel
theorem subd5_0_530 : subd5_0 [0, 1, -1] = true := by decide +kernel
theorem subd5_0_531 : subd5_0 [0, 1, 0] = true := by decide +kernel
theorem subd5_0_532 : subd5_0 [0, 1, 1] = true := by decide +kernel
theorem subd5_0_533 : subd5_0 [0, 1, 2] = true := by decide +kernel
theorem subd5_0_534 : subd5_0 [0, 1, 3] = true := by decide +kernel
theorem subd5_0_535 : subd5_0 [0, 1, 4] = true := by decide +kernel
theorem subd5_0_536 : subd5_0 [0, 1, 5] = true := by decide +kernel
theorem subd5_0_537 : subd5_0 [0, 1, 6] = true := by decide +kernel
theorem subd5_0_538 : subd5_0 [0, 1, 7] = true := by decide +kernel
theorem subd5_0_539 : subd5_0 [0, 1, 8] = true := by decide +kernel
theorem subd5_0_540 : subd5_0 [0, 1, 9] = true := by decide +kernel
theorem subd5_0_541 : subd5_0 [0, 2, -10] = true := by decide +kernel
theorem subd5_0_542 : subd5_0 [0, 2, -9] = true := by decide +kernel
theorem subd5_0_543 : subd5_0 [0, 2, -8] = true := by decide +kernel
theorem sbd5_0_16 : ∀ q ∈ blkd5_0_16, subd5_0 q = true := by
  unfold blkd5_0_16
  exact List.forall_mem_cons.2 ⟨subd5_0_512, List.forall_mem_cons.2 ⟨subd5_0_513, List.forall_mem_cons.2 ⟨subd5_0_514, List.forall_mem_cons.2 ⟨subd5_0_515, List.forall_mem_cons.2 ⟨subd5_0_516, List.forall_mem_cons.2 ⟨subd5_0_517, List.forall_mem_cons.2 ⟨subd5_0_518, List.forall_mem_cons.2 ⟨subd5_0_519, List.forall_mem_cons.2 ⟨subd5_0_520, List.forall_mem_cons.2 ⟨subd5_0_521, List.forall_mem_cons.2 ⟨subd5_0_522, List.forall_mem_cons.2 ⟨subd5_0_523, List.forall_mem_cons.2 ⟨subd5_0_524, List.forall_mem_cons.2 ⟨subd5_0_525, List.forall_mem_cons.2 ⟨subd5_0_526, List.forall_mem_cons.2 ⟨subd5_0_527, List.forall_mem_cons.2 ⟨subd5_0_528, List.forall_mem_cons.2 ⟨subd5_0_529, List.forall_mem_cons.2 ⟨subd5_0_530, List.forall_mem_cons.2 ⟨subd5_0_531, List.forall_mem_cons.2 ⟨subd5_0_532, List.forall_mem_cons.2 ⟨subd5_0_533, List.forall_mem_cons.2 ⟨subd5_0_534, List.forall_mem_cons.2 ⟨subd5_0_535, List.forall_mem_cons.2 ⟨subd5_0_536, List.forall_mem_cons.2 ⟨subd5_0_537, List.forall_mem_cons.2 ⟨subd5_0_538, List.forall_mem_cons.2 ⟨subd5_0_539, List.forall_mem_cons.2 ⟨subd5_0_540, List.forall_mem_cons.2 ⟨subd5_0_541, List.forall_mem_cons.2 ⟨subd5_0_542, List.forall_mem_cons.2 ⟨subd5_0_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_544 : subd5_0 [0, 2, -7] = true := by decide +kernel
theorem subd5_0_545 : subd5_0 [0, 2, -6] = true := by decide +kernel
theorem subd5_0_546 : subd5_0 [0, 2, -5] = true := by decide +kernel
theorem subd5_0_547 : subd5_0 [0, 2, -4] = true := by decide +kernel
theorem subd5_0_548 : subd5_0 [0, 2, -3] = true := by decide +kernel
theorem subd5_0_549 : subd5_0 [0, 2, -2] = true := by decide +kernel
theorem subd5_0_550 : subd5_0 [0, 2, -1] = true := by decide +kernel
theorem subd5_0_551 : subd5_0 [0, 2, 0] = true := by decide +kernel
theorem subd5_0_552 : subd5_0 [0, 2, 1] = true := by decide +kernel
theorem subd5_0_553 : subd5_0 [0, 2, 2] = true := by decide +kernel
theorem subd5_0_554 : subd5_0 [0, 2, 3] = true := by decide +kernel
theorem subd5_0_555 : subd5_0 [0, 2, 4] = true := by decide +kernel
theorem subd5_0_556 : subd5_0 [0, 2, 5] = true := by decide +kernel
theorem subd5_0_557 : subd5_0 [0, 2, 6] = true := by decide +kernel
theorem subd5_0_558 : subd5_0 [0, 2, 7] = true := by decide +kernel
theorem subd5_0_559 : subd5_0 [0, 2, 8] = true := by decide +kernel
theorem subd5_0_560 : subd5_0 [0, 3, -10] = true := by decide +kernel
theorem subd5_0_561 : subd5_0 [0, 3, -9] = true := by decide +kernel
theorem subd5_0_562 : subd5_0 [0, 3, -8] = true := by decide +kernel
theorem subd5_0_563 : subd5_0 [0, 3, -7] = true := by decide +kernel
theorem subd5_0_564 : subd5_0 [0, 3, -6] = true := by decide +kernel
theorem subd5_0_565 : subd5_0 [0, 3, -5] = true := by decide +kernel
theorem subd5_0_566 : subd5_0 [0, 3, -4] = true := by decide +kernel
theorem subd5_0_567 : subd5_0 [0, 3, -3] = true := by decide +kernel
theorem subd5_0_568 : subd5_0 [0, 3, -2] = true := by decide +kernel
theorem subd5_0_569 : subd5_0 [0, 3, -1] = true := by decide +kernel
theorem subd5_0_570 : subd5_0 [0, 3, 0] = true := by decide +kernel
theorem subd5_0_571 : subd5_0 [0, 3, 1] = true := by decide +kernel
theorem subd5_0_572 : subd5_0 [0, 3, 2] = true := by decide +kernel
theorem subd5_0_573 : subd5_0 [0, 3, 3] = true := by decide +kernel
theorem subd5_0_574 : subd5_0 [0, 3, 4] = true := by decide +kernel
theorem subd5_0_575 : subd5_0 [0, 3, 5] = true := by decide +kernel
theorem sbd5_0_17 : ∀ q ∈ blkd5_0_17, subd5_0 q = true := by
  unfold blkd5_0_17
  exact List.forall_mem_cons.2 ⟨subd5_0_544, List.forall_mem_cons.2 ⟨subd5_0_545, List.forall_mem_cons.2 ⟨subd5_0_546, List.forall_mem_cons.2 ⟨subd5_0_547, List.forall_mem_cons.2 ⟨subd5_0_548, List.forall_mem_cons.2 ⟨subd5_0_549, List.forall_mem_cons.2 ⟨subd5_0_550, List.forall_mem_cons.2 ⟨subd5_0_551, List.forall_mem_cons.2 ⟨subd5_0_552, List.forall_mem_cons.2 ⟨subd5_0_553, List.forall_mem_cons.2 ⟨subd5_0_554, List.forall_mem_cons.2 ⟨subd5_0_555, List.forall_mem_cons.2 ⟨subd5_0_556, List.forall_mem_cons.2 ⟨subd5_0_557, List.forall_mem_cons.2 ⟨subd5_0_558, List.forall_mem_cons.2 ⟨subd5_0_559, List.forall_mem_cons.2 ⟨subd5_0_560, List.forall_mem_cons.2 ⟨subd5_0_561, List.forall_mem_cons.2 ⟨subd5_0_562, List.forall_mem_cons.2 ⟨subd5_0_563, List.forall_mem_cons.2 ⟨subd5_0_564, List.forall_mem_cons.2 ⟨subd5_0_565, List.forall_mem_cons.2 ⟨subd5_0_566, List.forall_mem_cons.2 ⟨subd5_0_567, List.forall_mem_cons.2 ⟨subd5_0_568, List.forall_mem_cons.2 ⟨subd5_0_569, List.forall_mem_cons.2 ⟨subd5_0_570, List.forall_mem_cons.2 ⟨subd5_0_571, List.forall_mem_cons.2 ⟨subd5_0_572, List.forall_mem_cons.2 ⟨subd5_0_573, List.forall_mem_cons.2 ⟨subd5_0_574, List.forall_mem_cons.2 ⟨subd5_0_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_576 : subd5_0 [0, 3, 6] = true := by decide +kernel
theorem subd5_0_577 : subd5_0 [0, 3, 7] = true := by decide +kernel
theorem subd5_0_578 : subd5_0 [0, 4, -9] = true := by decide +kernel
theorem subd5_0_579 : subd5_0 [0, 4, -8] = true := by decide +kernel
theorem subd5_0_580 : subd5_0 [0, 4, -7] = true := by decide +kernel
theorem subd5_0_581 : subd5_0 [0, 4, -6] = true := by decide +kernel
theorem subd5_0_582 : subd5_0 [0, 4, -5] = true := by decide +kernel
theorem subd5_0_583 : subd5_0 [0, 4, -4] = true := by decide +kernel
theorem subd5_0_584 : subd5_0 [0, 4, -3] = true := by decide +kernel
theorem subd5_0_585 : subd5_0 [0, 4, -2] = true := by decide +kernel
theorem subd5_0_586 : subd5_0 [0, 4, -1] = true := by decide +kernel
theorem subd5_0_587 : subd5_0 [0, 4, 0] = true := by decide +kernel
theorem subd5_0_588 : subd5_0 [0, 4, 1] = true := by decide +kernel
theorem subd5_0_589 : subd5_0 [0, 4, 2] = true := by decide +kernel
theorem subd5_0_590 : subd5_0 [0, 4, 3] = true := by decide +kernel
theorem subd5_0_591 : subd5_0 [0, 4, 4] = true := by decide +kernel
theorem subd5_0_592 : subd5_0 [0, 4, 5] = true := by decide +kernel
theorem subd5_0_593 : subd5_0 [0, 5] = true := by decide +kernel
theorem subd5_0_594 : subd5_0 [1, -6] = true := by decide +kernel
theorem subd5_0_595 : subd5_0 [1, -5] = true := by decide +kernel
theorem subd5_0_596 : subd5_0 [1, -4, -5] = true := by decide +kernel
theorem subd5_0_597 : subd5_0 [1, -4, -4] = true := by decide +kernel
theorem subd5_0_598 : subd5_0 [1, -4, -3] = true := by decide +kernel
theorem subd5_0_599 : subd5_0 [1, -4, -2] = true := by decide +kernel
theorem subd5_0_600 : subd5_0 [1, -4, -1] = true := by decide +kernel
theorem subd5_0_601 : subd5_0 [1, -4, 0] = true := by decide +kernel
theorem subd5_0_602 : subd5_0 [1, -4, 1] = true := by decide +kernel
theorem subd5_0_603 : subd5_0 [1, -4, 2] = true := by decide +kernel
theorem subd5_0_604 : subd5_0 [1, -4, 3] = true := by decide +kernel
theorem subd5_0_605 : subd5_0 [1, -4, 4] = true := by decide +kernel
theorem subd5_0_606 : subd5_0 [1, -4, 5] = true := by decide +kernel
theorem subd5_0_607 : subd5_0 [1, -4, 6] = true := by decide +kernel
theorem sbd5_0_18 : ∀ q ∈ blkd5_0_18, subd5_0 q = true := by
  unfold blkd5_0_18
  exact List.forall_mem_cons.2 ⟨subd5_0_576, List.forall_mem_cons.2 ⟨subd5_0_577, List.forall_mem_cons.2 ⟨subd5_0_578, List.forall_mem_cons.2 ⟨subd5_0_579, List.forall_mem_cons.2 ⟨subd5_0_580, List.forall_mem_cons.2 ⟨subd5_0_581, List.forall_mem_cons.2 ⟨subd5_0_582, List.forall_mem_cons.2 ⟨subd5_0_583, List.forall_mem_cons.2 ⟨subd5_0_584, List.forall_mem_cons.2 ⟨subd5_0_585, List.forall_mem_cons.2 ⟨subd5_0_586, List.forall_mem_cons.2 ⟨subd5_0_587, List.forall_mem_cons.2 ⟨subd5_0_588, List.forall_mem_cons.2 ⟨subd5_0_589, List.forall_mem_cons.2 ⟨subd5_0_590, List.forall_mem_cons.2 ⟨subd5_0_591, List.forall_mem_cons.2 ⟨subd5_0_592, List.forall_mem_cons.2 ⟨subd5_0_593, List.forall_mem_cons.2 ⟨subd5_0_594, List.forall_mem_cons.2 ⟨subd5_0_595, List.forall_mem_cons.2 ⟨subd5_0_596, List.forall_mem_cons.2 ⟨subd5_0_597, List.forall_mem_cons.2 ⟨subd5_0_598, List.forall_mem_cons.2 ⟨subd5_0_599, List.forall_mem_cons.2 ⟨subd5_0_600, List.forall_mem_cons.2 ⟨subd5_0_601, List.forall_mem_cons.2 ⟨subd5_0_602, List.forall_mem_cons.2 ⟨subd5_0_603, List.forall_mem_cons.2 ⟨subd5_0_604, List.forall_mem_cons.2 ⟨subd5_0_605, List.forall_mem_cons.2 ⟨subd5_0_606, List.forall_mem_cons.2 ⟨subd5_0_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_608 : subd5_0 [1, -4, 7] = true := by decide +kernel
theorem subd5_0_609 : subd5_0 [1, -4, 8] = true := by decide +kernel
theorem subd5_0_610 : subd5_0 [1, -3, -7] = true := by decide +kernel
theorem subd5_0_611 : subd5_0 [1, -3, -6] = true := by decide +kernel
theorem subd5_0_612 : subd5_0 [1, -3, -5] = true := by decide +kernel
theorem subd5_0_613 : subd5_0 [1, -3, -4] = true := by decide +kernel
theorem subd5_0_614 : subd5_0 [1, -3, -3] = true := by decide +kernel
theorem subd5_0_615 : subd5_0 [1, -3, -2] = true := by decide +kernel
theorem subd5_0_616 : subd5_0 [1, -3, -1] = true := by decide +kernel
theorem subd5_0_617 : subd5_0 [1, -3, 0] = true := by decide +kernel
theorem subd5_0_618 : subd5_0 [1, -3, 1] = true := by decide +kernel
theorem subd5_0_619 : subd5_0 [1, -3, 2] = true := by decide +kernel
theorem subd5_0_620 : subd5_0 [1, -3, 3] = true := by decide +kernel
theorem subd5_0_621 : subd5_0 [1, -3, 4] = true := by decide +kernel
theorem subd5_0_622 : subd5_0 [1, -3, 5] = true := by decide +kernel
theorem subd5_0_623 : subd5_0 [1, -3, 6] = true := by decide +kernel
theorem subd5_0_624 : subd5_0 [1, -3, 7] = true := by decide +kernel
theorem subd5_0_625 : subd5_0 [1, -3, 8] = true := by decide +kernel
theorem subd5_0_626 : subd5_0 [1, -3, 9] = true := by decide +kernel
theorem subd5_0_627 : subd5_0 [1, -2, -8] = true := by decide +kernel
theorem subd5_0_628 : subd5_0 [1, -2, -7] = true := by decide +kernel
theorem subd5_0_629 : subd5_0 [1, -2, -6] = true := by decide +kernel
theorem subd5_0_630 : subd5_0 [1, -2, -5] = true := by decide +kernel
theorem subd5_0_631 : subd5_0 [1, -2, -4] = true := by decide +kernel
theorem subd5_0_632 : subd5_0 [1, -2, -3] = true := by decide +kernel
theorem subd5_0_633 : subd5_0 [1, -2, -2] = true := by decide +kernel
theorem subd5_0_634 : subd5_0 [1, -2, -1] = true := by decide +kernel
theorem subd5_0_635 : subd5_0 [1, -2, 0] = true := by decide +kernel
theorem subd5_0_636 : subd5_0 [1, -2, 1] = true := by decide +kernel
theorem subd5_0_637 : subd5_0 [1, -2, 2] = true := by decide +kernel
theorem subd5_0_638 : subd5_0 [1, -2, 3] = true := by decide +kernel
theorem subd5_0_639 : subd5_0 [1, -2, 4] = true := by decide +kernel
theorem sbd5_0_19 : ∀ q ∈ blkd5_0_19, subd5_0 q = true := by
  unfold blkd5_0_19
  exact List.forall_mem_cons.2 ⟨subd5_0_608, List.forall_mem_cons.2 ⟨subd5_0_609, List.forall_mem_cons.2 ⟨subd5_0_610, List.forall_mem_cons.2 ⟨subd5_0_611, List.forall_mem_cons.2 ⟨subd5_0_612, List.forall_mem_cons.2 ⟨subd5_0_613, List.forall_mem_cons.2 ⟨subd5_0_614, List.forall_mem_cons.2 ⟨subd5_0_615, List.forall_mem_cons.2 ⟨subd5_0_616, List.forall_mem_cons.2 ⟨subd5_0_617, List.forall_mem_cons.2 ⟨subd5_0_618, List.forall_mem_cons.2 ⟨subd5_0_619, List.forall_mem_cons.2 ⟨subd5_0_620, List.forall_mem_cons.2 ⟨subd5_0_621, List.forall_mem_cons.2 ⟨subd5_0_622, List.forall_mem_cons.2 ⟨subd5_0_623, List.forall_mem_cons.2 ⟨subd5_0_624, List.forall_mem_cons.2 ⟨subd5_0_625, List.forall_mem_cons.2 ⟨subd5_0_626, List.forall_mem_cons.2 ⟨subd5_0_627, List.forall_mem_cons.2 ⟨subd5_0_628, List.forall_mem_cons.2 ⟨subd5_0_629, List.forall_mem_cons.2 ⟨subd5_0_630, List.forall_mem_cons.2 ⟨subd5_0_631, List.forall_mem_cons.2 ⟨subd5_0_632, List.forall_mem_cons.2 ⟨subd5_0_633, List.forall_mem_cons.2 ⟨subd5_0_634, List.forall_mem_cons.2 ⟨subd5_0_635, List.forall_mem_cons.2 ⟨subd5_0_636, List.forall_mem_cons.2 ⟨subd5_0_637, List.forall_mem_cons.2 ⟨subd5_0_638, List.forall_mem_cons.2 ⟨subd5_0_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_640 : subd5_0 [1, -2, 5] = true := by decide +kernel
theorem subd5_0_641 : subd5_0 [1, -2, 6] = true := by decide +kernel
theorem subd5_0_642 : subd5_0 [1, -2, 7] = true := by decide +kernel
theorem subd5_0_643 : subd5_0 [1, -2, 8] = true := by decide +kernel
theorem subd5_0_644 : subd5_0 [1, -2, 9] = true := by decide +kernel
theorem subd5_0_645 : subd5_0 [1, -1, -9] = true := by decide +kernel
theorem subd5_0_646 : subd5_0 [1, -1, -8] = true := by decide +kernel
theorem subd5_0_647 : subd5_0 [1, -1, -7] = true := by decide +kernel
theorem subd5_0_648 : subd5_0 [1, -1, -6] = true := by decide +kernel
theorem subd5_0_649 : subd5_0 [1, -1, -5] = true := by decide +kernel
theorem subd5_0_650 : subd5_0 [1, -1, -4] = true := by decide +kernel
theorem subd5_0_651 : subd5_0 [1, -1, -3] = true := by decide +kernel
theorem subd5_0_652 : subd5_0 [1, -1, -2] = true := by decide +kernel
theorem subd5_0_653 : subd5_0 [1, -1, -1] = true := by decide +kernel
theorem subd5_0_654 : subd5_0 [1, -1, 0] = true := by decide +kernel
theorem subd5_0_655 : subd5_0 [1, -1, 1] = true := by decide +kernel
theorem subd5_0_656 : subd5_0 [1, -1, 2] = true := by decide +kernel
theorem subd5_0_657 : subd5_0 [1, -1, 3] = true := by decide +kernel
theorem subd5_0_658 : subd5_0 [1, -1, 4] = true := by decide +kernel
theorem subd5_0_659 : subd5_0 [1, -1, 5] = true := by decide +kernel
theorem subd5_0_660 : subd5_0 [1, -1, 6] = true := by decide +kernel
theorem subd5_0_661 : subd5_0 [1, -1, 7] = true := by decide +kernel
theorem subd5_0_662 : subd5_0 [1, -1, 8] = true := by decide +kernel
theorem subd5_0_663 : subd5_0 [1, -1, 9] = true := by decide +kernel
theorem subd5_0_664 : subd5_0 [1, -1, 10] = true := by decide +kernel
theorem subd5_0_665 : subd5_0 [1, 0, -10] = true := by decide +kernel
theorem subd5_0_666 : subd5_0 [1, 0, -9] = true := by decide +kernel
theorem subd5_0_667 : subd5_0 [1, 0, -8] = true := by decide +kernel
theorem subd5_0_668 : subd5_0 [1, 0, -7] = true := by decide +kernel
theorem subd5_0_669 : subd5_0 [1, 0, -6] = true := by decide +kernel
theorem subd5_0_670 : subd5_0 [1, 0, -5] = true := by decide +kernel
theorem subd5_0_671 : subd5_0 [1, 0, -4] = true := by decide +kernel
theorem sbd5_0_20 : ∀ q ∈ blkd5_0_20, subd5_0 q = true := by
  unfold blkd5_0_20
  exact List.forall_mem_cons.2 ⟨subd5_0_640, List.forall_mem_cons.2 ⟨subd5_0_641, List.forall_mem_cons.2 ⟨subd5_0_642, List.forall_mem_cons.2 ⟨subd5_0_643, List.forall_mem_cons.2 ⟨subd5_0_644, List.forall_mem_cons.2 ⟨subd5_0_645, List.forall_mem_cons.2 ⟨subd5_0_646, List.forall_mem_cons.2 ⟨subd5_0_647, List.forall_mem_cons.2 ⟨subd5_0_648, List.forall_mem_cons.2 ⟨subd5_0_649, List.forall_mem_cons.2 ⟨subd5_0_650, List.forall_mem_cons.2 ⟨subd5_0_651, List.forall_mem_cons.2 ⟨subd5_0_652, List.forall_mem_cons.2 ⟨subd5_0_653, List.forall_mem_cons.2 ⟨subd5_0_654, List.forall_mem_cons.2 ⟨subd5_0_655, List.forall_mem_cons.2 ⟨subd5_0_656, List.forall_mem_cons.2 ⟨subd5_0_657, List.forall_mem_cons.2 ⟨subd5_0_658, List.forall_mem_cons.2 ⟨subd5_0_659, List.forall_mem_cons.2 ⟨subd5_0_660, List.forall_mem_cons.2 ⟨subd5_0_661, List.forall_mem_cons.2 ⟨subd5_0_662, List.forall_mem_cons.2 ⟨subd5_0_663, List.forall_mem_cons.2 ⟨subd5_0_664, List.forall_mem_cons.2 ⟨subd5_0_665, List.forall_mem_cons.2 ⟨subd5_0_666, List.forall_mem_cons.2 ⟨subd5_0_667, List.forall_mem_cons.2 ⟨subd5_0_668, List.forall_mem_cons.2 ⟨subd5_0_669, List.forall_mem_cons.2 ⟨subd5_0_670, List.forall_mem_cons.2 ⟨subd5_0_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_672 : subd5_0 [1, 0, -3] = true := by decide +kernel
theorem subd5_0_673 : subd5_0 [1, 0, -2] = true := by decide +kernel
theorem subd5_0_674 : subd5_0 [1, 0, -1] = true := by decide +kernel
theorem subd5_0_675 : subd5_0 [1, 0, 0] = true := by decide +kernel
theorem subd5_0_676 : subd5_0 [1, 0, 1] = true := by decide +kernel
theorem subd5_0_677 : subd5_0 [1, 0, 2] = true := by decide +kernel
theorem subd5_0_678 : subd5_0 [1, 0, 3] = true := by decide +kernel
theorem subd5_0_679 : subd5_0 [1, 0, 4] = true := by decide +kernel
theorem subd5_0_680 : subd5_0 [1, 0, 5] = true := by decide +kernel
theorem subd5_0_681 : subd5_0 [1, 0, 6] = true := by decide +kernel
theorem subd5_0_682 : subd5_0 [1, 0, 7] = true := by decide +kernel
theorem subd5_0_683 : subd5_0 [1, 0, 8] = true := by decide +kernel
theorem subd5_0_684 : subd5_0 [1, 0, 9] = true := by decide +kernel
theorem subd5_0_685 : subd5_0 [1, 1, -10] = true := by decide +kernel
theorem subd5_0_686 : subd5_0 [1, 1, -9] = true := by decide +kernel
theorem subd5_0_687 : subd5_0 [1, 1, -8] = true := by decide +kernel
theorem subd5_0_688 : subd5_0 [1, 1, -7] = true := by decide +kernel
theorem subd5_0_689 : subd5_0 [1, 1, -6] = true := by decide +kernel
theorem subd5_0_690 : subd5_0 [1, 1, -5] = true := by decide +kernel
theorem subd5_0_691 : subd5_0 [1, 1, -4] = true := by decide +kernel
theorem subd5_0_692 : subd5_0 [1, 1, -3] = true := by decide +kernel
theorem subd5_0_693 : subd5_0 [1, 1, -2] = true := by decide +kernel
theorem subd5_0_694 : subd5_0 [1, 1, -1] = true := by decide +kernel
theorem subd5_0_695 : subd5_0 [1, 1, 0] = true := by decide +kernel
theorem subd5_0_696 : subd5_0 [1, 1, 1] = true := by decide +kernel
theorem subd5_0_697 : subd5_0 [1, 1, 2] = true := by decide +kernel
theorem subd5_0_698 : subd5_0 [1, 1, 3] = true := by decide +kernel
theorem subd5_0_699 : subd5_0 [1, 1, 4] = true := by decide +kernel
theorem subd5_0_700 : subd5_0 [1, 1, 5] = true := by decide +kernel
theorem subd5_0_701 : subd5_0 [1, 1, 6] = true := by decide +kernel
theorem subd5_0_702 : subd5_0 [1, 1, 7] = true := by decide +kernel
theorem subd5_0_703 : subd5_0 [1, 1, 8] = true := by decide +kernel
theorem sbd5_0_21 : ∀ q ∈ blkd5_0_21, subd5_0 q = true := by
  unfold blkd5_0_21
  exact List.forall_mem_cons.2 ⟨subd5_0_672, List.forall_mem_cons.2 ⟨subd5_0_673, List.forall_mem_cons.2 ⟨subd5_0_674, List.forall_mem_cons.2 ⟨subd5_0_675, List.forall_mem_cons.2 ⟨subd5_0_676, List.forall_mem_cons.2 ⟨subd5_0_677, List.forall_mem_cons.2 ⟨subd5_0_678, List.forall_mem_cons.2 ⟨subd5_0_679, List.forall_mem_cons.2 ⟨subd5_0_680, List.forall_mem_cons.2 ⟨subd5_0_681, List.forall_mem_cons.2 ⟨subd5_0_682, List.forall_mem_cons.2 ⟨subd5_0_683, List.forall_mem_cons.2 ⟨subd5_0_684, List.forall_mem_cons.2 ⟨subd5_0_685, List.forall_mem_cons.2 ⟨subd5_0_686, List.forall_mem_cons.2 ⟨subd5_0_687, List.forall_mem_cons.2 ⟨subd5_0_688, List.forall_mem_cons.2 ⟨subd5_0_689, List.forall_mem_cons.2 ⟨subd5_0_690, List.forall_mem_cons.2 ⟨subd5_0_691, List.forall_mem_cons.2 ⟨subd5_0_692, List.forall_mem_cons.2 ⟨subd5_0_693, List.forall_mem_cons.2 ⟨subd5_0_694, List.forall_mem_cons.2 ⟨subd5_0_695, List.forall_mem_cons.2 ⟨subd5_0_696, List.forall_mem_cons.2 ⟨subd5_0_697, List.forall_mem_cons.2 ⟨subd5_0_698, List.forall_mem_cons.2 ⟨subd5_0_699, List.forall_mem_cons.2 ⟨subd5_0_700, List.forall_mem_cons.2 ⟨subd5_0_701, List.forall_mem_cons.2 ⟨subd5_0_702, List.forall_mem_cons.2 ⟨subd5_0_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_704 : subd5_0 [1, 1, 9] = true := by decide +kernel
theorem subd5_0_705 : subd5_0 [1, 2, -10] = true := by decide +kernel
theorem subd5_0_706 : subd5_0 [1, 2, -9] = true := by decide +kernel
theorem subd5_0_707 : subd5_0 [1, 2, -8] = true := by decide +kernel
theorem subd5_0_708 : subd5_0 [1, 2, -7] = true := by decide +kernel
theorem subd5_0_709 : subd5_0 [1, 2, -6] = true := by decide +kernel
theorem subd5_0_710 : subd5_0 [1, 2, -5] = true := by decide +kernel
theorem subd5_0_711 : subd5_0 [1, 2, -4] = true := by decide +kernel
theorem subd5_0_712 : subd5_0 [1, 2, -3] = true := by decide +kernel
theorem subd5_0_713 : subd5_0 [1, 2, -2] = true := by decide +kernel
theorem subd5_0_714 : subd5_0 [1, 2, -1] = true := by decide +kernel
theorem subd5_0_715 : subd5_0 [1, 2, 0] = true := by decide +kernel
theorem subd5_0_716 : subd5_0 [1, 2, 1] = true := by decide +kernel
theorem subd5_0_717 : subd5_0 [1, 2, 2] = true := by decide +kernel
theorem subd5_0_718 : subd5_0 [1, 2, 3] = true := by decide +kernel
theorem subd5_0_719 : subd5_0 [1, 2, 4] = true := by decide +kernel
theorem subd5_0_720 : subd5_0 [1, 2, 5] = true := by decide +kernel
theorem subd5_0_721 : subd5_0 [1, 2, 6] = true := by decide +kernel
theorem subd5_0_722 : subd5_0 [1, 2, 7] = true := by decide +kernel
theorem subd5_0_723 : subd5_0 [1, 2, 8] = true := by decide +kernel
theorem subd5_0_724 : subd5_0 [1, 3, -9] = true := by decide +kernel
theorem subd5_0_725 : subd5_0 [1, 3, -8] = true := by decide +kernel
theorem subd5_0_726 : subd5_0 [1, 3, -7] = true := by decide +kernel
theorem subd5_0_727 : subd5_0 [1, 3, -6] = true := by decide +kernel
theorem subd5_0_728 : subd5_0 [1, 3, -5] = true := by decide +kernel
theorem subd5_0_729 : subd5_0 [1, 3, -4] = true := by decide +kernel
theorem subd5_0_730 : subd5_0 [1, 3, -3] = true := by decide +kernel
theorem subd5_0_731 : subd5_0 [1, 3, -2] = true := by decide +kernel
theorem subd5_0_732 : subd5_0 [1, 3, -1] = true := by decide +kernel
theorem subd5_0_733 : subd5_0 [1, 3, 0] = true := by decide +kernel
theorem subd5_0_734 : subd5_0 [1, 3, 1] = true := by decide +kernel
theorem subd5_0_735 : subd5_0 [1, 3, 2] = true := by decide +kernel
theorem sbd5_0_22 : ∀ q ∈ blkd5_0_22, subd5_0 q = true := by
  unfold blkd5_0_22
  exact List.forall_mem_cons.2 ⟨subd5_0_704, List.forall_mem_cons.2 ⟨subd5_0_705, List.forall_mem_cons.2 ⟨subd5_0_706, List.forall_mem_cons.2 ⟨subd5_0_707, List.forall_mem_cons.2 ⟨subd5_0_708, List.forall_mem_cons.2 ⟨subd5_0_709, List.forall_mem_cons.2 ⟨subd5_0_710, List.forall_mem_cons.2 ⟨subd5_0_711, List.forall_mem_cons.2 ⟨subd5_0_712, List.forall_mem_cons.2 ⟨subd5_0_713, List.forall_mem_cons.2 ⟨subd5_0_714, List.forall_mem_cons.2 ⟨subd5_0_715, List.forall_mem_cons.2 ⟨subd5_0_716, List.forall_mem_cons.2 ⟨subd5_0_717, List.forall_mem_cons.2 ⟨subd5_0_718, List.forall_mem_cons.2 ⟨subd5_0_719, List.forall_mem_cons.2 ⟨subd5_0_720, List.forall_mem_cons.2 ⟨subd5_0_721, List.forall_mem_cons.2 ⟨subd5_0_722, List.forall_mem_cons.2 ⟨subd5_0_723, List.forall_mem_cons.2 ⟨subd5_0_724, List.forall_mem_cons.2 ⟨subd5_0_725, List.forall_mem_cons.2 ⟨subd5_0_726, List.forall_mem_cons.2 ⟨subd5_0_727, List.forall_mem_cons.2 ⟨subd5_0_728, List.forall_mem_cons.2 ⟨subd5_0_729, List.forall_mem_cons.2 ⟨subd5_0_730, List.forall_mem_cons.2 ⟨subd5_0_731, List.forall_mem_cons.2 ⟨subd5_0_732, List.forall_mem_cons.2 ⟨subd5_0_733, List.forall_mem_cons.2 ⟨subd5_0_734, List.forall_mem_cons.2 ⟨subd5_0_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_736 : subd5_0 [1, 3, 3] = true := by decide +kernel
theorem subd5_0_737 : subd5_0 [1, 3, 4] = true := by decide +kernel
theorem subd5_0_738 : subd5_0 [1, 3, 5] = true := by decide +kernel
theorem subd5_0_739 : subd5_0 [1, 3, 6] = true := by decide +kernel
theorem subd5_0_740 : subd5_0 [1, 3, 7] = true := by decide +kernel
theorem subd5_0_741 : subd5_0 [1, 4, -8] = true := by decide +kernel
theorem subd5_0_742 : subd5_0 [1, 4, -7] = true := by decide +kernel
theorem subd5_0_743 : subd5_0 [1, 4, -6] = true := by decide +kernel
theorem subd5_0_744 : subd5_0 [1, 4, -5] = true := by decide +kernel
theorem subd5_0_745 : subd5_0 [1, 4, -4] = true := by decide +kernel
theorem subd5_0_746 : subd5_0 [1, 4, -3] = true := by decide +kernel
theorem subd5_0_747 : subd5_0 [1, 4, -2] = true := by decide +kernel
theorem subd5_0_748 : subd5_0 [1, 4, -1] = true := by decide +kernel
theorem subd5_0_749 : subd5_0 [1, 4, 0] = true := by decide +kernel
theorem subd5_0_750 : subd5_0 [1, 4, 1] = true := by decide +kernel
theorem subd5_0_751 : subd5_0 [1, 4, 2] = true := by decide +kernel
theorem subd5_0_752 : subd5_0 [1, 4, 3] = true := by decide +kernel
theorem subd5_0_753 : subd5_0 [1, 4, 4] = true := by decide +kernel
theorem subd5_0_754 : subd5_0 [1, 4, 5] = true := by decide +kernel
theorem subd5_0_755 : subd5_0 [1, 5] = true := by decide +kernel
theorem subd5_0_756 : subd5_0 [2, -6] = true := by decide +kernel
theorem subd5_0_757 : subd5_0 [2, -5] = true := by decide +kernel
theorem subd5_0_758 : subd5_0 [2, -4] = true := by decide +kernel
theorem subd5_0_759 : subd5_0 [2, -3, -6] = true := by decide +kernel
theorem subd5_0_760 : subd5_0 [2, -3, -5] = true := by decide +kernel
theorem subd5_0_761 : subd5_0 [2, -3, -4] = true := by decide +kernel
theorem subd5_0_762 : subd5_0 [2, -3, -3] = true := by decide +kernel
theorem subd5_0_763 : subd5_0 [2, -3, -2] = true := by decide +kernel
theorem subd5_0_764 : subd5_0 [2, -3, -1] = true := by decide +kernel
theorem subd5_0_765 : subd5_0 [2, -3, 0] = true := by decide +kernel
theorem subd5_0_766 : subd5_0 [2, -3, 1] = true := by decide +kernel
theorem subd5_0_767 : subd5_0 [2, -3, 2] = true := by decide +kernel
theorem sbd5_0_23 : ∀ q ∈ blkd5_0_23, subd5_0 q = true := by
  unfold blkd5_0_23
  exact List.forall_mem_cons.2 ⟨subd5_0_736, List.forall_mem_cons.2 ⟨subd5_0_737, List.forall_mem_cons.2 ⟨subd5_0_738, List.forall_mem_cons.2 ⟨subd5_0_739, List.forall_mem_cons.2 ⟨subd5_0_740, List.forall_mem_cons.2 ⟨subd5_0_741, List.forall_mem_cons.2 ⟨subd5_0_742, List.forall_mem_cons.2 ⟨subd5_0_743, List.forall_mem_cons.2 ⟨subd5_0_744, List.forall_mem_cons.2 ⟨subd5_0_745, List.forall_mem_cons.2 ⟨subd5_0_746, List.forall_mem_cons.2 ⟨subd5_0_747, List.forall_mem_cons.2 ⟨subd5_0_748, List.forall_mem_cons.2 ⟨subd5_0_749, List.forall_mem_cons.2 ⟨subd5_0_750, List.forall_mem_cons.2 ⟨subd5_0_751, List.forall_mem_cons.2 ⟨subd5_0_752, List.forall_mem_cons.2 ⟨subd5_0_753, List.forall_mem_cons.2 ⟨subd5_0_754, List.forall_mem_cons.2 ⟨subd5_0_755, List.forall_mem_cons.2 ⟨subd5_0_756, List.forall_mem_cons.2 ⟨subd5_0_757, List.forall_mem_cons.2 ⟨subd5_0_758, List.forall_mem_cons.2 ⟨subd5_0_759, List.forall_mem_cons.2 ⟨subd5_0_760, List.forall_mem_cons.2 ⟨subd5_0_761, List.forall_mem_cons.2 ⟨subd5_0_762, List.forall_mem_cons.2 ⟨subd5_0_763, List.forall_mem_cons.2 ⟨subd5_0_764, List.forall_mem_cons.2 ⟨subd5_0_765, List.forall_mem_cons.2 ⟨subd5_0_766, List.forall_mem_cons.2 ⟨subd5_0_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_768 : subd5_0 [2, -3, 3] = true := by decide +kernel
theorem subd5_0_769 : subd5_0 [2, -3, 4] = true := by decide +kernel
theorem subd5_0_770 : subd5_0 [2, -3, 5] = true := by decide +kernel
theorem subd5_0_771 : subd5_0 [2, -3, 6] = true := by decide +kernel
theorem subd5_0_772 : subd5_0 [2, -3, 7] = true := by decide +kernel
theorem subd5_0_773 : subd5_0 [2, -3, 8] = true := by decide +kernel
theorem subd5_0_774 : subd5_0 [2, -3, 9] = true := by decide +kernel
theorem subd5_0_775 : subd5_0 [2, -2, -7] = true := by decide +kernel
theorem subd5_0_776 : subd5_0 [2, -2, -6] = true := by decide +kernel
theorem subd5_0_777 : subd5_0 [2, -2, -5] = true := by decide +kernel
theorem subd5_0_778 : subd5_0 [2, -2, -4] = true := by decide +kernel
theorem subd5_0_779 : subd5_0 [2, -2, -3] = true := by decide +kernel
theorem subd5_0_780 : subd5_0 [2, -2, -2] = true := by decide +kernel
theorem subd5_0_781 : subd5_0 [2, -2, -1] = true := by decide +kernel
theorem subd5_0_782 : subd5_0 [2, -2, 0] = true := by decide +kernel
theorem subd5_0_783 : subd5_0 [2, -2, 1] = true := by decide +kernel
theorem subd5_0_784 : subd5_0 [2, -2, 2] = true := by decide +kernel
theorem subd5_0_785 : subd5_0 [2, -2, 3] = true := by decide +kernel
theorem subd5_0_786 : subd5_0 [2, -2, 4] = true := by decide +kernel
theorem subd5_0_787 : subd5_0 [2, -2, 5] = true := by decide +kernel
theorem subd5_0_788 : subd5_0 [2, -2, 6] = true := by decide +kernel
theorem subd5_0_789 : subd5_0 [2, -2, 7] = true := by decide +kernel
theorem subd5_0_790 : subd5_0 [2, -2, 8] = true := by decide +kernel
theorem subd5_0_791 : subd5_0 [2, -2, 9] = true := by decide +kernel
theorem subd5_0_792 : subd5_0 [2, -1, -8] = true := by decide +kernel
theorem subd5_0_793 : subd5_0 [2, -1, -7] = true := by decide +kernel
theorem subd5_0_794 : subd5_0 [2, -1, -6] = true := by decide +kernel
theorem subd5_0_795 : subd5_0 [2, -1, -5] = true := by decide +kernel
theorem subd5_0_796 : subd5_0 [2, -1, -4] = true := by decide +kernel
theorem subd5_0_797 : subd5_0 [2, -1, -3] = true := by decide +kernel
theorem subd5_0_798 : subd5_0 [2, -1, -2] = true := by decide +kernel
theorem subd5_0_799 : subd5_0 [2, -1, -1] = true := by decide +kernel
theorem sbd5_0_24 : ∀ q ∈ blkd5_0_24, subd5_0 q = true := by
  unfold blkd5_0_24
  exact List.forall_mem_cons.2 ⟨subd5_0_768, List.forall_mem_cons.2 ⟨subd5_0_769, List.forall_mem_cons.2 ⟨subd5_0_770, List.forall_mem_cons.2 ⟨subd5_0_771, List.forall_mem_cons.2 ⟨subd5_0_772, List.forall_mem_cons.2 ⟨subd5_0_773, List.forall_mem_cons.2 ⟨subd5_0_774, List.forall_mem_cons.2 ⟨subd5_0_775, List.forall_mem_cons.2 ⟨subd5_0_776, List.forall_mem_cons.2 ⟨subd5_0_777, List.forall_mem_cons.2 ⟨subd5_0_778, List.forall_mem_cons.2 ⟨subd5_0_779, List.forall_mem_cons.2 ⟨subd5_0_780, List.forall_mem_cons.2 ⟨subd5_0_781, List.forall_mem_cons.2 ⟨subd5_0_782, List.forall_mem_cons.2 ⟨subd5_0_783, List.forall_mem_cons.2 ⟨subd5_0_784, List.forall_mem_cons.2 ⟨subd5_0_785, List.forall_mem_cons.2 ⟨subd5_0_786, List.forall_mem_cons.2 ⟨subd5_0_787, List.forall_mem_cons.2 ⟨subd5_0_788, List.forall_mem_cons.2 ⟨subd5_0_789, List.forall_mem_cons.2 ⟨subd5_0_790, List.forall_mem_cons.2 ⟨subd5_0_791, List.forall_mem_cons.2 ⟨subd5_0_792, List.forall_mem_cons.2 ⟨subd5_0_793, List.forall_mem_cons.2 ⟨subd5_0_794, List.forall_mem_cons.2 ⟨subd5_0_795, List.forall_mem_cons.2 ⟨subd5_0_796, List.forall_mem_cons.2 ⟨subd5_0_797, List.forall_mem_cons.2 ⟨subd5_0_798, List.forall_mem_cons.2 ⟨subd5_0_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_800 : subd5_0 [2, -1, 0] = true := by decide +kernel
theorem subd5_0_801 : subd5_0 [2, -1, 1] = true := by decide +kernel
theorem subd5_0_802 : subd5_0 [2, -1, 2] = true := by decide +kernel
theorem subd5_0_803 : subd5_0 [2, -1, 3] = true := by decide +kernel
theorem subd5_0_804 : subd5_0 [2, -1, 4] = true := by decide +kernel
theorem subd5_0_805 : subd5_0 [2, -1, 5] = true := by decide +kernel
theorem subd5_0_806 : subd5_0 [2, -1, 6] = true := by decide +kernel
theorem subd5_0_807 : subd5_0 [2, -1, 7] = true := by decide +kernel
theorem subd5_0_808 : subd5_0 [2, -1, 8] = true := by decide +kernel
theorem subd5_0_809 : subd5_0 [2, -1, 9] = true := by decide +kernel
theorem subd5_0_810 : subd5_0 [2, 0, -9] = true := by decide +kernel
theorem subd5_0_811 : subd5_0 [2, 0, -8] = true := by decide +kernel
theorem subd5_0_812 : subd5_0 [2, 0, -7] = true := by decide +kernel
theorem subd5_0_813 : subd5_0 [2, 0, -6] = true := by decide +kernel
theorem subd5_0_814 : subd5_0 [2, 0, -5] = true := by decide +kernel
theorem subd5_0_815 : subd5_0 [2, 0, -4] = true := by decide +kernel
theorem subd5_0_816 : subd5_0 [2, 0, -3] = true := by decide +kernel
theorem subd5_0_817 : subd5_0 [2, 0, -2] = true := by decide +kernel
theorem subd5_0_818 : subd5_0 [2, 0, -1] = true := by decide +kernel
theorem subd5_0_819 : subd5_0 [2, 0, 0] = true := by decide +kernel
theorem subd5_0_820 : subd5_0 [2, 0, 1] = true := by decide +kernel
theorem subd5_0_821 : subd5_0 [2, 0, 2] = true := by decide +kernel
theorem subd5_0_822 : subd5_0 [2, 0, 3] = true := by decide +kernel
theorem subd5_0_823 : subd5_0 [2, 0, 4] = true := by decide +kernel
theorem subd5_0_824 : subd5_0 [2, 0, 5] = true := by decide +kernel
theorem subd5_0_825 : subd5_0 [2, 0, 6] = true := by decide +kernel
theorem subd5_0_826 : subd5_0 [2, 0, 7] = true := by decide +kernel
theorem subd5_0_827 : subd5_0 [2, 0, 8] = true := by decide +kernel
theorem subd5_0_828 : subd5_0 [2, 0, 9] = true := by decide +kernel
theorem subd5_0_829 : subd5_0 [2, 1, -9] = true := by decide +kernel
theorem subd5_0_830 : subd5_0 [2, 1, -8] = true := by decide +kernel
theorem subd5_0_831 : subd5_0 [2, 1, -7] = true := by decide +kernel
theorem sbd5_0_25 : ∀ q ∈ blkd5_0_25, subd5_0 q = true := by
  unfold blkd5_0_25
  exact List.forall_mem_cons.2 ⟨subd5_0_800, List.forall_mem_cons.2 ⟨subd5_0_801, List.forall_mem_cons.2 ⟨subd5_0_802, List.forall_mem_cons.2 ⟨subd5_0_803, List.forall_mem_cons.2 ⟨subd5_0_804, List.forall_mem_cons.2 ⟨subd5_0_805, List.forall_mem_cons.2 ⟨subd5_0_806, List.forall_mem_cons.2 ⟨subd5_0_807, List.forall_mem_cons.2 ⟨subd5_0_808, List.forall_mem_cons.2 ⟨subd5_0_809, List.forall_mem_cons.2 ⟨subd5_0_810, List.forall_mem_cons.2 ⟨subd5_0_811, List.forall_mem_cons.2 ⟨subd5_0_812, List.forall_mem_cons.2 ⟨subd5_0_813, List.forall_mem_cons.2 ⟨subd5_0_814, List.forall_mem_cons.2 ⟨subd5_0_815, List.forall_mem_cons.2 ⟨subd5_0_816, List.forall_mem_cons.2 ⟨subd5_0_817, List.forall_mem_cons.2 ⟨subd5_0_818, List.forall_mem_cons.2 ⟨subd5_0_819, List.forall_mem_cons.2 ⟨subd5_0_820, List.forall_mem_cons.2 ⟨subd5_0_821, List.forall_mem_cons.2 ⟨subd5_0_822, List.forall_mem_cons.2 ⟨subd5_0_823, List.forall_mem_cons.2 ⟨subd5_0_824, List.forall_mem_cons.2 ⟨subd5_0_825, List.forall_mem_cons.2 ⟨subd5_0_826, List.forall_mem_cons.2 ⟨subd5_0_827, List.forall_mem_cons.2 ⟨subd5_0_828, List.forall_mem_cons.2 ⟨subd5_0_829, List.forall_mem_cons.2 ⟨subd5_0_830, List.forall_mem_cons.2 ⟨subd5_0_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_832 : subd5_0 [2, 1, -6] = true := by decide +kernel
theorem subd5_0_833 : subd5_0 [2, 1, -5] = true := by decide +kernel
theorem subd5_0_834 : subd5_0 [2, 1, -4] = true := by decide +kernel
theorem subd5_0_835 : subd5_0 [2, 1, -3] = true := by decide +kernel
theorem subd5_0_836 : subd5_0 [2, 1, -2] = true := by decide +kernel
theorem subd5_0_837 : subd5_0 [2, 1, -1] = true := by decide +kernel
theorem subd5_0_838 : subd5_0 [2, 1, 0] = true := by decide +kernel
theorem subd5_0_839 : subd5_0 [2, 1, 1] = true := by decide +kernel
theorem subd5_0_840 : subd5_0 [2, 1, 2] = true := by decide +kernel
theorem subd5_0_841 : subd5_0 [2, 1, 3] = true := by decide +kernel
theorem subd5_0_842 : subd5_0 [2, 1, 4] = true := by decide +kernel
theorem subd5_0_843 : subd5_0 [2, 1, 5] = true := by decide +kernel
theorem subd5_0_844 : subd5_0 [2, 1, 6] = true := by decide +kernel
theorem subd5_0_845 : subd5_0 [2, 1, 7] = true := by decide +kernel
theorem subd5_0_846 : subd5_0 [2, 1, 8] = true := by decide +kernel
theorem subd5_0_847 : subd5_0 [2, 1, 9] = true := by decide +kernel
theorem subd5_0_848 : subd5_0 [2, 2, -9] = true := by decide +kernel
theorem subd5_0_849 : subd5_0 [2, 2, -8] = true := by decide +kernel
theorem subd5_0_850 : subd5_0 [2, 2, -7] = true := by decide +kernel
theorem subd5_0_851 : subd5_0 [2, 2, -6] = true := by decide +kernel
theorem subd5_0_852 : subd5_0 [2, 2, -5] = true := by decide +kernel
theorem subd5_0_853 : subd5_0 [2, 2, -4] = true := by decide +kernel
theorem subd5_0_854 : subd5_0 [2, 2, -3] = true := by decide +kernel
theorem subd5_0_855 : subd5_0 [2, 2, -2] = true := by decide +kernel
theorem subd5_0_856 : subd5_0 [2, 2, -1] = true := by decide +kernel
theorem subd5_0_857 : subd5_0 [2, 2, 0] = true := by decide +kernel
theorem subd5_0_858 : subd5_0 [2, 2, 1] = true := by decide +kernel
theorem subd5_0_859 : subd5_0 [2, 2, 2] = true := by decide +kernel
theorem subd5_0_860 : subd5_0 [2, 2, 3] = true := by decide +kernel
theorem subd5_0_861 : subd5_0 [2, 2, 4] = true := by decide +kernel
theorem subd5_0_862 : subd5_0 [2, 2, 5] = true := by decide +kernel
theorem subd5_0_863 : subd5_0 [2, 2, 6] = true := by decide +kernel
theorem sbd5_0_26 : ∀ q ∈ blkd5_0_26, subd5_0 q = true := by
  unfold blkd5_0_26
  exact List.forall_mem_cons.2 ⟨subd5_0_832, List.forall_mem_cons.2 ⟨subd5_0_833, List.forall_mem_cons.2 ⟨subd5_0_834, List.forall_mem_cons.2 ⟨subd5_0_835, List.forall_mem_cons.2 ⟨subd5_0_836, List.forall_mem_cons.2 ⟨subd5_0_837, List.forall_mem_cons.2 ⟨subd5_0_838, List.forall_mem_cons.2 ⟨subd5_0_839, List.forall_mem_cons.2 ⟨subd5_0_840, List.forall_mem_cons.2 ⟨subd5_0_841, List.forall_mem_cons.2 ⟨subd5_0_842, List.forall_mem_cons.2 ⟨subd5_0_843, List.forall_mem_cons.2 ⟨subd5_0_844, List.forall_mem_cons.2 ⟨subd5_0_845, List.forall_mem_cons.2 ⟨subd5_0_846, List.forall_mem_cons.2 ⟨subd5_0_847, List.forall_mem_cons.2 ⟨subd5_0_848, List.forall_mem_cons.2 ⟨subd5_0_849, List.forall_mem_cons.2 ⟨subd5_0_850, List.forall_mem_cons.2 ⟨subd5_0_851, List.forall_mem_cons.2 ⟨subd5_0_852, List.forall_mem_cons.2 ⟨subd5_0_853, List.forall_mem_cons.2 ⟨subd5_0_854, List.forall_mem_cons.2 ⟨subd5_0_855, List.forall_mem_cons.2 ⟨subd5_0_856, List.forall_mem_cons.2 ⟨subd5_0_857, List.forall_mem_cons.2 ⟨subd5_0_858, List.forall_mem_cons.2 ⟨subd5_0_859, List.forall_mem_cons.2 ⟨subd5_0_860, List.forall_mem_cons.2 ⟨subd5_0_861, List.forall_mem_cons.2 ⟨subd5_0_862, List.forall_mem_cons.2 ⟨subd5_0_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_864 : subd5_0 [2, 2, 7] = true := by decide +kernel
theorem subd5_0_865 : subd5_0 [2, 2, 8] = true := by decide +kernel
theorem subd5_0_866 : subd5_0 [2, 3, -8] = true := by decide +kernel
theorem subd5_0_867 : subd5_0 [2, 3, -7] = true := by decide +kernel
theorem subd5_0_868 : subd5_0 [2, 3, -6] = true := by decide +kernel
theorem subd5_0_869 : subd5_0 [2, 3, -5] = true := by decide +kernel
theorem subd5_0_870 : subd5_0 [2, 3, -4] = true := by decide +kernel
theorem subd5_0_871 : subd5_0 [2, 3, -3] = true := by decide +kernel
theorem subd5_0_872 : subd5_0 [2, 3, -2] = true := by decide +kernel
theorem subd5_0_873 : subd5_0 [2, 3, -1] = true := by decide +kernel
theorem subd5_0_874 : subd5_0 [2, 3, 0] = true := by decide +kernel
theorem subd5_0_875 : subd5_0 [2, 3, 1] = true := by decide +kernel
theorem subd5_0_876 : subd5_0 [2, 3, 2] = true := by decide +kernel
theorem subd5_0_877 : subd5_0 [2, 3, 3] = true := by decide +kernel
theorem subd5_0_878 : subd5_0 [2, 3, 4] = true := by decide +kernel
theorem subd5_0_879 : subd5_0 [2, 3, 5] = true := by decide +kernel
theorem subd5_0_880 : subd5_0 [2, 3, 6] = true := by decide +kernel
theorem subd5_0_881 : subd5_0 [2, 4] = true := by decide +kernel
theorem subd5_0_882 : subd5_0 [2, 5] = true := by decide +kernel
theorem subd5_0_883 : subd5_0 [3, -5] = true := by decide +kernel
theorem subd5_0_884 : subd5_0 [3, -4] = true := by decide +kernel
theorem subd5_0_885 : subd5_0 [3, -3, -5] = true := by decide +kernel
theorem subd5_0_886 : subd5_0 [3, -3, -4] = true := by decide +kernel
theorem subd5_0_887 : subd5_0 [3, -3, -3] = true := by decide +kernel
theorem subd5_0_888 : subd5_0 [3, -3, -2] = true := by decide +kernel
theorem subd5_0_889 : subd5_0 [3, -3, -1] = true := by decide +kernel
theorem subd5_0_890 : subd5_0 [3, -3, 0] = true := by decide +kernel
theorem subd5_0_891 : subd5_0 [3, -3, 1] = true := by decide +kernel
theorem subd5_0_892 : subd5_0 [3, -3, 2] = true := by decide +kernel
theorem subd5_0_893 : subd5_0 [3, -3, 3] = true := by decide +kernel
theorem subd5_0_894 : subd5_0 [3, -3, 4] = true := by decide +kernel
theorem subd5_0_895 : subd5_0 [3, -3, 5] = true := by decide +kernel
theorem sbd5_0_27 : ∀ q ∈ blkd5_0_27, subd5_0 q = true := by
  unfold blkd5_0_27
  exact List.forall_mem_cons.2 ⟨subd5_0_864, List.forall_mem_cons.2 ⟨subd5_0_865, List.forall_mem_cons.2 ⟨subd5_0_866, List.forall_mem_cons.2 ⟨subd5_0_867, List.forall_mem_cons.2 ⟨subd5_0_868, List.forall_mem_cons.2 ⟨subd5_0_869, List.forall_mem_cons.2 ⟨subd5_0_870, List.forall_mem_cons.2 ⟨subd5_0_871, List.forall_mem_cons.2 ⟨subd5_0_872, List.forall_mem_cons.2 ⟨subd5_0_873, List.forall_mem_cons.2 ⟨subd5_0_874, List.forall_mem_cons.2 ⟨subd5_0_875, List.forall_mem_cons.2 ⟨subd5_0_876, List.forall_mem_cons.2 ⟨subd5_0_877, List.forall_mem_cons.2 ⟨subd5_0_878, List.forall_mem_cons.2 ⟨subd5_0_879, List.forall_mem_cons.2 ⟨subd5_0_880, List.forall_mem_cons.2 ⟨subd5_0_881, List.forall_mem_cons.2 ⟨subd5_0_882, List.forall_mem_cons.2 ⟨subd5_0_883, List.forall_mem_cons.2 ⟨subd5_0_884, List.forall_mem_cons.2 ⟨subd5_0_885, List.forall_mem_cons.2 ⟨subd5_0_886, List.forall_mem_cons.2 ⟨subd5_0_887, List.forall_mem_cons.2 ⟨subd5_0_888, List.forall_mem_cons.2 ⟨subd5_0_889, List.forall_mem_cons.2 ⟨subd5_0_890, List.forall_mem_cons.2 ⟨subd5_0_891, List.forall_mem_cons.2 ⟨subd5_0_892, List.forall_mem_cons.2 ⟨subd5_0_893, List.forall_mem_cons.2 ⟨subd5_0_894, List.forall_mem_cons.2 ⟨subd5_0_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_896 : subd5_0 [3, -3, 6] = true := by decide +kernel
theorem subd5_0_897 : subd5_0 [3, -3, 7] = true := by decide +kernel
theorem subd5_0_898 : subd5_0 [3, -3, 8] = true := by decide +kernel
theorem subd5_0_899 : subd5_0 [3, -2, -6] = true := by decide +kernel
theorem subd5_0_900 : subd5_0 [3, -2, -5] = true := by decide +kernel
theorem subd5_0_901 : subd5_0 [3, -2, -4] = true := by decide +kernel
theorem subd5_0_902 : subd5_0 [3, -2, -3] = true := by decide +kernel
theorem subd5_0_903 : subd5_0 [3, -2, -2] = true := by decide +kernel
theorem subd5_0_904 : subd5_0 [3, -2, -1] = true := by decide +kernel
theorem subd5_0_905 : subd5_0 [3, -2, 0] = true := by decide +kernel
theorem subd5_0_906 : subd5_0 [3, -2, 1] = true := by decide +kernel
theorem subd5_0_907 : subd5_0 [3, -2, 2] = true := by decide +kernel
theorem subd5_0_908 : subd5_0 [3, -2, 3] = true := by decide +kernel
theorem subd5_0_909 : subd5_0 [3, -2, 4] = true := by decide +kernel
theorem subd5_0_910 : subd5_0 [3, -2, 5] = true := by decide +kernel
theorem subd5_0_911 : subd5_0 [3, -2, 6] = true := by decide +kernel
theorem subd5_0_912 : subd5_0 [3, -2, 7] = true := by decide +kernel
theorem subd5_0_913 : subd5_0 [3, -2, 8] = true := by decide +kernel
theorem subd5_0_914 : subd5_0 [3, -2, 9] = true := by decide +kernel
theorem subd5_0_915 : subd5_0 [3, -1, -7] = true := by decide +kernel
theorem subd5_0_916 : subd5_0 [3, -1, -6] = true := by decide +kernel
theorem subd5_0_917 : subd5_0 [3, -1, -5] = true := by decide +kernel
theorem subd5_0_918 : subd5_0 [3, -1, -4] = true := by decide +kernel
theorem subd5_0_919 : subd5_0 [3, -1, -3] = true := by decide +kernel
theorem subd5_0_920 : subd5_0 [3, -1, -2] = true := by decide +kernel
theorem subd5_0_921 : subd5_0 [3, -1, -1] = true := by decide +kernel
theorem subd5_0_922 : subd5_0 [3, -1, 0] = true := by decide +kernel
theorem subd5_0_923 : subd5_0 [3, -1, 1] = true := by decide +kernel
theorem subd5_0_924 : subd5_0 [3, -1, 2] = true := by decide +kernel
theorem subd5_0_925 : subd5_0 [3, -1, 3] = true := by decide +kernel
theorem subd5_0_926 : subd5_0 [3, -1, 4] = true := by decide +kernel
theorem subd5_0_927 : subd5_0 [3, -1, 5] = true := by decide +kernel
theorem sbd5_0_28 : ∀ q ∈ blkd5_0_28, subd5_0 q = true := by
  unfold blkd5_0_28
  exact List.forall_mem_cons.2 ⟨subd5_0_896, List.forall_mem_cons.2 ⟨subd5_0_897, List.forall_mem_cons.2 ⟨subd5_0_898, List.forall_mem_cons.2 ⟨subd5_0_899, List.forall_mem_cons.2 ⟨subd5_0_900, List.forall_mem_cons.2 ⟨subd5_0_901, List.forall_mem_cons.2 ⟨subd5_0_902, List.forall_mem_cons.2 ⟨subd5_0_903, List.forall_mem_cons.2 ⟨subd5_0_904, List.forall_mem_cons.2 ⟨subd5_0_905, List.forall_mem_cons.2 ⟨subd5_0_906, List.forall_mem_cons.2 ⟨subd5_0_907, List.forall_mem_cons.2 ⟨subd5_0_908, List.forall_mem_cons.2 ⟨subd5_0_909, List.forall_mem_cons.2 ⟨subd5_0_910, List.forall_mem_cons.2 ⟨subd5_0_911, List.forall_mem_cons.2 ⟨subd5_0_912, List.forall_mem_cons.2 ⟨subd5_0_913, List.forall_mem_cons.2 ⟨subd5_0_914, List.forall_mem_cons.2 ⟨subd5_0_915, List.forall_mem_cons.2 ⟨subd5_0_916, List.forall_mem_cons.2 ⟨subd5_0_917, List.forall_mem_cons.2 ⟨subd5_0_918, List.forall_mem_cons.2 ⟨subd5_0_919, List.forall_mem_cons.2 ⟨subd5_0_920, List.forall_mem_cons.2 ⟨subd5_0_921, List.forall_mem_cons.2 ⟨subd5_0_922, List.forall_mem_cons.2 ⟨subd5_0_923, List.forall_mem_cons.2 ⟨subd5_0_924, List.forall_mem_cons.2 ⟨subd5_0_925, List.forall_mem_cons.2 ⟨subd5_0_926, List.forall_mem_cons.2 ⟨subd5_0_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_928 : subd5_0 [3, -1, 6] = true := by decide +kernel
theorem subd5_0_929 : subd5_0 [3, -1, 7] = true := by decide +kernel
theorem subd5_0_930 : subd5_0 [3, -1, 8] = true := by decide +kernel
theorem subd5_0_931 : subd5_0 [3, -1, 9] = true := by decide +kernel
theorem subd5_0_932 : subd5_0 [3, 0, -7] = true := by decide +kernel
theorem subd5_0_933 : subd5_0 [3, 0, -6] = true := by decide +kernel
theorem subd5_0_934 : subd5_0 [3, 0, -5] = true := by decide +kernel
theorem subd5_0_935 : subd5_0 [3, 0, -4] = true := by decide +kernel
theorem subd5_0_936 : subd5_0 [3, 0, -3] = true := by decide +kernel
theorem subd5_0_937 : subd5_0 [3, 0, -2] = true := by decide +kernel
theorem subd5_0_938 : subd5_0 [3, 0, -1] = true := by decide +kernel
theorem subd5_0_939 : subd5_0 [3, 0, 0] = true := by decide +kernel
theorem subd5_0_940 : subd5_0 [3, 0, 1] = true := by decide +kernel
theorem subd5_0_941 : subd5_0 [3, 0, 2] = true := by decide +kernel
theorem subd5_0_942 : subd5_0 [3, 0, 3] = true := by decide +kernel
theorem subd5_0_943 : subd5_0 [3, 0, 4] = true := by decide +kernel
theorem subd5_0_944 : subd5_0 [3, 0, 5] = true := by decide +kernel
theorem subd5_0_945 : subd5_0 [3, 0, 6] = true := by decide +kernel
theorem subd5_0_946 : subd5_0 [3, 0, 7] = true := by decide +kernel
theorem subd5_0_947 : subd5_0 [3, 0, 8] = true := by decide +kernel
theorem subd5_0_948 : subd5_0 [3, 0, 9] = true := by decide +kernel
theorem subd5_0_949 : subd5_0 [3, 1, -7] = true := by decide +kernel
theorem subd5_0_950 : subd5_0 [3, 1, -6] = true := by decide +kernel
theorem subd5_0_951 : subd5_0 [3, 1, -5] = true := by decide +kernel
theorem subd5_0_952 : subd5_0 [3, 1, -4] = true := by decide +kernel
theorem subd5_0_953 : subd5_0 [3, 1, -3] = true := by decide +kernel
theorem subd5_0_954 : subd5_0 [3, 1, -2] = true := by decide +kernel
theorem subd5_0_955 : subd5_0 [3, 1, -1] = true := by decide +kernel
theorem subd5_0_956 : subd5_0 [3, 1, 0] = true := by decide +kernel
theorem subd5_0_957 : subd5_0 [3, 1, 1] = true := by decide +kernel
theorem subd5_0_958 : subd5_0 [3, 1, 2] = true := by decide +kernel
theorem subd5_0_959 : subd5_0 [3, 1, 3] = true := by decide +kernel
theorem sbd5_0_29 : ∀ q ∈ blkd5_0_29, subd5_0 q = true := by
  unfold blkd5_0_29
  exact List.forall_mem_cons.2 ⟨subd5_0_928, List.forall_mem_cons.2 ⟨subd5_0_929, List.forall_mem_cons.2 ⟨subd5_0_930, List.forall_mem_cons.2 ⟨subd5_0_931, List.forall_mem_cons.2 ⟨subd5_0_932, List.forall_mem_cons.2 ⟨subd5_0_933, List.forall_mem_cons.2 ⟨subd5_0_934, List.forall_mem_cons.2 ⟨subd5_0_935, List.forall_mem_cons.2 ⟨subd5_0_936, List.forall_mem_cons.2 ⟨subd5_0_937, List.forall_mem_cons.2 ⟨subd5_0_938, List.forall_mem_cons.2 ⟨subd5_0_939, List.forall_mem_cons.2 ⟨subd5_0_940, List.forall_mem_cons.2 ⟨subd5_0_941, List.forall_mem_cons.2 ⟨subd5_0_942, List.forall_mem_cons.2 ⟨subd5_0_943, List.forall_mem_cons.2 ⟨subd5_0_944, List.forall_mem_cons.2 ⟨subd5_0_945, List.forall_mem_cons.2 ⟨subd5_0_946, List.forall_mem_cons.2 ⟨subd5_0_947, List.forall_mem_cons.2 ⟨subd5_0_948, List.forall_mem_cons.2 ⟨subd5_0_949, List.forall_mem_cons.2 ⟨subd5_0_950, List.forall_mem_cons.2 ⟨subd5_0_951, List.forall_mem_cons.2 ⟨subd5_0_952, List.forall_mem_cons.2 ⟨subd5_0_953, List.forall_mem_cons.2 ⟨subd5_0_954, List.forall_mem_cons.2 ⟨subd5_0_955, List.forall_mem_cons.2 ⟨subd5_0_956, List.forall_mem_cons.2 ⟨subd5_0_957, List.forall_mem_cons.2 ⟨subd5_0_958, List.forall_mem_cons.2 ⟨subd5_0_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd5_0_960 : subd5_0 [3, 1, 4] = true := by decide +kernel
theorem subd5_0_961 : subd5_0 [3, 1, 5] = true := by decide +kernel
theorem subd5_0_962 : subd5_0 [3, 1, 6] = true := by decide +kernel
theorem subd5_0_963 : subd5_0 [3, 1, 7] = true := by decide +kernel
theorem subd5_0_964 : subd5_0 [3, 1, 8] = true := by decide +kernel
theorem subd5_0_965 : subd5_0 [3, 2, -7] = true := by decide +kernel
theorem subd5_0_966 : subd5_0 [3, 2, -6] = true := by decide +kernel
theorem subd5_0_967 : subd5_0 [3, 2, -5] = true := by decide +kernel
theorem subd5_0_968 : subd5_0 [3, 2, -4] = true := by decide +kernel
theorem subd5_0_969 : subd5_0 [3, 2, -3] = true := by decide +kernel
theorem subd5_0_970 : subd5_0 [3, 2, -2] = true := by decide +kernel
theorem subd5_0_971 : subd5_0 [3, 2, -1] = true := by decide +kernel
theorem subd5_0_972 : subd5_0 [3, 2, 0] = true := by decide +kernel
theorem subd5_0_973 : subd5_0 [3, 2, 1] = true := by decide +kernel
theorem subd5_0_974 : subd5_0 [3, 2, 2] = true := by decide +kernel
theorem subd5_0_975 : subd5_0 [3, 2, 3] = true := by decide +kernel
theorem subd5_0_976 : subd5_0 [3, 2, 4] = true := by decide +kernel
theorem subd5_0_977 : subd5_0 [3, 2, 5] = true := by decide +kernel
theorem subd5_0_978 : subd5_0 [3, 2, 6] = true := by decide +kernel
theorem subd5_0_979 : subd5_0 [3, 2, 7] = true := by decide +kernel
theorem subd5_0_980 : subd5_0 [3, 3] = true := by decide +kernel
theorem subd5_0_981 : subd5_0 [3, 4] = true := by decide +kernel
theorem subd5_0_982 : subd5_0 [4, -5] = true := by decide +kernel
theorem subd5_0_983 : subd5_0 [4, -4] = true := by decide +kernel
theorem subd5_0_984 : subd5_0 [4, -3] = true := by decide +kernel
theorem subd5_0_985 : subd5_0 [4, -2] = true := by decide +kernel
theorem subd5_0_986 : subd5_0 [4, -1, -5] = true := by decide +kernel
theorem subd5_0_987 : subd5_0 [4, -1, -4] = true := by decide +kernel
theorem subd5_0_988 : subd5_0 [4, -1, -3] = true := by decide +kernel
theorem subd5_0_989 : subd5_0 [4, -1, -2] = true := by decide +kernel
theorem subd5_0_990 : subd5_0 [4, -1, -1] = true := by decide +kernel
theorem subd5_0_991 : subd5_0 [4, -1, 0] = true := by decide +kernel
theorem sbd5_0_30 : ∀ q ∈ blkd5_0_30, subd5_0 q = true := by
  unfold blkd5_0_30
  exact List.forall_mem_cons.2 ⟨subd5_0_960, List.forall_mem_cons.2 ⟨subd5_0_961, List.forall_mem_cons.2 ⟨subd5_0_962, List.forall_mem_cons.2 ⟨subd5_0_963, List.forall_mem_cons.2 ⟨subd5_0_964, List.forall_mem_cons.2 ⟨subd5_0_965, List.forall_mem_cons.2 ⟨subd5_0_966, List.forall_mem_cons.2 ⟨subd5_0_967, List.forall_mem_cons.2 ⟨subd5_0_968, List.forall_mem_cons.2 ⟨subd5_0_969, List.forall_mem_cons.2 ⟨subd5_0_970, List.forall_mem_cons.2 ⟨subd5_0_971, List.forall_mem_cons.2 ⟨subd5_0_972, List.forall_mem_cons.2 ⟨subd5_0_973, List.forall_mem_cons.2 ⟨subd5_0_974, List.forall_mem_cons.2 ⟨subd5_0_975, List.forall_mem_cons.2 ⟨subd5_0_976, List.forall_mem_cons.2 ⟨subd5_0_977, List.forall_mem_cons.2 ⟨subd5_0_978, List.forall_mem_cons.2 ⟨subd5_0_979, List.forall_mem_cons.2 ⟨subd5_0_980, List.forall_mem_cons.2 ⟨subd5_0_981, List.forall_mem_cons.2 ⟨subd5_0_982, List.forall_mem_cons.2 ⟨subd5_0_983, List.forall_mem_cons.2 ⟨subd5_0_984, List.forall_mem_cons.2 ⟨subd5_0_985, List.forall_mem_cons.2 ⟨subd5_0_986, List.forall_mem_cons.2 ⟨subd5_0_987, List.forall_mem_cons.2 ⟨subd5_0_988, List.forall_mem_cons.2 ⟨subd5_0_989, List.forall_mem_cons.2 ⟨subd5_0_990, List.forall_mem_cons.2 ⟨subd5_0_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
