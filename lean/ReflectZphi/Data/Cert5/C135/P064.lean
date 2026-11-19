import ReflectZphi.Data.Cert5.C135.Base

namespace ReflectZphi.Data.Cert5.C135

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd10_3_512 : subd10_3 [-1, 2, 8] = true := by decide +kernel
theorem subd10_3_513 : subd10_3 [-1, 3, -9] = true := by decide +kernel
theorem subd10_3_514 : subd10_3 [-1, 3, -8] = true := by decide +kernel
theorem subd10_3_515 : subd10_3 [-1, 3, -7] = true := by decide +kernel
theorem subd10_3_516 : subd10_3 [-1, 3, -6] = true := by decide +kernel
theorem subd10_3_517 : subd10_3 [-1, 3, -5] = true := by decide +kernel
theorem subd10_3_518 : subd10_3 [-1, 3, -4] = true := by decide +kernel
theorem subd10_3_519 : subd10_3 [-1, 3, -3] = true := by decide +kernel
theorem subd10_3_520 : subd10_3 [-1, 3, -2] = true := by decide +kernel
theorem subd10_3_521 : subd10_3 [-1, 3, -1] = true := by decide +kernel
theorem subd10_3_522 : subd10_3 [-1, 3, 0] = true := by decide +kernel
theorem subd10_3_523 : subd10_3 [-1, 3, 1] = true := by decide +kernel
theorem subd10_3_524 : subd10_3 [-1, 3, 2] = true := by decide +kernel
theorem subd10_3_525 : subd10_3 [-1, 3, 3] = true := by decide +kernel
theorem subd10_3_526 : subd10_3 [-1, 3, 4] = true := by decide +kernel
theorem subd10_3_527 : subd10_3 [-1, 3, 5] = true := by decide +kernel
theorem subd10_3_528 : subd10_3 [-1, 3, 6] = true := by decide +kernel
theorem subd10_3_529 : subd10_3 [-1, 3, 7] = true := by decide +kernel
theorem subd10_3_530 : subd10_3 [-1, 4, -9] = true := by decide +kernel
theorem subd10_3_531 : subd10_3 [-1, 4, -8] = true := by decide +kernel
theorem subd10_3_532 : subd10_3 [-1, 4, -7] = true := by decide +kernel
theorem subd10_3_533 : subd10_3 [-1, 4, -6] = true := by decide +kernel
theorem subd10_3_534 : subd10_3 [-1, 4, -5] = true := by decide +kernel
theorem subd10_3_535 : subd10_3 [-1, 4, -4] = true := by decide +kernel
theorem subd10_3_536 : subd10_3 [-1, 4, -3] = true := by decide +kernel
theorem subd10_3_537 : subd10_3 [-1, 4, -2] = true := by decide +kernel
theorem subd10_3_538 : subd10_3 [-1, 4, -1] = true := by decide +kernel
theorem subd10_3_539 : subd10_3 [-1, 4, 0] = true := by decide +kernel
theorem subd10_3_540 : subd10_3 [-1, 4, 1] = true := by decide +kernel
theorem subd10_3_541 : subd10_3 [-1, 4, 2] = true := by decide +kernel
theorem subd10_3_542 : subd10_3 [-1, 4, 3] = true := by decide +kernel
theorem subd10_3_543 : subd10_3 [-1, 4, 4] = true := by decide +kernel
theorem sbd10_3_16 : ∀ q ∈ blkd10_3_16, subd10_3 q = true := by
  unfold blkd10_3_16
  exact List.forall_mem_cons.2 ⟨subd10_3_512, List.forall_mem_cons.2 ⟨subd10_3_513, List.forall_mem_cons.2 ⟨subd10_3_514, List.forall_mem_cons.2 ⟨subd10_3_515, List.forall_mem_cons.2 ⟨subd10_3_516, List.forall_mem_cons.2 ⟨subd10_3_517, List.forall_mem_cons.2 ⟨subd10_3_518, List.forall_mem_cons.2 ⟨subd10_3_519, List.forall_mem_cons.2 ⟨subd10_3_520, List.forall_mem_cons.2 ⟨subd10_3_521, List.forall_mem_cons.2 ⟨subd10_3_522, List.forall_mem_cons.2 ⟨subd10_3_523, List.forall_mem_cons.2 ⟨subd10_3_524, List.forall_mem_cons.2 ⟨subd10_3_525, List.forall_mem_cons.2 ⟨subd10_3_526, List.forall_mem_cons.2 ⟨subd10_3_527, List.forall_mem_cons.2 ⟨subd10_3_528, List.forall_mem_cons.2 ⟨subd10_3_529, List.forall_mem_cons.2 ⟨subd10_3_530, List.forall_mem_cons.2 ⟨subd10_3_531, List.forall_mem_cons.2 ⟨subd10_3_532, List.forall_mem_cons.2 ⟨subd10_3_533, List.forall_mem_cons.2 ⟨subd10_3_534, List.forall_mem_cons.2 ⟨subd10_3_535, List.forall_mem_cons.2 ⟨subd10_3_536, List.forall_mem_cons.2 ⟨subd10_3_537, List.forall_mem_cons.2 ⟨subd10_3_538, List.forall_mem_cons.2 ⟨subd10_3_539, List.forall_mem_cons.2 ⟨subd10_3_540, List.forall_mem_cons.2 ⟨subd10_3_541, List.forall_mem_cons.2 ⟨subd10_3_542, List.forall_mem_cons.2 ⟨subd10_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_544 : subd10_3 [-1, 4, 5] = true := by decide +kernel
theorem subd10_3_545 : subd10_3 [-1, 5] = true := by decide +kernel
theorem subd10_3_546 : subd10_3 [-1, 6] = true := by decide +kernel
theorem subd10_3_547 : subd10_3 [0, -7] = true := by decide +kernel
theorem subd10_3_548 : subd10_3 [0, -6] = true := by decide +kernel
theorem subd10_3_549 : subd10_3 [0, -5] = true := by decide +kernel
theorem subd10_3_550 : subd10_3 [0, -4, -7] = true := by decide +kernel
theorem subd10_3_551 : subd10_3 [0, -4, -6] = true := by decide +kernel
theorem subd10_3_552 : subd10_3 [0, -4, -5] = true := by decide +kernel
theorem subd10_3_553 : subd10_3 [0, -4, -4] = true := by decide +kernel
theorem subd10_3_554 : subd10_3 [0, -4, -3] = true := by decide +kernel
theorem subd10_3_555 : subd10_3 [0, -4, -2] = true := by decide +kernel
theorem subd10_3_556 : subd10_3 [0, -4, -1] = true := by decide +kernel
theorem subd10_3_557 : subd10_3 [0, -4, 0] = true := by decide +kernel
theorem subd10_3_558 : subd10_3 [0, -4, 1] = true := by decide +kernel
theorem subd10_3_559 : subd10_3 [0, -4, 2] = true := by decide +kernel
theorem subd10_3_560 : subd10_3 [0, -4, 3] = true := by decide +kernel
theorem subd10_3_561 : subd10_3 [0, -4, 4] = true := by decide +kernel
theorem subd10_3_562 : subd10_3 [0, -4, 5] = true := by decide +kernel
theorem subd10_3_563 : subd10_3 [0, -4, 6] = true := by decide +kernel
theorem subd10_3_564 : subd10_3 [0, -4, 7] = true := by decide +kernel
theorem subd10_3_565 : subd10_3 [0, -4, 8] = true := by decide +kernel
theorem subd10_3_566 : subd10_3 [0, -3, -8] = true := by decide +kernel
theorem subd10_3_567 : subd10_3 [0, -3, -7] = true := by decide +kernel
theorem subd10_3_568 : subd10_3 [0, -3, -6] = true := by decide +kernel
theorem subd10_3_569 : subd10_3 [0, -3, -5] = true := by decide +kernel
theorem subd10_3_570 : subd10_3 [0, -3, -4] = true := by decide +kernel
theorem subd10_3_571 : subd10_3 [0, -3, -3] = true := by decide +kernel
theorem subd10_3_572 : subd10_3 [0, -3, -2] = true := by decide +kernel
theorem subd10_3_573 : subd10_3 [0, -3, -1] = true := by decide +kernel
theorem subd10_3_574 : subd10_3 [0, -3, 0] = true := by decide +kernel
theorem subd10_3_575 : subd10_3 [0, -3, 1] = true := by decide +kernel
theorem sbd10_3_17 : ∀ q ∈ blkd10_3_17, subd10_3 q = true := by
  unfold blkd10_3_17
  exact List.forall_mem_cons.2 ⟨subd10_3_544, List.forall_mem_cons.2 ⟨subd10_3_545, List.forall_mem_cons.2 ⟨subd10_3_546, List.forall_mem_cons.2 ⟨subd10_3_547, List.forall_mem_cons.2 ⟨subd10_3_548, List.forall_mem_cons.2 ⟨subd10_3_549, List.forall_mem_cons.2 ⟨subd10_3_550, List.forall_mem_cons.2 ⟨subd10_3_551, List.forall_mem_cons.2 ⟨subd10_3_552, List.forall_mem_cons.2 ⟨subd10_3_553, List.forall_mem_cons.2 ⟨subd10_3_554, List.forall_mem_cons.2 ⟨subd10_3_555, List.forall_mem_cons.2 ⟨subd10_3_556, List.forall_mem_cons.2 ⟨subd10_3_557, List.forall_mem_cons.2 ⟨subd10_3_558, List.forall_mem_cons.2 ⟨subd10_3_559, List.forall_mem_cons.2 ⟨subd10_3_560, List.forall_mem_cons.2 ⟨subd10_3_561, List.forall_mem_cons.2 ⟨subd10_3_562, List.forall_mem_cons.2 ⟨subd10_3_563, List.forall_mem_cons.2 ⟨subd10_3_564, List.forall_mem_cons.2 ⟨subd10_3_565, List.forall_mem_cons.2 ⟨subd10_3_566, List.forall_mem_cons.2 ⟨subd10_3_567, List.forall_mem_cons.2 ⟨subd10_3_568, List.forall_mem_cons.2 ⟨subd10_3_569, List.forall_mem_cons.2 ⟨subd10_3_570, List.forall_mem_cons.2 ⟨subd10_3_571, List.forall_mem_cons.2 ⟨subd10_3_572, List.forall_mem_cons.2 ⟨subd10_3_573, List.forall_mem_cons.2 ⟨subd10_3_574, List.forall_mem_cons.2 ⟨subd10_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_576 : subd10_3 [0, -3, 2] = true := by decide +kernel
theorem subd10_3_577 : subd10_3 [0, -3, 3] = true := by decide +kernel
theorem subd10_3_578 : subd10_3 [0, -3, 4] = true := by decide +kernel
theorem subd10_3_579 : subd10_3 [0, -3, 5] = true := by decide +kernel
theorem subd10_3_580 : subd10_3 [0, -3, 6] = true := by decide +kernel
theorem subd10_3_581 : subd10_3 [0, -3, 7] = true := by decide +kernel
theorem subd10_3_582 : subd10_3 [0, -3, 8] = true := by decide +kernel
theorem subd10_3_583 : subd10_3 [0, -2, -9] = true := by decide +kernel
theorem subd10_3_584 : subd10_3 [0, -2, -8] = true := by decide +kernel
theorem subd10_3_585 : subd10_3 [0, -2, -7] = true := by decide +kernel
theorem subd10_3_586 : subd10_3 [0, -2, -6] = true := by decide +kernel
theorem subd10_3_587 : subd10_3 [0, -2, -5] = true := by decide +kernel
theorem subd10_3_588 : subd10_3 [0, -2, -4] = true := by decide +kernel
theorem subd10_3_589 : subd10_3 [0, -2, -3] = true := by decide +kernel
theorem subd10_3_590 : subd10_3 [0, -2, -2] = true := by decide +kernel
theorem subd10_3_591 : subd10_3 [0, -2, -1] = true := by decide +kernel
theorem subd10_3_592 : subd10_3 [0, -2, 0] = true := by decide +kernel
theorem subd10_3_593 : subd10_3 [0, -2, 1] = true := by decide +kernel
theorem subd10_3_594 : subd10_3 [0, -2, 2] = true := by decide +kernel
theorem subd10_3_595 : subd10_3 [0, -2, 3] = true := by decide +kernel
theorem subd10_3_596 : subd10_3 [0, -2, 4] = true := by decide +kernel
theorem subd10_3_597 : subd10_3 [0, -2, 5] = true := by decide +kernel
theorem subd10_3_598 : subd10_3 [0, -2, 6] = true := by decide +kernel
theorem subd10_3_599 : subd10_3 [0, -2, 7] = true := by decide +kernel
theorem subd10_3_600 : subd10_3 [0, -2, 8] = true := by decide +kernel
theorem subd10_3_601 : subd10_3 [0, -2, 9] = true := by decide +kernel
theorem subd10_3_602 : subd10_3 [0, -1, -9] = true := by decide +kernel
theorem subd10_3_603 : subd10_3 [0, -1, -8] = true := by decide +kernel
theorem subd10_3_604 : subd10_3 [0, -1, -7] = true := by decide +kernel
theorem subd10_3_605 : subd10_3 [0, -1, -6] = true := by decide +kernel
theorem subd10_3_606 : subd10_3 [0, -1, -5] = true := by decide +kernel
theorem subd10_3_607 : subd10_3 [0, -1, -4] = true := by decide +kernel
theorem sbd10_3_18 : ∀ q ∈ blkd10_3_18, subd10_3 q = true := by
  unfold blkd10_3_18
  exact List.forall_mem_cons.2 ⟨subd10_3_576, List.forall_mem_cons.2 ⟨subd10_3_577, List.forall_mem_cons.2 ⟨subd10_3_578, List.forall_mem_cons.2 ⟨subd10_3_579, List.forall_mem_cons.2 ⟨subd10_3_580, List.forall_mem_cons.2 ⟨subd10_3_581, List.forall_mem_cons.2 ⟨subd10_3_582, List.forall_mem_cons.2 ⟨subd10_3_583, List.forall_mem_cons.2 ⟨subd10_3_584, List.forall_mem_cons.2 ⟨subd10_3_585, List.forall_mem_cons.2 ⟨subd10_3_586, List.forall_mem_cons.2 ⟨subd10_3_587, List.forall_mem_cons.2 ⟨subd10_3_588, List.forall_mem_cons.2 ⟨subd10_3_589, List.forall_mem_cons.2 ⟨subd10_3_590, List.forall_mem_cons.2 ⟨subd10_3_591, List.forall_mem_cons.2 ⟨subd10_3_592, List.forall_mem_cons.2 ⟨subd10_3_593, List.forall_mem_cons.2 ⟨subd10_3_594, List.forall_mem_cons.2 ⟨subd10_3_595, List.forall_mem_cons.2 ⟨subd10_3_596, List.forall_mem_cons.2 ⟨subd10_3_597, List.forall_mem_cons.2 ⟨subd10_3_598, List.forall_mem_cons.2 ⟨subd10_3_599, List.forall_mem_cons.2 ⟨subd10_3_600, List.forall_mem_cons.2 ⟨subd10_3_601, List.forall_mem_cons.2 ⟨subd10_3_602, List.forall_mem_cons.2 ⟨subd10_3_603, List.forall_mem_cons.2 ⟨subd10_3_604, List.forall_mem_cons.2 ⟨subd10_3_605, List.forall_mem_cons.2 ⟨subd10_3_606, List.forall_mem_cons.2 ⟨subd10_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_608 : subd10_3 [0, -1, -3] = true := by decide +kernel
theorem subd10_3_609 : subd10_3 [0, -1, -2] = true := by decide +kernel
theorem subd10_3_610 : subd10_3 [0, -1, -1] = true := by decide +kernel
theorem subd10_3_611 : subd10_3 [0, -1, 0] = true := by decide +kernel
theorem subd10_3_612 : subd10_3 [0, -1, 1] = true := by decide +kernel
theorem subd10_3_613 : subd10_3 [0, -1, 2] = true := by decide +kernel
theorem subd10_3_614 : subd10_3 [0, -1, 3] = true := by decide +kernel
theorem subd10_3_615 : subd10_3 [0, -1, 4] = true := by decide +kernel
theorem subd10_3_616 : subd10_3 [0, -1, 5] = true := by decide +kernel
theorem subd10_3_617 : subd10_3 [0, -1, 6] = true := by decide +kernel
theorem subd10_3_618 : subd10_3 [0, -1, 7] = true := by decide +kernel
theorem subd10_3_619 : subd10_3 [0, -1, 8] = true := by decide +kernel
theorem subd10_3_620 : subd10_3 [0, -1, 9] = true := by decide +kernel
theorem subd10_3_621 : subd10_3 [0, 0, -10] = true := by decide +kernel
theorem subd10_3_622 : subd10_3 [0, 0, -9] = true := by decide +kernel
theorem subd10_3_623 : subd10_3 [0, 0, -8] = true := by decide +kernel
theorem subd10_3_624 : subd10_3 [0, 0, -7] = true := by decide +kernel
theorem subd10_3_625 : subd10_3 [0, 0, -6] = true := by decide +kernel
theorem subd10_3_626 : subd10_3 [0, 0, -5] = true := by decide +kernel
theorem subd10_3_627 : subd10_3 [0, 0, -4] = true := by decide +kernel
theorem subd10_3_628 : subd10_3 [0, 0, -3] = true := by decide +kernel
theorem subd10_3_629 : subd10_3 [0, 0, -2] = true := by decide +kernel
theorem subd10_3_630 : subd10_3 [0, 0, -1] = true := by decide +kernel
theorem subd10_3_631 : subd10_3 [0, 0, 0] = true := by decide +kernel
theorem subd10_3_632 : subd10_3 [0, 0, 1] = true := by decide +kernel
theorem subd10_3_633 : subd10_3 [0, 0, 2] = true := by decide +kernel
theorem subd10_3_634 : subd10_3 [0, 0, 3] = true := by decide +kernel
theorem subd10_3_635 : subd10_3 [0, 0, 4] = true := by decide +kernel
theorem subd10_3_636 : subd10_3 [0, 0, 5] = true := by decide +kernel
theorem subd10_3_637 : subd10_3 [0, 0, 6] = true := by decide +kernel
theorem subd10_3_638 : subd10_3 [0, 0, 7] = true := by decide +kernel
theorem subd10_3_639 : subd10_3 [0, 0, 8] = true := by decide +kernel
theorem sbd10_3_19 : ∀ q ∈ blkd10_3_19, subd10_3 q = true := by
  unfold blkd10_3_19
  exact List.forall_mem_cons.2 ⟨subd10_3_608, List.forall_mem_cons.2 ⟨subd10_3_609, List.forall_mem_cons.2 ⟨subd10_3_610, List.forall_mem_cons.2 ⟨subd10_3_611, List.forall_mem_cons.2 ⟨subd10_3_612, List.forall_mem_cons.2 ⟨subd10_3_613, List.forall_mem_cons.2 ⟨subd10_3_614, List.forall_mem_cons.2 ⟨subd10_3_615, List.forall_mem_cons.2 ⟨subd10_3_616, List.forall_mem_cons.2 ⟨subd10_3_617, List.forall_mem_cons.2 ⟨subd10_3_618, List.forall_mem_cons.2 ⟨subd10_3_619, List.forall_mem_cons.2 ⟨subd10_3_620, List.forall_mem_cons.2 ⟨subd10_3_621, List.forall_mem_cons.2 ⟨subd10_3_622, List.forall_mem_cons.2 ⟨subd10_3_623, List.forall_mem_cons.2 ⟨subd10_3_624, List.forall_mem_cons.2 ⟨subd10_3_625, List.forall_mem_cons.2 ⟨subd10_3_626, List.forall_mem_cons.2 ⟨subd10_3_627, List.forall_mem_cons.2 ⟨subd10_3_628, List.forall_mem_cons.2 ⟨subd10_3_629, List.forall_mem_cons.2 ⟨subd10_3_630, List.forall_mem_cons.2 ⟨subd10_3_631, List.forall_mem_cons.2 ⟨subd10_3_632, List.forall_mem_cons.2 ⟨subd10_3_633, List.forall_mem_cons.2 ⟨subd10_3_634, List.forall_mem_cons.2 ⟨subd10_3_635, List.forall_mem_cons.2 ⟨subd10_3_636, List.forall_mem_cons.2 ⟨subd10_3_637, List.forall_mem_cons.2 ⟨subd10_3_638, List.forall_mem_cons.2 ⟨subd10_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_640 : subd10_3 [0, 0, 9] = true := by decide +kernel
theorem subd10_3_641 : subd10_3 [0, 1, -10] = true := by decide +kernel
theorem subd10_3_642 : subd10_3 [0, 1, -9] = true := by decide +kernel
theorem subd10_3_643 : subd10_3 [0, 1, -8] = true := by decide +kernel
theorem subd10_3_644 : subd10_3 [0, 1, -7] = true := by decide +kernel
theorem subd10_3_645 : subd10_3 [0, 1, -6] = true := by decide +kernel
theorem subd10_3_646 : subd10_3 [0, 1, -5] = true := by decide +kernel
theorem subd10_3_647 : subd10_3 [0, 1, -4] = true := by decide +kernel
theorem subd10_3_648 : subd10_3 [0, 1, -3] = true := by decide +kernel
theorem subd10_3_649 : subd10_3 [0, 1, -2] = true := by decide +kernel
theorem subd10_3_650 : subd10_3 [0, 1, -1] = true := by decide +kernel
theorem subd10_3_651 : subd10_3 [0, 1, 0] = true := by decide +kernel
theorem subd10_3_652 : subd10_3 [0, 1, 1] = true := by decide +kernel
theorem subd10_3_653 : subd10_3 [0, 1, 2] = true := by decide +kernel
theorem subd10_3_654 : subd10_3 [0, 1, 3] = true := by decide +kernel
theorem subd10_3_655 : subd10_3 [0, 1, 4] = true := by decide +kernel
theorem subd10_3_656 : subd10_3 [0, 1, 5] = true := by decide +kernel
theorem subd10_3_657 : subd10_3 [0, 1, 6] = true := by decide +kernel
theorem subd10_3_658 : subd10_3 [0, 1, 7] = true := by decide +kernel
theorem subd10_3_659 : subd10_3 [0, 1, 8] = true := by decide +kernel
theorem subd10_3_660 : subd10_3 [0, 2, -10] = true := by decide +kernel
theorem subd10_3_661 : subd10_3 [0, 2, -9] = true := by decide +kernel
theorem subd10_3_662 : subd10_3 [0, 2, -8] = true := by decide +kernel
theorem subd10_3_663 : subd10_3 [0, 2, -7] = true := by decide +kernel
theorem subd10_3_664 : subd10_3 [0, 2, -6] = true := by decide +kernel
theorem subd10_3_665 : subd10_3 [0, 2, -5] = true := by decide +kernel
theorem subd10_3_666 : subd10_3 [0, 2, -4] = true := by decide +kernel
theorem subd10_3_667 : subd10_3 [0, 2, -3] = true := by decide +kernel
theorem subd10_3_668 : subd10_3 [0, 2, -2] = true := by decide +kernel
theorem subd10_3_669 : subd10_3 [0, 2, -1] = true := by decide +kernel
theorem subd10_3_670 : subd10_3 [0, 2, 0] = true := by decide +kernel
theorem subd10_3_671 : subd10_3 [0, 2, 1] = true := by decide +kernel
theorem sbd10_3_20 : ∀ q ∈ blkd10_3_20, subd10_3 q = true := by
  unfold blkd10_3_20
  exact List.forall_mem_cons.2 ⟨subd10_3_640, List.forall_mem_cons.2 ⟨subd10_3_641, List.forall_mem_cons.2 ⟨subd10_3_642, List.forall_mem_cons.2 ⟨subd10_3_643, List.forall_mem_cons.2 ⟨subd10_3_644, List.forall_mem_cons.2 ⟨subd10_3_645, List.forall_mem_cons.2 ⟨subd10_3_646, List.forall_mem_cons.2 ⟨subd10_3_647, List.forall_mem_cons.2 ⟨subd10_3_648, List.forall_mem_cons.2 ⟨subd10_3_649, List.forall_mem_cons.2 ⟨subd10_3_650, List.forall_mem_cons.2 ⟨subd10_3_651, List.forall_mem_cons.2 ⟨subd10_3_652, List.forall_mem_cons.2 ⟨subd10_3_653, List.forall_mem_cons.2 ⟨subd10_3_654, List.forall_mem_cons.2 ⟨subd10_3_655, List.forall_mem_cons.2 ⟨subd10_3_656, List.forall_mem_cons.2 ⟨subd10_3_657, List.forall_mem_cons.2 ⟨subd10_3_658, List.forall_mem_cons.2 ⟨subd10_3_659, List.forall_mem_cons.2 ⟨subd10_3_660, List.forall_mem_cons.2 ⟨subd10_3_661, List.forall_mem_cons.2 ⟨subd10_3_662, List.forall_mem_cons.2 ⟨subd10_3_663, List.forall_mem_cons.2 ⟨subd10_3_664, List.forall_mem_cons.2 ⟨subd10_3_665, List.forall_mem_cons.2 ⟨subd10_3_666, List.forall_mem_cons.2 ⟨subd10_3_667, List.forall_mem_cons.2 ⟨subd10_3_668, List.forall_mem_cons.2 ⟨subd10_3_669, List.forall_mem_cons.2 ⟨subd10_3_670, List.forall_mem_cons.2 ⟨subd10_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_672 : subd10_3 [0, 2, 2] = true := by decide +kernel
theorem subd10_3_673 : subd10_3 [0, 2, 3] = true := by decide +kernel
theorem subd10_3_674 : subd10_3 [0, 2, 4] = true := by decide +kernel
theorem subd10_3_675 : subd10_3 [0, 2, 5] = true := by decide +kernel
theorem subd10_3_676 : subd10_3 [0, 2, 6] = true := by decide +kernel
theorem subd10_3_677 : subd10_3 [0, 2, 7] = true := by decide +kernel
theorem subd10_3_678 : subd10_3 [0, 2, 8] = true := by decide +kernel
theorem subd10_3_679 : subd10_3 [0, 3, -9] = true := by decide +kernel
theorem subd10_3_680 : subd10_3 [0, 3, -8] = true := by decide +kernel
theorem subd10_3_681 : subd10_3 [0, 3, -7] = true := by decide +kernel
theorem subd10_3_682 : subd10_3 [0, 3, -6] = true := by decide +kernel
theorem subd10_3_683 : subd10_3 [0, 3, -5] = true := by decide +kernel
theorem subd10_3_684 : subd10_3 [0, 3, -4] = true := by decide +kernel
theorem subd10_3_685 : subd10_3 [0, 3, -3] = true := by decide +kernel
theorem subd10_3_686 : subd10_3 [0, 3, -2] = true := by decide +kernel
theorem subd10_3_687 : subd10_3 [0, 3, -1] = true := by decide +kernel
theorem subd10_3_688 : subd10_3 [0, 3, 0] = true := by decide +kernel
theorem subd10_3_689 : subd10_3 [0, 3, 1] = true := by decide +kernel
theorem subd10_3_690 : subd10_3 [0, 3, 2] = true := by decide +kernel
theorem subd10_3_691 : subd10_3 [0, 3, 3] = true := by decide +kernel
theorem subd10_3_692 : subd10_3 [0, 3, 4] = true := by decide +kernel
theorem subd10_3_693 : subd10_3 [0, 3, 5] = true := by decide +kernel
theorem subd10_3_694 : subd10_3 [0, 3, 6] = true := by decide +kernel
theorem subd10_3_695 : subd10_3 [0, 3, 7] = true := by decide +kernel
theorem subd10_3_696 : subd10_3 [0, 4, -9] = true := by decide +kernel
theorem subd10_3_697 : subd10_3 [0, 4, -8] = true := by decide +kernel
theorem subd10_3_698 : subd10_3 [0, 4, -7] = true := by decide +kernel
theorem subd10_3_699 : subd10_3 [0, 4, -6] = true := by decide +kernel
theorem subd10_3_700 : subd10_3 [0, 4, -5] = true := by decide +kernel
theorem subd10_3_701 : subd10_3 [0, 4, -4] = true := by decide +kernel
theorem subd10_3_702 : subd10_3 [0, 4, -3] = true := by decide +kernel
theorem subd10_3_703 : subd10_3 [0, 4, -2] = true := by decide +kernel
theorem sbd10_3_21 : ∀ q ∈ blkd10_3_21, subd10_3 q = true := by
  unfold blkd10_3_21
  exact List.forall_mem_cons.2 ⟨subd10_3_672, List.forall_mem_cons.2 ⟨subd10_3_673, List.forall_mem_cons.2 ⟨subd10_3_674, List.forall_mem_cons.2 ⟨subd10_3_675, List.forall_mem_cons.2 ⟨subd10_3_676, List.forall_mem_cons.2 ⟨subd10_3_677, List.forall_mem_cons.2 ⟨subd10_3_678, List.forall_mem_cons.2 ⟨subd10_3_679, List.forall_mem_cons.2 ⟨subd10_3_680, List.forall_mem_cons.2 ⟨subd10_3_681, List.forall_mem_cons.2 ⟨subd10_3_682, List.forall_mem_cons.2 ⟨subd10_3_683, List.forall_mem_cons.2 ⟨subd10_3_684, List.forall_mem_cons.2 ⟨subd10_3_685, List.forall_mem_cons.2 ⟨subd10_3_686, List.forall_mem_cons.2 ⟨subd10_3_687, List.forall_mem_cons.2 ⟨subd10_3_688, List.forall_mem_cons.2 ⟨subd10_3_689, List.forall_mem_cons.2 ⟨subd10_3_690, List.forall_mem_cons.2 ⟨subd10_3_691, List.forall_mem_cons.2 ⟨subd10_3_692, List.forall_mem_cons.2 ⟨subd10_3_693, List.forall_mem_cons.2 ⟨subd10_3_694, List.forall_mem_cons.2 ⟨subd10_3_695, List.forall_mem_cons.2 ⟨subd10_3_696, List.forall_mem_cons.2 ⟨subd10_3_697, List.forall_mem_cons.2 ⟨subd10_3_698, List.forall_mem_cons.2 ⟨subd10_3_699, List.forall_mem_cons.2 ⟨subd10_3_700, List.forall_mem_cons.2 ⟨subd10_3_701, List.forall_mem_cons.2 ⟨subd10_3_702, List.forall_mem_cons.2 ⟨subd10_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_704 : subd10_3 [0, 4, -1] = true := by decide +kernel
theorem subd10_3_705 : subd10_3 [0, 4, 0] = true := by decide +kernel
theorem subd10_3_706 : subd10_3 [0, 4, 1] = true := by decide +kernel
theorem subd10_3_707 : subd10_3 [0, 4, 2] = true := by decide +kernel
theorem subd10_3_708 : subd10_3 [0, 4, 3] = true := by decide +kernel
theorem subd10_3_709 : subd10_3 [0, 4, 4] = true := by decide +kernel
theorem subd10_3_710 : subd10_3 [0, 4, 5] = true := by decide +kernel
theorem subd10_3_711 : subd10_3 [0, 4, 6] = true := by decide +kernel
theorem subd10_3_712 : subd10_3 [0, 5] = true := by decide +kernel
theorem subd10_3_713 : subd10_3 [0, 6] = true := by decide +kernel
theorem subd10_3_714 : subd10_3 [1, -7] = true := by decide +kernel
theorem subd10_3_715 : subd10_3 [1, -6] = true := by decide +kernel
theorem subd10_3_716 : subd10_3 [1, -5] = true := by decide +kernel
theorem subd10_3_717 : subd10_3 [1, -4, -6] = true := by decide +kernel
theorem subd10_3_718 : subd10_3 [1, -4, -5] = true := by decide +kernel
theorem subd10_3_719 : subd10_3 [1, -4, -4] = true := by decide +kernel
theorem subd10_3_720 : subd10_3 [1, -4, -3] = true := by decide +kernel
theorem subd10_3_721 : subd10_3 [1, -4, -2] = true := by decide +kernel
theorem subd10_3_722 : subd10_3 [1, -4, -1] = true := by decide +kernel
theorem subd10_3_723 : subd10_3 [1, -4, 0] = true := by decide +kernel
theorem subd10_3_724 : subd10_3 [1, -4, 1] = true := by decide +kernel
theorem subd10_3_725 : subd10_3 [1, -4, 2] = true := by decide +kernel
theorem subd10_3_726 : subd10_3 [1, -4, 3] = true := by decide +kernel
theorem subd10_3_727 : subd10_3 [1, -4, 4] = true := by decide +kernel
theorem subd10_3_728 : subd10_3 [1, -4, 5] = true := by decide +kernel
theorem subd10_3_729 : subd10_3 [1, -4, 6] = true := by decide +kernel
theorem subd10_3_730 : subd10_3 [1, -4, 7] = true := by decide +kernel
theorem subd10_3_731 : subd10_3 [1, -4, 8] = true := by decide +kernel
theorem subd10_3_732 : subd10_3 [1, -3, -8] = true := by decide +kernel
theorem subd10_3_733 : subd10_3 [1, -3, -7] = true := by decide +kernel
theorem subd10_3_734 : subd10_3 [1, -3, -6] = true := by decide +kernel
theorem subd10_3_735 : subd10_3 [1, -3, -5] = true := by decide +kernel
theorem sbd10_3_22 : ∀ q ∈ blkd10_3_22, subd10_3 q = true := by
  unfold blkd10_3_22
  exact List.forall_mem_cons.2 ⟨subd10_3_704, List.forall_mem_cons.2 ⟨subd10_3_705, List.forall_mem_cons.2 ⟨subd10_3_706, List.forall_mem_cons.2 ⟨subd10_3_707, List.forall_mem_cons.2 ⟨subd10_3_708, List.forall_mem_cons.2 ⟨subd10_3_709, List.forall_mem_cons.2 ⟨subd10_3_710, List.forall_mem_cons.2 ⟨subd10_3_711, List.forall_mem_cons.2 ⟨subd10_3_712, List.forall_mem_cons.2 ⟨subd10_3_713, List.forall_mem_cons.2 ⟨subd10_3_714, List.forall_mem_cons.2 ⟨subd10_3_715, List.forall_mem_cons.2 ⟨subd10_3_716, List.forall_mem_cons.2 ⟨subd10_3_717, List.forall_mem_cons.2 ⟨subd10_3_718, List.forall_mem_cons.2 ⟨subd10_3_719, List.forall_mem_cons.2 ⟨subd10_3_720, List.forall_mem_cons.2 ⟨subd10_3_721, List.forall_mem_cons.2 ⟨subd10_3_722, List.forall_mem_cons.2 ⟨subd10_3_723, List.forall_mem_cons.2 ⟨subd10_3_724, List.forall_mem_cons.2 ⟨subd10_3_725, List.forall_mem_cons.2 ⟨subd10_3_726, List.forall_mem_cons.2 ⟨subd10_3_727, List.forall_mem_cons.2 ⟨subd10_3_728, List.forall_mem_cons.2 ⟨subd10_3_729, List.forall_mem_cons.2 ⟨subd10_3_730, List.forall_mem_cons.2 ⟨subd10_3_731, List.forall_mem_cons.2 ⟨subd10_3_732, List.forall_mem_cons.2 ⟨subd10_3_733, List.forall_mem_cons.2 ⟨subd10_3_734, List.forall_mem_cons.2 ⟨subd10_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_736 : subd10_3 [1, -3, -4] = true := by decide +kernel
theorem subd10_3_737 : subd10_3 [1, -3, -3] = true := by decide +kernel
theorem subd10_3_738 : subd10_3 [1, -3, -2] = true := by decide +kernel
theorem subd10_3_739 : subd10_3 [1, -3, -1] = true := by decide +kernel
theorem subd10_3_740 : subd10_3 [1, -3, 0] = true := by decide +kernel
theorem subd10_3_741 : subd10_3 [1, -3, 1] = true := by decide +kernel
theorem subd10_3_742 : subd10_3 [1, -3, 2] = true := by decide +kernel
theorem subd10_3_743 : subd10_3 [1, -3, 3] = true := by decide +kernel
theorem subd10_3_744 : subd10_3 [1, -3, 4] = true := by decide +kernel
theorem subd10_3_745 : subd10_3 [1, -3, 5] = true := by decide +kernel
theorem subd10_3_746 : subd10_3 [1, -3, 6] = true := by decide +kernel
theorem subd10_3_747 : subd10_3 [1, -3, 7] = true := by decide +kernel
theorem subd10_3_748 : subd10_3 [1, -3, 8] = true := by decide +kernel
theorem subd10_3_749 : subd10_3 [1, -2, -9] = true := by decide +kernel
theorem subd10_3_750 : subd10_3 [1, -2, -8] = true := by decide +kernel
theorem subd10_3_751 : subd10_3 [1, -2, -7] = true := by decide +kernel
theorem subd10_3_752 : subd10_3 [1, -2, -6] = true := by decide +kernel
theorem subd10_3_753 : subd10_3 [1, -2, -5] = true := by decide +kernel
theorem subd10_3_754 : subd10_3 [1, -2, -4] = true := by decide +kernel
theorem subd10_3_755 : subd10_3 [1, -2, -3] = true := by decide +kernel
theorem subd10_3_756 : subd10_3 [1, -2, -2] = true := by decide +kernel
theorem subd10_3_757 : subd10_3 [1, -2, -1] = true := by decide +kernel
theorem subd10_3_758 : subd10_3 [1, -2, 0] = true := by decide +kernel
theorem subd10_3_759 : subd10_3 [1, -2, 1] = true := by decide +kernel
theorem subd10_3_760 : subd10_3 [1, -2, 2] = true := by decide +kernel
theorem subd10_3_761 : subd10_3 [1, -2, 3] = true := by decide +kernel
theorem subd10_3_762 : subd10_3 [1, -2, 4] = true := by decide +kernel
theorem subd10_3_763 : subd10_3 [1, -2, 5] = true := by decide +kernel
theorem subd10_3_764 : subd10_3 [1, -2, 6] = true := by decide +kernel
theorem subd10_3_765 : subd10_3 [1, -2, 7] = true := by decide +kernel
theorem subd10_3_766 : subd10_3 [1, -2, 8] = true := by decide +kernel
theorem subd10_3_767 : subd10_3 [1, -2, 9] = true := by decide +kernel
theorem sbd10_3_23 : ∀ q ∈ blkd10_3_23, subd10_3 q = true := by
  unfold blkd10_3_23
  exact List.forall_mem_cons.2 ⟨subd10_3_736, List.forall_mem_cons.2 ⟨subd10_3_737, List.forall_mem_cons.2 ⟨subd10_3_738, List.forall_mem_cons.2 ⟨subd10_3_739, List.forall_mem_cons.2 ⟨subd10_3_740, List.forall_mem_cons.2 ⟨subd10_3_741, List.forall_mem_cons.2 ⟨subd10_3_742, List.forall_mem_cons.2 ⟨subd10_3_743, List.forall_mem_cons.2 ⟨subd10_3_744, List.forall_mem_cons.2 ⟨subd10_3_745, List.forall_mem_cons.2 ⟨subd10_3_746, List.forall_mem_cons.2 ⟨subd10_3_747, List.forall_mem_cons.2 ⟨subd10_3_748, List.forall_mem_cons.2 ⟨subd10_3_749, List.forall_mem_cons.2 ⟨subd10_3_750, List.forall_mem_cons.2 ⟨subd10_3_751, List.forall_mem_cons.2 ⟨subd10_3_752, List.forall_mem_cons.2 ⟨subd10_3_753, List.forall_mem_cons.2 ⟨subd10_3_754, List.forall_mem_cons.2 ⟨subd10_3_755, List.forall_mem_cons.2 ⟨subd10_3_756, List.forall_mem_cons.2 ⟨subd10_3_757, List.forall_mem_cons.2 ⟨subd10_3_758, List.forall_mem_cons.2 ⟨subd10_3_759, List.forall_mem_cons.2 ⟨subd10_3_760, List.forall_mem_cons.2 ⟨subd10_3_761, List.forall_mem_cons.2 ⟨subd10_3_762, List.forall_mem_cons.2 ⟨subd10_3_763, List.forall_mem_cons.2 ⟨subd10_3_764, List.forall_mem_cons.2 ⟨subd10_3_765, List.forall_mem_cons.2 ⟨subd10_3_766, List.forall_mem_cons.2 ⟨subd10_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_768 : subd10_3 [1, -1, -9] = true := by decide +kernel
theorem subd10_3_769 : subd10_3 [1, -1, -8] = true := by decide +kernel
theorem subd10_3_770 : subd10_3 [1, -1, -7] = true := by decide +kernel
theorem subd10_3_771 : subd10_3 [1, -1, -6] = true := by decide +kernel
theorem subd10_3_772 : subd10_3 [1, -1, -5] = true := by decide +kernel
theorem subd10_3_773 : subd10_3 [1, -1, -4] = true := by decide +kernel
theorem subd10_3_774 : subd10_3 [1, -1, -3] = true := by decide +kernel
theorem subd10_3_775 : subd10_3 [1, -1, -2] = true := by decide +kernel
theorem subd10_3_776 : subd10_3 [1, -1, -1] = true := by decide +kernel
theorem subd10_3_777 : subd10_3 [1, -1, 0] = true := by decide +kernel
theorem subd10_3_778 : subd10_3 [1, -1, 1] = true := by decide +kernel
theorem subd10_3_779 : subd10_3 [1, -1, 2] = true := by decide +kernel
theorem subd10_3_780 : subd10_3 [1, -1, 3] = true := by decide +kernel
theorem subd10_3_781 : subd10_3 [1, -1, 4] = true := by decide +kernel
theorem subd10_3_782 : subd10_3 [1, -1, 5] = true := by decide +kernel
theorem subd10_3_783 : subd10_3 [1, -1, 6] = true := by decide +kernel
theorem subd10_3_784 : subd10_3 [1, -1, 7] = true := by decide +kernel
theorem subd10_3_785 : subd10_3 [1, -1, 8] = true := by decide +kernel
theorem subd10_3_786 : subd10_3 [1, -1, 9] = true := by decide +kernel
theorem subd10_3_787 : subd10_3 [1, 0, -9] = true := by decide +kernel
theorem subd10_3_788 : subd10_3 [1, 0, -8] = true := by decide +kernel
theorem subd10_3_789 : subd10_3 [1, 0, -7] = true := by decide +kernel
theorem subd10_3_790 : subd10_3 [1, 0, -6] = true := by decide +kernel
theorem subd10_3_791 : subd10_3 [1, 0, -5] = true := by decide +kernel
theorem subd10_3_792 : subd10_3 [1, 0, -4] = true := by decide +kernel
theorem subd10_3_793 : subd10_3 [1, 0, -3] = true := by decide +kernel
theorem subd10_3_794 : subd10_3 [1, 0, -2] = true := by decide +kernel
theorem subd10_3_795 : subd10_3 [1, 0, -1] = true := by decide +kernel
theorem subd10_3_796 : subd10_3 [1, 0, 0] = true := by decide +kernel
theorem subd10_3_797 : subd10_3 [1, 0, 1] = true := by decide +kernel
theorem subd10_3_798 : subd10_3 [1, 0, 2] = true := by decide +kernel
theorem subd10_3_799 : subd10_3 [1, 0, 3] = true := by decide +kernel
theorem sbd10_3_24 : ∀ q ∈ blkd10_3_24, subd10_3 q = true := by
  unfold blkd10_3_24
  exact List.forall_mem_cons.2 ⟨subd10_3_768, List.forall_mem_cons.2 ⟨subd10_3_769, List.forall_mem_cons.2 ⟨subd10_3_770, List.forall_mem_cons.2 ⟨subd10_3_771, List.forall_mem_cons.2 ⟨subd10_3_772, List.forall_mem_cons.2 ⟨subd10_3_773, List.forall_mem_cons.2 ⟨subd10_3_774, List.forall_mem_cons.2 ⟨subd10_3_775, List.forall_mem_cons.2 ⟨subd10_3_776, List.forall_mem_cons.2 ⟨subd10_3_777, List.forall_mem_cons.2 ⟨subd10_3_778, List.forall_mem_cons.2 ⟨subd10_3_779, List.forall_mem_cons.2 ⟨subd10_3_780, List.forall_mem_cons.2 ⟨subd10_3_781, List.forall_mem_cons.2 ⟨subd10_3_782, List.forall_mem_cons.2 ⟨subd10_3_783, List.forall_mem_cons.2 ⟨subd10_3_784, List.forall_mem_cons.2 ⟨subd10_3_785, List.forall_mem_cons.2 ⟨subd10_3_786, List.forall_mem_cons.2 ⟨subd10_3_787, List.forall_mem_cons.2 ⟨subd10_3_788, List.forall_mem_cons.2 ⟨subd10_3_789, List.forall_mem_cons.2 ⟨subd10_3_790, List.forall_mem_cons.2 ⟨subd10_3_791, List.forall_mem_cons.2 ⟨subd10_3_792, List.forall_mem_cons.2 ⟨subd10_3_793, List.forall_mem_cons.2 ⟨subd10_3_794, List.forall_mem_cons.2 ⟨subd10_3_795, List.forall_mem_cons.2 ⟨subd10_3_796, List.forall_mem_cons.2 ⟨subd10_3_797, List.forall_mem_cons.2 ⟨subd10_3_798, List.forall_mem_cons.2 ⟨subd10_3_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_800 : subd10_3 [1, 0, 4] = true := by decide +kernel
theorem subd10_3_801 : subd10_3 [1, 0, 5] = true := by decide +kernel
theorem subd10_3_802 : subd10_3 [1, 0, 6] = true := by decide +kernel
theorem subd10_3_803 : subd10_3 [1, 0, 7] = true := by decide +kernel
theorem subd10_3_804 : subd10_3 [1, 0, 8] = true := by decide +kernel
theorem subd10_3_805 : subd10_3 [1, 1, -10] = true := by decide +kernel
theorem subd10_3_806 : subd10_3 [1, 1, -9] = true := by decide +kernel
theorem subd10_3_807 : subd10_3 [1, 1, -8] = true := by decide +kernel
theorem subd10_3_808 : subd10_3 [1, 1, -7] = true := by decide +kernel
theorem subd10_3_809 : subd10_3 [1, 1, -6] = true := by decide +kernel
theorem subd10_3_810 : subd10_3 [1, 1, -5] = true := by decide +kernel
theorem subd10_3_811 : subd10_3 [1, 1, -4] = true := by decide +kernel
theorem subd10_3_812 : subd10_3 [1, 1, -3] = true := by decide +kernel
theorem subd10_3_813 : subd10_3 [1, 1, -2] = true := by decide +kernel
theorem subd10_3_814 : subd10_3 [1, 1, -1] = true := by decide +kernel
theorem subd10_3_815 : subd10_3 [1, 1, 0] = true := by decide +kernel
theorem subd10_3_816 : subd10_3 [1, 1, 1] = true := by decide +kernel
theorem subd10_3_817 : subd10_3 [1, 1, 2] = true := by decide +kernel
theorem subd10_3_818 : subd10_3 [1, 1, 3] = true := by decide +kernel
theorem subd10_3_819 : subd10_3 [1, 1, 4] = true := by decide +kernel
theorem subd10_3_820 : subd10_3 [1, 1, 5] = true := by decide +kernel
theorem subd10_3_821 : subd10_3 [1, 1, 6] = true := by decide +kernel
theorem subd10_3_822 : subd10_3 [1, 1, 7] = true := by decide +kernel
theorem subd10_3_823 : subd10_3 [1, 1, 8] = true := by decide +kernel
theorem subd10_3_824 : subd10_3 [1, 2, -10] = true := by decide +kernel
theorem subd10_3_825 : subd10_3 [1, 2, -9] = true := by decide +kernel
theorem subd10_3_826 : subd10_3 [1, 2, -8] = true := by decide +kernel
theorem subd10_3_827 : subd10_3 [1, 2, -7] = true := by decide +kernel
theorem subd10_3_828 : subd10_3 [1, 2, -6] = true := by decide +kernel
theorem subd10_3_829 : subd10_3 [1, 2, -5] = true := by decide +kernel
theorem subd10_3_830 : subd10_3 [1, 2, -4] = true := by decide +kernel
theorem subd10_3_831 : subd10_3 [1, 2, -3] = true := by decide +kernel
theorem sbd10_3_25 : ∀ q ∈ blkd10_3_25, subd10_3 q = true := by
  unfold blkd10_3_25
  exact List.forall_mem_cons.2 ⟨subd10_3_800, List.forall_mem_cons.2 ⟨subd10_3_801, List.forall_mem_cons.2 ⟨subd10_3_802, List.forall_mem_cons.2 ⟨subd10_3_803, List.forall_mem_cons.2 ⟨subd10_3_804, List.forall_mem_cons.2 ⟨subd10_3_805, List.forall_mem_cons.2 ⟨subd10_3_806, List.forall_mem_cons.2 ⟨subd10_3_807, List.forall_mem_cons.2 ⟨subd10_3_808, List.forall_mem_cons.2 ⟨subd10_3_809, List.forall_mem_cons.2 ⟨subd10_3_810, List.forall_mem_cons.2 ⟨subd10_3_811, List.forall_mem_cons.2 ⟨subd10_3_812, List.forall_mem_cons.2 ⟨subd10_3_813, List.forall_mem_cons.2 ⟨subd10_3_814, List.forall_mem_cons.2 ⟨subd10_3_815, List.forall_mem_cons.2 ⟨subd10_3_816, List.forall_mem_cons.2 ⟨subd10_3_817, List.forall_mem_cons.2 ⟨subd10_3_818, List.forall_mem_cons.2 ⟨subd10_3_819, List.forall_mem_cons.2 ⟨subd10_3_820, List.forall_mem_cons.2 ⟨subd10_3_821, List.forall_mem_cons.2 ⟨subd10_3_822, List.forall_mem_cons.2 ⟨subd10_3_823, List.forall_mem_cons.2 ⟨subd10_3_824, List.forall_mem_cons.2 ⟨subd10_3_825, List.forall_mem_cons.2 ⟨subd10_3_826, List.forall_mem_cons.2 ⟨subd10_3_827, List.forall_mem_cons.2 ⟨subd10_3_828, List.forall_mem_cons.2 ⟨subd10_3_829, List.forall_mem_cons.2 ⟨subd10_3_830, List.forall_mem_cons.2 ⟨subd10_3_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_832 : subd10_3 [1, 2, -2] = true := by decide +kernel
theorem subd10_3_833 : subd10_3 [1, 2, -1] = true := by decide +kernel
theorem subd10_3_834 : subd10_3 [1, 2, 0] = true := by decide +kernel
theorem subd10_3_835 : subd10_3 [1, 2, 1] = true := by decide +kernel
theorem subd10_3_836 : subd10_3 [1, 2, 2] = true := by decide +kernel
theorem subd10_3_837 : subd10_3 [1, 2, 3] = true := by decide +kernel
theorem subd10_3_838 : subd10_3 [1, 2, 4] = true := by decide +kernel
theorem subd10_3_839 : subd10_3 [1, 2, 5] = true := by decide +kernel
theorem subd10_3_840 : subd10_3 [1, 2, 6] = true := by decide +kernel
theorem subd10_3_841 : subd10_3 [1, 2, 7] = true := by decide +kernel
theorem subd10_3_842 : subd10_3 [1, 3, -9] = true := by decide +kernel
theorem subd10_3_843 : subd10_3 [1, 3, -8] = true := by decide +kernel
theorem subd10_3_844 : subd10_3 [1, 3, -7] = true := by decide +kernel
theorem subd10_3_845 : subd10_3 [1, 3, -6] = true := by decide +kernel
theorem subd10_3_846 : subd10_3 [1, 3, -5] = true := by decide +kernel
theorem subd10_3_847 : subd10_3 [1, 3, -4] = true := by decide +kernel
theorem subd10_3_848 : subd10_3 [1, 3, -3] = true := by decide +kernel
theorem subd10_3_849 : subd10_3 [1, 3, -2] = true := by decide +kernel
theorem subd10_3_850 : subd10_3 [1, 3, -1] = true := by decide +kernel
theorem subd10_3_851 : subd10_3 [1, 3, 0] = true := by decide +kernel
theorem subd10_3_852 : subd10_3 [1, 3, 1] = true := by decide +kernel
theorem subd10_3_853 : subd10_3 [1, 3, 2] = true := by decide +kernel
theorem subd10_3_854 : subd10_3 [1, 3, 3] = true := by decide +kernel
theorem subd10_3_855 : subd10_3 [1, 3, 4] = true := by decide +kernel
theorem subd10_3_856 : subd10_3 [1, 3, 5] = true := by decide +kernel
theorem subd10_3_857 : subd10_3 [1, 3, 6] = true := by decide +kernel
theorem subd10_3_858 : subd10_3 [1, 3, 7] = true := by decide +kernel
theorem subd10_3_859 : subd10_3 [1, 4, -9] = true := by decide +kernel
theorem subd10_3_860 : subd10_3 [1, 4, -8] = true := by decide +kernel
theorem subd10_3_861 : subd10_3 [1, 4, -7] = true := by decide +kernel
theorem subd10_3_862 : subd10_3 [1, 4, -6] = true := by decide +kernel
theorem subd10_3_863 : subd10_3 [1, 4, -5] = true := by decide +kernel
theorem sbd10_3_26 : ∀ q ∈ blkd10_3_26, subd10_3 q = true := by
  unfold blkd10_3_26
  exact List.forall_mem_cons.2 ⟨subd10_3_832, List.forall_mem_cons.2 ⟨subd10_3_833, List.forall_mem_cons.2 ⟨subd10_3_834, List.forall_mem_cons.2 ⟨subd10_3_835, List.forall_mem_cons.2 ⟨subd10_3_836, List.forall_mem_cons.2 ⟨subd10_3_837, List.forall_mem_cons.2 ⟨subd10_3_838, List.forall_mem_cons.2 ⟨subd10_3_839, List.forall_mem_cons.2 ⟨subd10_3_840, List.forall_mem_cons.2 ⟨subd10_3_841, List.forall_mem_cons.2 ⟨subd10_3_842, List.forall_mem_cons.2 ⟨subd10_3_843, List.forall_mem_cons.2 ⟨subd10_3_844, List.forall_mem_cons.2 ⟨subd10_3_845, List.forall_mem_cons.2 ⟨subd10_3_846, List.forall_mem_cons.2 ⟨subd10_3_847, List.forall_mem_cons.2 ⟨subd10_3_848, List.forall_mem_cons.2 ⟨subd10_3_849, List.forall_mem_cons.2 ⟨subd10_3_850, List.forall_mem_cons.2 ⟨subd10_3_851, List.forall_mem_cons.2 ⟨subd10_3_852, List.forall_mem_cons.2 ⟨subd10_3_853, List.forall_mem_cons.2 ⟨subd10_3_854, List.forall_mem_cons.2 ⟨subd10_3_855, List.forall_mem_cons.2 ⟨subd10_3_856, List.forall_mem_cons.2 ⟨subd10_3_857, List.forall_mem_cons.2 ⟨subd10_3_858, List.forall_mem_cons.2 ⟨subd10_3_859, List.forall_mem_cons.2 ⟨subd10_3_860, List.forall_mem_cons.2 ⟨subd10_3_861, List.forall_mem_cons.2 ⟨subd10_3_862, List.forall_mem_cons.2 ⟨subd10_3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_864 : subd10_3 [1, 4, -4] = true := by decide +kernel
theorem subd10_3_865 : subd10_3 [1, 4, -3] = true := by decide +kernel
theorem subd10_3_866 : subd10_3 [1, 4, -2] = true := by decide +kernel
theorem subd10_3_867 : subd10_3 [1, 4, -1] = true := by decide +kernel
theorem subd10_3_868 : subd10_3 [1, 4, 0] = true := by decide +kernel
theorem subd10_3_869 : subd10_3 [1, 4, 1] = true := by decide +kernel
theorem subd10_3_870 : subd10_3 [1, 4, 2] = true := by decide +kernel
theorem subd10_3_871 : subd10_3 [1, 4, 3] = true := by decide +kernel
theorem subd10_3_872 : subd10_3 [1, 4, 4] = true := by decide +kernel
theorem subd10_3_873 : subd10_3 [1, 4, 5] = true := by decide +kernel
theorem subd10_3_874 : subd10_3 [1, 5] = true := by decide +kernel
theorem subd10_3_875 : subd10_3 [1, 6] = true := by decide +kernel
theorem subd10_3_876 : subd10_3 [2, -7] = true := by decide +kernel
theorem subd10_3_877 : subd10_3 [2, -6] = true := by decide +kernel
theorem subd10_3_878 : subd10_3 [2, -5] = true := by decide +kernel
theorem subd10_3_879 : subd10_3 [2, -4, -6] = true := by decide +kernel
theorem subd10_3_880 : subd10_3 [2, -4, -5] = true := by decide +kernel
theorem subd10_3_881 : subd10_3 [2, -4, -4] = true := by decide +kernel
theorem subd10_3_882 : subd10_3 [2, -4, -3] = true := by decide +kernel
theorem subd10_3_883 : subd10_3 [2, -4, -2] = true := by decide +kernel
theorem subd10_3_884 : subd10_3 [2, -4, -1] = true := by decide +kernel
theorem subd10_3_885 : subd10_3 [2, -4, 0] = true := by decide +kernel
theorem subd10_3_886 : subd10_3 [2, -4, 1] = true := by decide +kernel
theorem subd10_3_887 : subd10_3 [2, -4, 2] = true := by decide +kernel
theorem subd10_3_888 : subd10_3 [2, -4, 3] = true := by decide +kernel
theorem subd10_3_889 : subd10_3 [2, -4, 4] = true := by decide +kernel
theorem subd10_3_890 : subd10_3 [2, -4, 5] = true := by decide +kernel
theorem subd10_3_891 : subd10_3 [2, -4, 6] = true := by decide +kernel
theorem subd10_3_892 : subd10_3 [2, -4, 7] = true := by decide +kernel
theorem subd10_3_893 : subd10_3 [2, -3, -7] = true := by decide +kernel
theorem subd10_3_894 : subd10_3 [2, -3, -6] = true := by decide +kernel
theorem subd10_3_895 : subd10_3 [2, -3, -5] = true := by decide +kernel
theorem sbd10_3_27 : ∀ q ∈ blkd10_3_27, subd10_3 q = true := by
  unfold blkd10_3_27
  exact List.forall_mem_cons.2 ⟨subd10_3_864, List.forall_mem_cons.2 ⟨subd10_3_865, List.forall_mem_cons.2 ⟨subd10_3_866, List.forall_mem_cons.2 ⟨subd10_3_867, List.forall_mem_cons.2 ⟨subd10_3_868, List.forall_mem_cons.2 ⟨subd10_3_869, List.forall_mem_cons.2 ⟨subd10_3_870, List.forall_mem_cons.2 ⟨subd10_3_871, List.forall_mem_cons.2 ⟨subd10_3_872, List.forall_mem_cons.2 ⟨subd10_3_873, List.forall_mem_cons.2 ⟨subd10_3_874, List.forall_mem_cons.2 ⟨subd10_3_875, List.forall_mem_cons.2 ⟨subd10_3_876, List.forall_mem_cons.2 ⟨subd10_3_877, List.forall_mem_cons.2 ⟨subd10_3_878, List.forall_mem_cons.2 ⟨subd10_3_879, List.forall_mem_cons.2 ⟨subd10_3_880, List.forall_mem_cons.2 ⟨subd10_3_881, List.forall_mem_cons.2 ⟨subd10_3_882, List.forall_mem_cons.2 ⟨subd10_3_883, List.forall_mem_cons.2 ⟨subd10_3_884, List.forall_mem_cons.2 ⟨subd10_3_885, List.forall_mem_cons.2 ⟨subd10_3_886, List.forall_mem_cons.2 ⟨subd10_3_887, List.forall_mem_cons.2 ⟨subd10_3_888, List.forall_mem_cons.2 ⟨subd10_3_889, List.forall_mem_cons.2 ⟨subd10_3_890, List.forall_mem_cons.2 ⟨subd10_3_891, List.forall_mem_cons.2 ⟨subd10_3_892, List.forall_mem_cons.2 ⟨subd10_3_893, List.forall_mem_cons.2 ⟨subd10_3_894, List.forall_mem_cons.2 ⟨subd10_3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_896 : subd10_3 [2, -3, -4] = true := by decide +kernel
theorem subd10_3_897 : subd10_3 [2, -3, -3] = true := by decide +kernel
theorem subd10_3_898 : subd10_3 [2, -3, -2] = true := by decide +kernel
theorem subd10_3_899 : subd10_3 [2, -3, -1] = true := by decide +kernel
theorem subd10_3_900 : subd10_3 [2, -3, 0] = true := by decide +kernel
theorem subd10_3_901 : subd10_3 [2, -3, 1] = true := by decide +kernel
theorem subd10_3_902 : subd10_3 [2, -3, 2] = true := by decide +kernel
theorem subd10_3_903 : subd10_3 [2, -3, 3] = true := by decide +kernel
theorem subd10_3_904 : subd10_3 [2, -3, 4] = true := by decide +kernel
theorem subd10_3_905 : subd10_3 [2, -3, 5] = true := by decide +kernel
theorem subd10_3_906 : subd10_3 [2, -3, 6] = true := by decide +kernel
theorem subd10_3_907 : subd10_3 [2, -3, 7] = true := by decide +kernel
theorem subd10_3_908 : subd10_3 [2, -3, 8] = true := by decide +kernel
theorem subd10_3_909 : subd10_3 [2, -2, -8] = true := by decide +kernel
theorem subd10_3_910 : subd10_3 [2, -2, -7] = true := by decide +kernel
theorem subd10_3_911 : subd10_3 [2, -2, -6] = true := by decide +kernel
theorem subd10_3_912 : subd10_3 [2, -2, -5] = true := by decide +kernel
theorem subd10_3_913 : subd10_3 [2, -2, -4] = true := by decide +kernel
theorem subd10_3_914 : subd10_3 [2, -2, -3] = true := by decide +kernel
theorem subd10_3_915 : subd10_3 [2, -2, -2] = true := by decide +kernel
theorem subd10_3_916 : subd10_3 [2, -2, -1] = true := by decide +kernel
theorem subd10_3_917 : subd10_3 [2, -2, 0] = true := by decide +kernel
theorem subd10_3_918 : subd10_3 [2, -2, 1] = true := by decide +kernel
theorem subd10_3_919 : subd10_3 [2, -2, 2] = true := by decide +kernel
theorem subd10_3_920 : subd10_3 [2, -2, 3] = true := by decide +kernel
theorem subd10_3_921 : subd10_3 [2, -2, 4] = true := by decide +kernel
theorem subd10_3_922 : subd10_3 [2, -2, 5] = true := by decide +kernel
theorem subd10_3_923 : subd10_3 [2, -2, 6] = true := by decide +kernel
theorem subd10_3_924 : subd10_3 [2, -2, 7] = true := by decide +kernel
theorem subd10_3_925 : subd10_3 [2, -2, 8] = true := by decide +kernel
theorem subd10_3_926 : subd10_3 [2, -1, -9] = true := by decide +kernel
theorem subd10_3_927 : subd10_3 [2, -1, -8] = true := by decide +kernel
theorem sbd10_3_28 : ∀ q ∈ blkd10_3_28, subd10_3 q = true := by
  unfold blkd10_3_28
  exact List.forall_mem_cons.2 ⟨subd10_3_896, List.forall_mem_cons.2 ⟨subd10_3_897, List.forall_mem_cons.2 ⟨subd10_3_898, List.forall_mem_cons.2 ⟨subd10_3_899, List.forall_mem_cons.2 ⟨subd10_3_900, List.forall_mem_cons.2 ⟨subd10_3_901, List.forall_mem_cons.2 ⟨subd10_3_902, List.forall_mem_cons.2 ⟨subd10_3_903, List.forall_mem_cons.2 ⟨subd10_3_904, List.forall_mem_cons.2 ⟨subd10_3_905, List.forall_mem_cons.2 ⟨subd10_3_906, List.forall_mem_cons.2 ⟨subd10_3_907, List.forall_mem_cons.2 ⟨subd10_3_908, List.forall_mem_cons.2 ⟨subd10_3_909, List.forall_mem_cons.2 ⟨subd10_3_910, List.forall_mem_cons.2 ⟨subd10_3_911, List.forall_mem_cons.2 ⟨subd10_3_912, List.forall_mem_cons.2 ⟨subd10_3_913, List.forall_mem_cons.2 ⟨subd10_3_914, List.forall_mem_cons.2 ⟨subd10_3_915, List.forall_mem_cons.2 ⟨subd10_3_916, List.forall_mem_cons.2 ⟨subd10_3_917, List.forall_mem_cons.2 ⟨subd10_3_918, List.forall_mem_cons.2 ⟨subd10_3_919, List.forall_mem_cons.2 ⟨subd10_3_920, List.forall_mem_cons.2 ⟨subd10_3_921, List.forall_mem_cons.2 ⟨subd10_3_922, List.forall_mem_cons.2 ⟨subd10_3_923, List.forall_mem_cons.2 ⟨subd10_3_924, List.forall_mem_cons.2 ⟨subd10_3_925, List.forall_mem_cons.2 ⟨subd10_3_926, List.forall_mem_cons.2 ⟨subd10_3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd10_3_928 : subd10_3 [2, -1, -7] = true := by decide +kernel
theorem subd10_3_929 : subd10_3 [2, -1, -6] = true := by decide +kernel
theorem subd10_3_930 : subd10_3 [2, -1, -5] = true := by decide +kernel
theorem subd10_3_931 : subd10_3 [2, -1, -4] = true := by decide +kernel
theorem subd10_3_932 : subd10_3 [2, -1, -3] = true := by decide +kernel
theorem subd10_3_933 : subd10_3 [2, -1, -2] = true := by decide +kernel
theorem subd10_3_934 : subd10_3 [2, -1, -1] = true := by decide +kernel
theorem subd10_3_935 : subd10_3 [2, -1, 0] = true := by decide +kernel
theorem subd10_3_936 : subd10_3 [2, -1, 1] = true := by decide +kernel
theorem subd10_3_937 : subd10_3 [2, -1, 2] = true := by decide +kernel
theorem subd10_3_938 : subd10_3 [2, -1, 3] = true := by decide +kernel
theorem subd10_3_939 : subd10_3 [2, -1, 4] = true := by decide +kernel
theorem subd10_3_940 : subd10_3 [2, -1, 5] = true := by decide +kernel
theorem subd10_3_941 : subd10_3 [2, -1, 6] = true := by decide +kernel
theorem subd10_3_942 : subd10_3 [2, -1, 7] = true := by decide +kernel
theorem subd10_3_943 : subd10_3 [2, -1, 8] = true := by decide +kernel
theorem subd10_3_944 : subd10_3 [2, 0, -9] = true := by decide +kernel
theorem subd10_3_945 : subd10_3 [2, 0, -8] = true := by decide +kernel
theorem subd10_3_946 : subd10_3 [2, 0, -7] = true := by decide +kernel
theorem subd10_3_947 : subd10_3 [2, 0, -6] = true := by decide +kernel
theorem subd10_3_948 : subd10_3 [2, 0, -5] = true := by decide +kernel
theorem subd10_3_949 : subd10_3 [2, 0, -4] = true := by decide +kernel
theorem subd10_3_950 : subd10_3 [2, 0, -3] = true := by decide +kernel
theorem subd10_3_951 : subd10_3 [2, 0, -2] = true := by decide +kernel
theorem subd10_3_952 : subd10_3 [2, 0, -1] = true := by decide +kernel
theorem subd10_3_953 : subd10_3 [2, 0, 0] = true := by decide +kernel
theorem subd10_3_954 : subd10_3 [2, 0, 1] = true := by decide +kernel
theorem subd10_3_955 : subd10_3 [2, 0, 2] = true := by decide +kernel
theorem subd10_3_956 : subd10_3 [2, 0, 3] = true := by decide +kernel
theorem subd10_3_957 : subd10_3 [2, 0, 4] = true := by decide +kernel
theorem subd10_3_958 : subd10_3 [2, 0, 5] = true := by decide +kernel
theorem subd10_3_959 : subd10_3 [2, 0, 6] = true := by decide +kernel
theorem sbd10_3_29 : ∀ q ∈ blkd10_3_29, subd10_3 q = true := by
  unfold blkd10_3_29
  exact List.forall_mem_cons.2 ⟨subd10_3_928, List.forall_mem_cons.2 ⟨subd10_3_929, List.forall_mem_cons.2 ⟨subd10_3_930, List.forall_mem_cons.2 ⟨subd10_3_931, List.forall_mem_cons.2 ⟨subd10_3_932, List.forall_mem_cons.2 ⟨subd10_3_933, List.forall_mem_cons.2 ⟨subd10_3_934, List.forall_mem_cons.2 ⟨subd10_3_935, List.forall_mem_cons.2 ⟨subd10_3_936, List.forall_mem_cons.2 ⟨subd10_3_937, List.forall_mem_cons.2 ⟨subd10_3_938, List.forall_mem_cons.2 ⟨subd10_3_939, List.forall_mem_cons.2 ⟨subd10_3_940, List.forall_mem_cons.2 ⟨subd10_3_941, List.forall_mem_cons.2 ⟨subd10_3_942, List.forall_mem_cons.2 ⟨subd10_3_943, List.forall_mem_cons.2 ⟨subd10_3_944, List.forall_mem_cons.2 ⟨subd10_3_945, List.forall_mem_cons.2 ⟨subd10_3_946, List.forall_mem_cons.2 ⟨subd10_3_947, List.forall_mem_cons.2 ⟨subd10_3_948, List.forall_mem_cons.2 ⟨subd10_3_949, List.forall_mem_cons.2 ⟨subd10_3_950, List.forall_mem_cons.2 ⟨subd10_3_951, List.forall_mem_cons.2 ⟨subd10_3_952, List.forall_mem_cons.2 ⟨subd10_3_953, List.forall_mem_cons.2 ⟨subd10_3_954, List.forall_mem_cons.2 ⟨subd10_3_955, List.forall_mem_cons.2 ⟨subd10_3_956, List.forall_mem_cons.2 ⟨subd10_3_957, List.forall_mem_cons.2 ⟨subd10_3_958, List.forall_mem_cons.2 ⟨subd10_3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C135
