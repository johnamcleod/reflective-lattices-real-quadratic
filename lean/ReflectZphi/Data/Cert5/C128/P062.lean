import ReflectZphi.Data.Cert5.C128.Base

namespace ReflectZphi.Data.Cert5.C128

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_512 : subd9_1 [1, 2, 2] = true := by decide +kernel
theorem subd9_1_513 : subd9_1 [1, 2, 3] = true := by decide +kernel
theorem subd9_1_514 : subd9_1 [1, 2, 4] = true := by decide +kernel
theorem subd9_1_515 : subd9_1 [1, 2, 5] = true := by decide +kernel
theorem subd9_1_516 : subd9_1 [1, 2, 6] = true := by decide +kernel
theorem subd9_1_517 : subd9_1 [1, 3, -8] = true := by decide +kernel
theorem subd9_1_518 : subd9_1 [1, 3, -7] = true := by decide +kernel
theorem subd9_1_519 : subd9_1 [1, 3, -6] = true := by decide +kernel
theorem subd9_1_520 : subd9_1 [1, 3, -5] = true := by decide +kernel
theorem subd9_1_521 : subd9_1 [1, 3, -4] = true := by decide +kernel
theorem subd9_1_522 : subd9_1 [1, 3, -3] = true := by decide +kernel
theorem subd9_1_523 : subd9_1 [1, 3, -2] = true := by decide +kernel
theorem subd9_1_524 : subd9_1 [1, 3, -1] = true := by decide +kernel
theorem subd9_1_525 : subd9_1 [1, 3, 0] = true := by decide +kernel
theorem subd9_1_526 : subd9_1 [1, 3, 1] = true := by decide +kernel
theorem subd9_1_527 : subd9_1 [1, 3, 2] = true := by decide +kernel
theorem subd9_1_528 : subd9_1 [1, 3, 3] = true := by decide +kernel
theorem subd9_1_529 : subd9_1 [1, 3, 4] = true := by decide +kernel
theorem subd9_1_530 : subd9_1 [1, 3, 5] = true := by decide +kernel
theorem subd9_1_531 : subd9_1 [1, 4] = true := by decide +kernel
theorem subd9_1_532 : subd9_1 [1, 5] = true := by decide +kernel
theorem subd9_1_533 : subd9_1 [1, 6] = true := by decide +kernel
theorem subd9_1_534 : subd9_1 [1, 7] = true := by decide +kernel
theorem subd9_1_535 : subd9_1 [2, -7] = true := by decide +kernel
theorem subd9_1_536 : subd9_1 [2, -6] = true := by decide +kernel
theorem subd9_1_537 : subd9_1 [2, -5] = true := by decide +kernel
theorem subd9_1_538 : subd9_1 [2, -4] = true := by decide +kernel
theorem subd9_1_539 : subd9_1 [2, -3] = true := by decide +kernel
theorem subd9_1_540 : subd9_1 [2, -2, -7] = true := by decide +kernel
theorem subd9_1_541 : subd9_1 [2, -2, -6] = true := by decide +kernel
theorem subd9_1_542 : subd9_1 [2, -2, -5] = true := by decide +kernel
theorem subd9_1_543 : subd9_1 [2, -2, -4] = true := by decide +kernel
theorem sbd9_1_16 : ∀ q ∈ blkd9_1_16, subd9_1 q = true := by
  unfold blkd9_1_16
  exact List.forall_mem_cons.2 ⟨subd9_1_512, List.forall_mem_cons.2 ⟨subd9_1_513, List.forall_mem_cons.2 ⟨subd9_1_514, List.forall_mem_cons.2 ⟨subd9_1_515, List.forall_mem_cons.2 ⟨subd9_1_516, List.forall_mem_cons.2 ⟨subd9_1_517, List.forall_mem_cons.2 ⟨subd9_1_518, List.forall_mem_cons.2 ⟨subd9_1_519, List.forall_mem_cons.2 ⟨subd9_1_520, List.forall_mem_cons.2 ⟨subd9_1_521, List.forall_mem_cons.2 ⟨subd9_1_522, List.forall_mem_cons.2 ⟨subd9_1_523, List.forall_mem_cons.2 ⟨subd9_1_524, List.forall_mem_cons.2 ⟨subd9_1_525, List.forall_mem_cons.2 ⟨subd9_1_526, List.forall_mem_cons.2 ⟨subd9_1_527, List.forall_mem_cons.2 ⟨subd9_1_528, List.forall_mem_cons.2 ⟨subd9_1_529, List.forall_mem_cons.2 ⟨subd9_1_530, List.forall_mem_cons.2 ⟨subd9_1_531, List.forall_mem_cons.2 ⟨subd9_1_532, List.forall_mem_cons.2 ⟨subd9_1_533, List.forall_mem_cons.2 ⟨subd9_1_534, List.forall_mem_cons.2 ⟨subd9_1_535, List.forall_mem_cons.2 ⟨subd9_1_536, List.forall_mem_cons.2 ⟨subd9_1_537, List.forall_mem_cons.2 ⟨subd9_1_538, List.forall_mem_cons.2 ⟨subd9_1_539, List.forall_mem_cons.2 ⟨subd9_1_540, List.forall_mem_cons.2 ⟨subd9_1_541, List.forall_mem_cons.2 ⟨subd9_1_542, List.forall_mem_cons.2 ⟨subd9_1_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_544 : subd9_1 [2, -2, -3] = true := by decide +kernel
theorem subd9_1_545 : subd9_1 [2, -2, -2] = true := by decide +kernel
theorem subd9_1_546 : subd9_1 [2, -2, -1] = true := by decide +kernel
theorem subd9_1_547 : subd9_1 [2, -2, 0] = true := by decide +kernel
theorem subd9_1_548 : subd9_1 [2, -2, 1] = true := by decide +kernel
theorem subd9_1_549 : subd9_1 [2, -2, 2] = true := by decide +kernel
theorem subd9_1_550 : subd9_1 [2, -2, 3] = true := by decide +kernel
theorem subd9_1_551 : subd9_1 [2, -2, 4] = true := by decide +kernel
theorem subd9_1_552 : subd9_1 [2, -2, 5] = true := by decide +kernel
theorem subd9_1_553 : subd9_1 [2, -2, 6] = true := by decide +kernel
theorem subd9_1_554 : subd9_1 [2, -2, 7] = true := by decide +kernel
theorem subd9_1_555 : subd9_1 [2, -1, -7] = true := by decide +kernel
theorem subd9_1_556 : subd9_1 [2, -1, -6] = true := by decide +kernel
theorem subd9_1_557 : subd9_1 [2, -1, -5] = true := by decide +kernel
theorem subd9_1_558 : subd9_1 [2, -1, -4] = true := by decide +kernel
theorem subd9_1_559 : subd9_1 [2, -1, -3] = true := by decide +kernel
theorem subd9_1_560 : subd9_1 [2, -1, -2] = true := by decide +kernel
theorem subd9_1_561 : subd9_1 [2, -1, -1] = true := by decide +kernel
theorem subd9_1_562 : subd9_1 [2, -1, 0] = true := by decide +kernel
theorem subd9_1_563 : subd9_1 [2, -1, 1] = true := by decide +kernel
theorem subd9_1_564 : subd9_1 [2, -1, 2] = true := by decide +kernel
theorem subd9_1_565 : subd9_1 [2, -1, 3] = true := by decide +kernel
theorem subd9_1_566 : subd9_1 [2, -1, 4] = true := by decide +kernel
theorem subd9_1_567 : subd9_1 [2, -1, 5] = true := by decide +kernel
theorem subd9_1_568 : subd9_1 [2, -1, 6] = true := by decide +kernel
theorem subd9_1_569 : subd9_1 [2, -1, 7] = true := by decide +kernel
theorem subd9_1_570 : subd9_1 [2, 0, -8] = true := by decide +kernel
theorem subd9_1_571 : subd9_1 [2, 0, -7] = true := by decide +kernel
theorem subd9_1_572 : subd9_1 [2, 0, -6] = true := by decide +kernel
theorem subd9_1_573 : subd9_1 [2, 0, -5] = true := by decide +kernel
theorem subd9_1_574 : subd9_1 [2, 0, -4] = true := by decide +kernel
theorem subd9_1_575 : subd9_1 [2, 0, -3] = true := by decide +kernel
theorem sbd9_1_17 : ∀ q ∈ blkd9_1_17, subd9_1 q = true := by
  unfold blkd9_1_17
  exact List.forall_mem_cons.2 ⟨subd9_1_544, List.forall_mem_cons.2 ⟨subd9_1_545, List.forall_mem_cons.2 ⟨subd9_1_546, List.forall_mem_cons.2 ⟨subd9_1_547, List.forall_mem_cons.2 ⟨subd9_1_548, List.forall_mem_cons.2 ⟨subd9_1_549, List.forall_mem_cons.2 ⟨subd9_1_550, List.forall_mem_cons.2 ⟨subd9_1_551, List.forall_mem_cons.2 ⟨subd9_1_552, List.forall_mem_cons.2 ⟨subd9_1_553, List.forall_mem_cons.2 ⟨subd9_1_554, List.forall_mem_cons.2 ⟨subd9_1_555, List.forall_mem_cons.2 ⟨subd9_1_556, List.forall_mem_cons.2 ⟨subd9_1_557, List.forall_mem_cons.2 ⟨subd9_1_558, List.forall_mem_cons.2 ⟨subd9_1_559, List.forall_mem_cons.2 ⟨subd9_1_560, List.forall_mem_cons.2 ⟨subd9_1_561, List.forall_mem_cons.2 ⟨subd9_1_562, List.forall_mem_cons.2 ⟨subd9_1_563, List.forall_mem_cons.2 ⟨subd9_1_564, List.forall_mem_cons.2 ⟨subd9_1_565, List.forall_mem_cons.2 ⟨subd9_1_566, List.forall_mem_cons.2 ⟨subd9_1_567, List.forall_mem_cons.2 ⟨subd9_1_568, List.forall_mem_cons.2 ⟨subd9_1_569, List.forall_mem_cons.2 ⟨subd9_1_570, List.forall_mem_cons.2 ⟨subd9_1_571, List.forall_mem_cons.2 ⟨subd9_1_572, List.forall_mem_cons.2 ⟨subd9_1_573, List.forall_mem_cons.2 ⟨subd9_1_574, List.forall_mem_cons.2 ⟨subd9_1_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_576 : subd9_1 [2, 0, -2] = true := by decide +kernel
theorem subd9_1_577 : subd9_1 [2, 0, -1] = true := by decide +kernel
theorem subd9_1_578 : subd9_1 [2, 0, 0] = true := by decide +kernel
theorem subd9_1_579 : subd9_1 [2, 0, 1] = true := by decide +kernel
theorem subd9_1_580 : subd9_1 [2, 0, 2] = true := by decide +kernel
theorem subd9_1_581 : subd9_1 [2, 0, 3] = true := by decide +kernel
theorem subd9_1_582 : subd9_1 [2, 0, 4] = true := by decide +kernel
theorem subd9_1_583 : subd9_1 [2, 0, 5] = true := by decide +kernel
theorem subd9_1_584 : subd9_1 [2, 0, 6] = true := by decide +kernel
theorem subd9_1_585 : subd9_1 [2, 1, -8] = true := by decide +kernel
theorem subd9_1_586 : subd9_1 [2, 1, -7] = true := by decide +kernel
theorem subd9_1_587 : subd9_1 [2, 1, -6] = true := by decide +kernel
theorem subd9_1_588 : subd9_1 [2, 1, -5] = true := by decide +kernel
theorem subd9_1_589 : subd9_1 [2, 1, -4] = true := by decide +kernel
theorem subd9_1_590 : subd9_1 [2, 1, -3] = true := by decide +kernel
theorem subd9_1_591 : subd9_1 [2, 1, -2] = true := by decide +kernel
theorem subd9_1_592 : subd9_1 [2, 1, -1] = true := by decide +kernel
theorem subd9_1_593 : subd9_1 [2, 1, 0] = true := by decide +kernel
theorem subd9_1_594 : subd9_1 [2, 1, 1] = true := by decide +kernel
theorem subd9_1_595 : subd9_1 [2, 1, 2] = true := by decide +kernel
theorem subd9_1_596 : subd9_1 [2, 1, 3] = true := by decide +kernel
theorem subd9_1_597 : subd9_1 [2, 1, 4] = true := by decide +kernel
theorem subd9_1_598 : subd9_1 [2, 1, 5] = true := by decide +kernel
theorem subd9_1_599 : subd9_1 [2, 1, 6] = true := by decide +kernel
theorem subd9_1_600 : subd9_1 [2, 2, -8] = true := by decide +kernel
theorem subd9_1_601 : subd9_1 [2, 2, -7] = true := by decide +kernel
theorem subd9_1_602 : subd9_1 [2, 2, -6] = true := by decide +kernel
theorem subd9_1_603 : subd9_1 [2, 2, -5] = true := by decide +kernel
theorem subd9_1_604 : subd9_1 [2, 2, -4] = true := by decide +kernel
theorem subd9_1_605 : subd9_1 [2, 2, -3] = true := by decide +kernel
theorem subd9_1_606 : subd9_1 [2, 2, -2] = true := by decide +kernel
theorem subd9_1_607 : subd9_1 [2, 2, -1] = true := by decide +kernel
theorem sbd9_1_18 : ∀ q ∈ blkd9_1_18, subd9_1 q = true := by
  unfold blkd9_1_18
  exact List.forall_mem_cons.2 ⟨subd9_1_576, List.forall_mem_cons.2 ⟨subd9_1_577, List.forall_mem_cons.2 ⟨subd9_1_578, List.forall_mem_cons.2 ⟨subd9_1_579, List.forall_mem_cons.2 ⟨subd9_1_580, List.forall_mem_cons.2 ⟨subd9_1_581, List.forall_mem_cons.2 ⟨subd9_1_582, List.forall_mem_cons.2 ⟨subd9_1_583, List.forall_mem_cons.2 ⟨subd9_1_584, List.forall_mem_cons.2 ⟨subd9_1_585, List.forall_mem_cons.2 ⟨subd9_1_586, List.forall_mem_cons.2 ⟨subd9_1_587, List.forall_mem_cons.2 ⟨subd9_1_588, List.forall_mem_cons.2 ⟨subd9_1_589, List.forall_mem_cons.2 ⟨subd9_1_590, List.forall_mem_cons.2 ⟨subd9_1_591, List.forall_mem_cons.2 ⟨subd9_1_592, List.forall_mem_cons.2 ⟨subd9_1_593, List.forall_mem_cons.2 ⟨subd9_1_594, List.forall_mem_cons.2 ⟨subd9_1_595, List.forall_mem_cons.2 ⟨subd9_1_596, List.forall_mem_cons.2 ⟨subd9_1_597, List.forall_mem_cons.2 ⟨subd9_1_598, List.forall_mem_cons.2 ⟨subd9_1_599, List.forall_mem_cons.2 ⟨subd9_1_600, List.forall_mem_cons.2 ⟨subd9_1_601, List.forall_mem_cons.2 ⟨subd9_1_602, List.forall_mem_cons.2 ⟨subd9_1_603, List.forall_mem_cons.2 ⟨subd9_1_604, List.forall_mem_cons.2 ⟨subd9_1_605, List.forall_mem_cons.2 ⟨subd9_1_606, List.forall_mem_cons.2 ⟨subd9_1_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_608 : subd9_1 [2, 2, 0] = true := by decide +kernel
theorem subd9_1_609 : subd9_1 [2, 2, 1] = true := by decide +kernel
theorem subd9_1_610 : subd9_1 [2, 2, 2] = true := by decide +kernel
theorem subd9_1_611 : subd9_1 [2, 2, 3] = true := by decide +kernel
theorem subd9_1_612 : subd9_1 [2, 2, 4] = true := by decide +kernel
theorem subd9_1_613 : subd9_1 [2, 2, 5] = true := by decide +kernel
theorem subd9_1_614 : subd9_1 [2, 3, -8] = true := by decide +kernel
theorem subd9_1_615 : subd9_1 [2, 3, -7] = true := by decide +kernel
theorem subd9_1_616 : subd9_1 [2, 3, -6] = true := by decide +kernel
theorem subd9_1_617 : subd9_1 [2, 3, -5] = true := by decide +kernel
theorem subd9_1_618 : subd9_1 [2, 3, -4] = true := by decide +kernel
theorem subd9_1_619 : subd9_1 [2, 3, -3] = true := by decide +kernel
theorem subd9_1_620 : subd9_1 [2, 3, -2] = true := by decide +kernel
theorem subd9_1_621 : subd9_1 [2, 3, -1] = true := by decide +kernel
theorem subd9_1_622 : subd9_1 [2, 3, 0] = true := by decide +kernel
theorem subd9_1_623 : subd9_1 [2, 3, 1] = true := by decide +kernel
theorem subd9_1_624 : subd9_1 [2, 3, 2] = true := by decide +kernel
theorem subd9_1_625 : subd9_1 [2, 3, 3] = true := by decide +kernel
theorem subd9_1_626 : subd9_1 [2, 3, 4] = true := by decide +kernel
theorem subd9_1_627 : subd9_1 [2, 3, 5] = true := by decide +kernel
theorem subd9_1_628 : subd9_1 [2, 4] = true := by decide +kernel
theorem subd9_1_629 : subd9_1 [2, 5] = true := by decide +kernel
theorem subd9_1_630 : subd9_1 [2, 6] = true := by decide +kernel
theorem subd9_1_631 : subd9_1 [2, 7] = true := by decide +kernel
theorem subd9_1_632 : subd9_1 [3, -7] = true := by decide +kernel
theorem subd9_1_633 : subd9_1 [3, -6] = true := by decide +kernel
theorem subd9_1_634 : subd9_1 [3, -5] = true := by decide +kernel
theorem subd9_1_635 : subd9_1 [3, -4] = true := by decide +kernel
theorem subd9_1_636 : subd9_1 [3, -3] = true := by decide +kernel
theorem subd9_1_637 : subd9_1 [3, -2] = true := by decide +kernel
theorem subd9_1_638 : subd9_1 [3, -1, -7] = true := by decide +kernel
theorem subd9_1_639 : subd9_1 [3, -1, -6] = true := by decide +kernel
theorem sbd9_1_19 : ∀ q ∈ blkd9_1_19, subd9_1 q = true := by
  unfold blkd9_1_19
  exact List.forall_mem_cons.2 ⟨subd9_1_608, List.forall_mem_cons.2 ⟨subd9_1_609, List.forall_mem_cons.2 ⟨subd9_1_610, List.forall_mem_cons.2 ⟨subd9_1_611, List.forall_mem_cons.2 ⟨subd9_1_612, List.forall_mem_cons.2 ⟨subd9_1_613, List.forall_mem_cons.2 ⟨subd9_1_614, List.forall_mem_cons.2 ⟨subd9_1_615, List.forall_mem_cons.2 ⟨subd9_1_616, List.forall_mem_cons.2 ⟨subd9_1_617, List.forall_mem_cons.2 ⟨subd9_1_618, List.forall_mem_cons.2 ⟨subd9_1_619, List.forall_mem_cons.2 ⟨subd9_1_620, List.forall_mem_cons.2 ⟨subd9_1_621, List.forall_mem_cons.2 ⟨subd9_1_622, List.forall_mem_cons.2 ⟨subd9_1_623, List.forall_mem_cons.2 ⟨subd9_1_624, List.forall_mem_cons.2 ⟨subd9_1_625, List.forall_mem_cons.2 ⟨subd9_1_626, List.forall_mem_cons.2 ⟨subd9_1_627, List.forall_mem_cons.2 ⟨subd9_1_628, List.forall_mem_cons.2 ⟨subd9_1_629, List.forall_mem_cons.2 ⟨subd9_1_630, List.forall_mem_cons.2 ⟨subd9_1_631, List.forall_mem_cons.2 ⟨subd9_1_632, List.forall_mem_cons.2 ⟨subd9_1_633, List.forall_mem_cons.2 ⟨subd9_1_634, List.forall_mem_cons.2 ⟨subd9_1_635, List.forall_mem_cons.2 ⟨subd9_1_636, List.forall_mem_cons.2 ⟨subd9_1_637, List.forall_mem_cons.2 ⟨subd9_1_638, List.forall_mem_cons.2 ⟨subd9_1_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_640 : subd9_1 [3, -1, -5] = true := by decide +kernel
theorem subd9_1_641 : subd9_1 [3, -1, -4] = true := by decide +kernel
theorem subd9_1_642 : subd9_1 [3, -1, -3] = true := by decide +kernel
theorem subd9_1_643 : subd9_1 [3, -1, -2] = true := by decide +kernel
theorem subd9_1_644 : subd9_1 [3, -1, -1] = true := by decide +kernel
theorem subd9_1_645 : subd9_1 [3, -1, 0] = true := by decide +kernel
theorem subd9_1_646 : subd9_1 [3, -1, 1] = true := by decide +kernel
theorem subd9_1_647 : subd9_1 [3, -1, 2] = true := by decide +kernel
theorem subd9_1_648 : subd9_1 [3, -1, 3] = true := by decide +kernel
theorem subd9_1_649 : subd9_1 [3, -1, 4] = true := by decide +kernel
theorem subd9_1_650 : subd9_1 [3, -1, 5] = true := by decide +kernel
theorem subd9_1_651 : subd9_1 [3, -1, 6] = true := by decide +kernel
theorem subd9_1_652 : subd9_1 [3, 0, -7] = true := by decide +kernel
theorem subd9_1_653 : subd9_1 [3, 0, -6] = true := by decide +kernel
theorem subd9_1_654 : subd9_1 [3, 0, -5] = true := by decide +kernel
theorem subd9_1_655 : subd9_1 [3, 0, -4] = true := by decide +kernel
theorem subd9_1_656 : subd9_1 [3, 0, -3] = true := by decide +kernel
theorem subd9_1_657 : subd9_1 [3, 0, -2] = true := by decide +kernel
theorem subd9_1_658 : subd9_1 [3, 0, -1] = true := by decide +kernel
theorem subd9_1_659 : subd9_1 [3, 0, 0] = true := by decide +kernel
theorem subd9_1_660 : subd9_1 [3, 0, 1] = true := by decide +kernel
theorem subd9_1_661 : subd9_1 [3, 0, 2] = true := by decide +kernel
theorem subd9_1_662 : subd9_1 [3, 0, 3] = true := by decide +kernel
theorem subd9_1_663 : subd9_1 [3, 0, 4] = true := by decide +kernel
theorem subd9_1_664 : subd9_1 [3, 0, 5] = true := by decide +kernel
theorem subd9_1_665 : subd9_1 [3, 0, 6] = true := by decide +kernel
theorem subd9_1_666 : subd9_1 [3, 1, -7] = true := by decide +kernel
theorem subd9_1_667 : subd9_1 [3, 1, -6] = true := by decide +kernel
theorem subd9_1_668 : subd9_1 [3, 1, -5] = true := by decide +kernel
theorem subd9_1_669 : subd9_1 [3, 1, -4] = true := by decide +kernel
theorem subd9_1_670 : subd9_1 [3, 1, -3] = true := by decide +kernel
theorem subd9_1_671 : subd9_1 [3, 1, -2] = true := by decide +kernel
theorem sbd9_1_20 : ∀ q ∈ blkd9_1_20, subd9_1 q = true := by
  unfold blkd9_1_20
  exact List.forall_mem_cons.2 ⟨subd9_1_640, List.forall_mem_cons.2 ⟨subd9_1_641, List.forall_mem_cons.2 ⟨subd9_1_642, List.forall_mem_cons.2 ⟨subd9_1_643, List.forall_mem_cons.2 ⟨subd9_1_644, List.forall_mem_cons.2 ⟨subd9_1_645, List.forall_mem_cons.2 ⟨subd9_1_646, List.forall_mem_cons.2 ⟨subd9_1_647, List.forall_mem_cons.2 ⟨subd9_1_648, List.forall_mem_cons.2 ⟨subd9_1_649, List.forall_mem_cons.2 ⟨subd9_1_650, List.forall_mem_cons.2 ⟨subd9_1_651, List.forall_mem_cons.2 ⟨subd9_1_652, List.forall_mem_cons.2 ⟨subd9_1_653, List.forall_mem_cons.2 ⟨subd9_1_654, List.forall_mem_cons.2 ⟨subd9_1_655, List.forall_mem_cons.2 ⟨subd9_1_656, List.forall_mem_cons.2 ⟨subd9_1_657, List.forall_mem_cons.2 ⟨subd9_1_658, List.forall_mem_cons.2 ⟨subd9_1_659, List.forall_mem_cons.2 ⟨subd9_1_660, List.forall_mem_cons.2 ⟨subd9_1_661, List.forall_mem_cons.2 ⟨subd9_1_662, List.forall_mem_cons.2 ⟨subd9_1_663, List.forall_mem_cons.2 ⟨subd9_1_664, List.forall_mem_cons.2 ⟨subd9_1_665, List.forall_mem_cons.2 ⟨subd9_1_666, List.forall_mem_cons.2 ⟨subd9_1_667, List.forall_mem_cons.2 ⟨subd9_1_668, List.forall_mem_cons.2 ⟨subd9_1_669, List.forall_mem_cons.2 ⟨subd9_1_670, List.forall_mem_cons.2 ⟨subd9_1_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_672 : subd9_1 [3, 1, -1] = true := by decide +kernel
theorem subd9_1_673 : subd9_1 [3, 1, 0] = true := by decide +kernel
theorem subd9_1_674 : subd9_1 [3, 1, 1] = true := by decide +kernel
theorem subd9_1_675 : subd9_1 [3, 1, 2] = true := by decide +kernel
theorem subd9_1_676 : subd9_1 [3, 1, 3] = true := by decide +kernel
theorem subd9_1_677 : subd9_1 [3, 1, 4] = true := by decide +kernel
theorem subd9_1_678 : subd9_1 [3, 1, 5] = true := by decide +kernel
theorem subd9_1_679 : subd9_1 [3, 1, 6] = true := by decide +kernel
theorem subd9_1_680 : subd9_1 [3, 2, -8] = true := by decide +kernel
theorem subd9_1_681 : subd9_1 [3, 2, -7] = true := by decide +kernel
theorem subd9_1_682 : subd9_1 [3, 2, -6] = true := by decide +kernel
theorem subd9_1_683 : subd9_1 [3, 2, -5] = true := by decide +kernel
theorem subd9_1_684 : subd9_1 [3, 2, -4] = true := by decide +kernel
theorem subd9_1_685 : subd9_1 [3, 2, -3] = true := by decide +kernel
theorem subd9_1_686 : subd9_1 [3, 2, -2] = true := by decide +kernel
theorem subd9_1_687 : subd9_1 [3, 2, -1] = true := by decide +kernel
theorem subd9_1_688 : subd9_1 [3, 2, 0] = true := by decide +kernel
theorem subd9_1_689 : subd9_1 [3, 2, 1] = true := by decide +kernel
theorem subd9_1_690 : subd9_1 [3, 2, 2] = true := by decide +kernel
theorem subd9_1_691 : subd9_1 [3, 2, 3] = true := by decide +kernel
theorem subd9_1_692 : subd9_1 [3, 2, 4] = true := by decide +kernel
theorem subd9_1_693 : subd9_1 [3, 2, 5] = true := by decide +kernel
theorem subd9_1_694 : subd9_1 [3, 3] = true := by decide +kernel
theorem subd9_1_695 : subd9_1 [3, 4] = true := by decide +kernel
theorem subd9_1_696 : subd9_1 [3, 5] = true := by decide +kernel
theorem subd9_1_697 : subd9_1 [3, 6] = true := by decide +kernel
theorem subd9_1_698 : subd9_1 [4, -6] = true := by decide +kernel
theorem subd9_1_699 : subd9_1 [4, -5] = true := by decide +kernel
theorem subd9_1_700 : subd9_1 [4, -4] = true := by decide +kernel
theorem subd9_1_701 : subd9_1 [4, -3] = true := by decide +kernel
theorem subd9_1_702 : subd9_1 [4, -2] = true := by decide +kernel
theorem subd9_1_703 : subd9_1 [4, -1] = true := by decide +kernel
theorem sbd9_1_21 : ∀ q ∈ blkd9_1_21, subd9_1 q = true := by
  unfold blkd9_1_21
  exact List.forall_mem_cons.2 ⟨subd9_1_672, List.forall_mem_cons.2 ⟨subd9_1_673, List.forall_mem_cons.2 ⟨subd9_1_674, List.forall_mem_cons.2 ⟨subd9_1_675, List.forall_mem_cons.2 ⟨subd9_1_676, List.forall_mem_cons.2 ⟨subd9_1_677, List.forall_mem_cons.2 ⟨subd9_1_678, List.forall_mem_cons.2 ⟨subd9_1_679, List.forall_mem_cons.2 ⟨subd9_1_680, List.forall_mem_cons.2 ⟨subd9_1_681, List.forall_mem_cons.2 ⟨subd9_1_682, List.forall_mem_cons.2 ⟨subd9_1_683, List.forall_mem_cons.2 ⟨subd9_1_684, List.forall_mem_cons.2 ⟨subd9_1_685, List.forall_mem_cons.2 ⟨subd9_1_686, List.forall_mem_cons.2 ⟨subd9_1_687, List.forall_mem_cons.2 ⟨subd9_1_688, List.forall_mem_cons.2 ⟨subd9_1_689, List.forall_mem_cons.2 ⟨subd9_1_690, List.forall_mem_cons.2 ⟨subd9_1_691, List.forall_mem_cons.2 ⟨subd9_1_692, List.forall_mem_cons.2 ⟨subd9_1_693, List.forall_mem_cons.2 ⟨subd9_1_694, List.forall_mem_cons.2 ⟨subd9_1_695, List.forall_mem_cons.2 ⟨subd9_1_696, List.forall_mem_cons.2 ⟨subd9_1_697, List.forall_mem_cons.2 ⟨subd9_1_698, List.forall_mem_cons.2 ⟨subd9_1_699, List.forall_mem_cons.2 ⟨subd9_1_700, List.forall_mem_cons.2 ⟨subd9_1_701, List.forall_mem_cons.2 ⟨subd9_1_702, List.forall_mem_cons.2 ⟨subd9_1_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_704 : subd9_1 [4, 0] = true := by decide +kernel
theorem subd9_1_705 : subd9_1 [4, 1] = true := by decide +kernel
theorem subd9_1_706 : subd9_1 [4, 2] = true := by decide +kernel
theorem subd9_1_707 : subd9_1 [4, 3] = true := by decide +kernel
theorem subd9_1_708 : subd9_1 [4, 4] = true := by decide +kernel
theorem subd9_1_709 : subd9_1 [4, 5] = true := by decide +kernel
theorem subd9_1_710 : subd9_1 [4, 6] = true := by decide +kernel
theorem subd9_1_711 : subd9_1 [5, -5] = true := by decide +kernel
theorem subd9_1_712 : subd9_1 [5, -4] = true := by decide +kernel
theorem subd9_1_713 : subd9_1 [5, -3] = true := by decide +kernel
theorem subd9_1_714 : subd9_1 [5, -2] = true := by decide +kernel
theorem subd9_1_715 : subd9_1 [5, -1] = true := by decide +kernel
theorem subd9_1_716 : subd9_1 [5, 0] = true := by decide +kernel
theorem subd9_1_717 : subd9_1 [5, 1] = true := by decide +kernel
theorem subd9_1_718 : subd9_1 [5, 2] = true := by decide +kernel
theorem subd9_1_719 : subd9_1 [5, 3] = true := by decide +kernel
theorem subd9_1_720 : subd9_1 [5, 4] = true := by decide +kernel
theorem subd9_1_721 : subd9_1 [5, 5] = true := by decide +kernel
theorem subd9_1_722 : subd9_1 [6, -4] = true := by decide +kernel
theorem subd9_1_723 : subd9_1 [6, -3] = true := by decide +kernel
theorem subd9_1_724 : subd9_1 [6, -2] = true := by decide +kernel
theorem subd9_1_725 : subd9_1 [6, -1] = true := by decide +kernel
theorem subd9_1_726 : subd9_1 [6, 0] = true := by decide +kernel
theorem subd9_1_727 : subd9_1 [6, 1] = true := by decide +kernel
theorem subd9_1_728 : subd9_1 [6, 2] = true := by decide +kernel
theorem subd9_1_729 : subd9_1 [6, 3] = true := by decide +kernel
theorem subd9_1_730 : subd9_1 [6, 4] = true := by decide +kernel
theorem sbd9_1_22 : ∀ q ∈ blkd9_1_22, subd9_1 q = true := by
  unfold blkd9_1_22
  exact List.forall_mem_cons.2 ⟨subd9_1_704, List.forall_mem_cons.2 ⟨subd9_1_705, List.forall_mem_cons.2 ⟨subd9_1_706, List.forall_mem_cons.2 ⟨subd9_1_707, List.forall_mem_cons.2 ⟨subd9_1_708, List.forall_mem_cons.2 ⟨subd9_1_709, List.forall_mem_cons.2 ⟨subd9_1_710, List.forall_mem_cons.2 ⟨subd9_1_711, List.forall_mem_cons.2 ⟨subd9_1_712, List.forall_mem_cons.2 ⟨subd9_1_713, List.forall_mem_cons.2 ⟨subd9_1_714, List.forall_mem_cons.2 ⟨subd9_1_715, List.forall_mem_cons.2 ⟨subd9_1_716, List.forall_mem_cons.2 ⟨subd9_1_717, List.forall_mem_cons.2 ⟨subd9_1_718, List.forall_mem_cons.2 ⟨subd9_1_719, List.forall_mem_cons.2 ⟨subd9_1_720, List.forall_mem_cons.2 ⟨subd9_1_721, List.forall_mem_cons.2 ⟨subd9_1_722, List.forall_mem_cons.2 ⟨subd9_1_723, List.forall_mem_cons.2 ⟨subd9_1_724, List.forall_mem_cons.2 ⟨subd9_1_725, List.forall_mem_cons.2 ⟨subd9_1_726, List.forall_mem_cons.2 ⟨subd9_1_727, List.forall_mem_cons.2 ⟨subd9_1_728, List.forall_mem_cons.2 ⟨subd9_1_729, List.forall_mem_cons.2 ⟨subd9_1_730, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd9_2 : ldCheck G d9_2.U d9_2.ms ldd9_2 = true := by decide +kernel
theorem pre_okd9_2 : subPre G cell9 d9_2 = true := by decide +kernel
theorem subd9_2_0 : subd9_2 [-4] = true := by decide +kernel
theorem subd9_2_1 : subd9_2 [-3, -3] = true := by decide +kernel
theorem subd9_2_2 : subd9_2 [-3, -2] = true := by decide +kernel
theorem subd9_2_3 : subd9_2 [-3, -1] = true := by decide +kernel
theorem subd9_2_4 : subd9_2 [-3, 0, -9] = true := by decide +kernel
theorem subd9_2_5 : subd9_2 [-3, 0, -8] = true := by decide +kernel
theorem subd9_2_6 : subd9_2 [-3, 0, -7] = true := by decide +kernel
theorem subd9_2_7 : subd9_2 [-3, 0, -6] = true := by decide +kernel
theorem subd9_2_8 : subd9_2 [-3, 0, -5] = true := by decide +kernel
theorem subd9_2_9 : subd9_2 [-3, 0, -4] = true := by decide +kernel
theorem subd9_2_10 : subd9_2 [-3, 0, -3] = true := by decide +kernel
theorem subd9_2_11 : subd9_2 [-3, 0, -2] = true := by decide +kernel
theorem subd9_2_12 : subd9_2 [-3, 0, -1] = true := by decide +kernel
theorem subd9_2_13 : subd9_2 [-3, 0, 0] = true := by decide +kernel
theorem subd9_2_14 : subd9_2 [-3, 0, 1] = true := by decide +kernel
theorem subd9_2_15 : subd9_2 [-3, 0, 2] = true := by decide +kernel
theorem subd9_2_16 : subd9_2 [-3, 0, 3] = true := by decide +kernel
theorem subd9_2_17 : subd9_2 [-3, 0, 4] = true := by decide +kernel
theorem subd9_2_18 : subd9_2 [-3, 0, 5] = true := by decide +kernel
theorem subd9_2_19 : subd9_2 [-3, 0, 6] = true := by decide +kernel
theorem subd9_2_20 : subd9_2 [-3, 1, -9] = true := by decide +kernel
theorem subd9_2_21 : subd9_2 [-3, 1, -8] = true := by decide +kernel
theorem subd9_2_22 : subd9_2 [-3, 1, -7] = true := by decide +kernel
theorem subd9_2_23 : subd9_2 [-3, 1, -6] = true := by decide +kernel
theorem subd9_2_24 : subd9_2 [-3, 1, -5] = true := by decide +kernel
theorem subd9_2_25 : subd9_2 [-3, 1, -4] = true := by decide +kernel
theorem subd9_2_26 : subd9_2 [-3, 1, -3] = true := by decide +kernel
theorem subd9_2_27 : subd9_2 [-3, 1, -2] = true := by decide +kernel
theorem subd9_2_28 : subd9_2 [-3, 1, -1] = true := by decide +kernel
theorem subd9_2_29 : subd9_2 [-3, 1, 0] = true := by decide +kernel
theorem subd9_2_30 : subd9_2 [-3, 1, 1] = true := by decide +kernel
theorem subd9_2_31 : subd9_2 [-3, 1, 2] = true := by decide +kernel
theorem sbd9_2_0 : ∀ q ∈ blkd9_2_0, subd9_2 q = true := by
  unfold blkd9_2_0
  exact List.forall_mem_cons.2 ⟨subd9_2_0, List.forall_mem_cons.2 ⟨subd9_2_1, List.forall_mem_cons.2 ⟨subd9_2_2, List.forall_mem_cons.2 ⟨subd9_2_3, List.forall_mem_cons.2 ⟨subd9_2_4, List.forall_mem_cons.2 ⟨subd9_2_5, List.forall_mem_cons.2 ⟨subd9_2_6, List.forall_mem_cons.2 ⟨subd9_2_7, List.forall_mem_cons.2 ⟨subd9_2_8, List.forall_mem_cons.2 ⟨subd9_2_9, List.forall_mem_cons.2 ⟨subd9_2_10, List.forall_mem_cons.2 ⟨subd9_2_11, List.forall_mem_cons.2 ⟨subd9_2_12, List.forall_mem_cons.2 ⟨subd9_2_13, List.forall_mem_cons.2 ⟨subd9_2_14, List.forall_mem_cons.2 ⟨subd9_2_15, List.forall_mem_cons.2 ⟨subd9_2_16, List.forall_mem_cons.2 ⟨subd9_2_17, List.forall_mem_cons.2 ⟨subd9_2_18, List.forall_mem_cons.2 ⟨subd9_2_19, List.forall_mem_cons.2 ⟨subd9_2_20, List.forall_mem_cons.2 ⟨subd9_2_21, List.forall_mem_cons.2 ⟨subd9_2_22, List.forall_mem_cons.2 ⟨subd9_2_23, List.forall_mem_cons.2 ⟨subd9_2_24, List.forall_mem_cons.2 ⟨subd9_2_25, List.forall_mem_cons.2 ⟨subd9_2_26, List.forall_mem_cons.2 ⟨subd9_2_27, List.forall_mem_cons.2 ⟨subd9_2_28, List.forall_mem_cons.2 ⟨subd9_2_29, List.forall_mem_cons.2 ⟨subd9_2_30, List.forall_mem_cons.2 ⟨subd9_2_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_2_32 : subd9_2 [-3, 1, 3] = true := by decide +kernel
theorem subd9_2_33 : subd9_2 [-3, 1, 4] = true := by decide +kernel
theorem subd9_2_34 : subd9_2 [-3, 1, 5] = true := by decide +kernel
theorem subd9_2_35 : subd9_2 [-3, 1, 6] = true := by decide +kernel
theorem subd9_2_36 : subd9_2 [-3, 1, 7] = true := by decide +kernel
theorem subd9_2_37 : subd9_2 [-3, 2, -8] = true := by decide +kernel
theorem subd9_2_38 : subd9_2 [-3, 2, -7] = true := by decide +kernel
theorem subd9_2_39 : subd9_2 [-3, 2, -6] = true := by decide +kernel
theorem subd9_2_40 : subd9_2 [-3, 2, -5] = true := by decide +kernel
theorem subd9_2_41 : subd9_2 [-3, 2, -4] = true := by decide +kernel
theorem subd9_2_42 : subd9_2 [-3, 2, -3] = true := by decide +kernel
theorem subd9_2_43 : subd9_2 [-3, 2, -2] = true := by decide +kernel
theorem subd9_2_44 : subd9_2 [-3, 2, -1] = true := by decide +kernel
theorem subd9_2_45 : subd9_2 [-3, 2, 0] = true := by decide +kernel
theorem subd9_2_46 : subd9_2 [-3, 2, 1] = true := by decide +kernel
theorem subd9_2_47 : subd9_2 [-3, 2, 2] = true := by decide +kernel
theorem subd9_2_48 : subd9_2 [-3, 2, 3] = true := by decide +kernel
theorem subd9_2_49 : subd9_2 [-3, 2, 4] = true := by decide +kernel
theorem subd9_2_50 : subd9_2 [-3, 2, 5] = true := by decide +kernel
theorem subd9_2_51 : subd9_2 [-3, 2, 6] = true := by decide +kernel
theorem subd9_2_52 : subd9_2 [-3, 2, 7] = true := by decide +kernel
theorem subd9_2_53 : subd9_2 [-3, 3] = true := by decide +kernel
theorem subd9_2_54 : subd9_2 [-3, 4] = true := by decide +kernel
theorem subd9_2_55 : subd9_2 [-2, -4] = true := by decide +kernel
theorem subd9_2_56 : subd9_2 [-2, -3] = true := by decide +kernel
theorem subd9_2_57 : subd9_2 [-2, -2, -9] = true := by decide +kernel
theorem subd9_2_58 : subd9_2 [-2, -2, -8] = true := by decide +kernel
theorem subd9_2_59 : subd9_2 [-2, -2, -7] = true := by decide +kernel
theorem subd9_2_60 : subd9_2 [-2, -2, -6] = true := by decide +kernel
theorem subd9_2_61 : subd9_2 [-2, -2, -5] = true := by decide +kernel
theorem subd9_2_62 : subd9_2 [-2, -2, -4] = true := by decide +kernel
theorem subd9_2_63 : subd9_2 [-2, -2, -3] = true := by decide +kernel
theorem sbd9_2_1 : ∀ q ∈ blkd9_2_1, subd9_2 q = true := by
  unfold blkd9_2_1
  exact List.forall_mem_cons.2 ⟨subd9_2_32, List.forall_mem_cons.2 ⟨subd9_2_33, List.forall_mem_cons.2 ⟨subd9_2_34, List.forall_mem_cons.2 ⟨subd9_2_35, List.forall_mem_cons.2 ⟨subd9_2_36, List.forall_mem_cons.2 ⟨subd9_2_37, List.forall_mem_cons.2 ⟨subd9_2_38, List.forall_mem_cons.2 ⟨subd9_2_39, List.forall_mem_cons.2 ⟨subd9_2_40, List.forall_mem_cons.2 ⟨subd9_2_41, List.forall_mem_cons.2 ⟨subd9_2_42, List.forall_mem_cons.2 ⟨subd9_2_43, List.forall_mem_cons.2 ⟨subd9_2_44, List.forall_mem_cons.2 ⟨subd9_2_45, List.forall_mem_cons.2 ⟨subd9_2_46, List.forall_mem_cons.2 ⟨subd9_2_47, List.forall_mem_cons.2 ⟨subd9_2_48, List.forall_mem_cons.2 ⟨subd9_2_49, List.forall_mem_cons.2 ⟨subd9_2_50, List.forall_mem_cons.2 ⟨subd9_2_51, List.forall_mem_cons.2 ⟨subd9_2_52, List.forall_mem_cons.2 ⟨subd9_2_53, List.forall_mem_cons.2 ⟨subd9_2_54, List.forall_mem_cons.2 ⟨subd9_2_55, List.forall_mem_cons.2 ⟨subd9_2_56, List.forall_mem_cons.2 ⟨subd9_2_57, List.forall_mem_cons.2 ⟨subd9_2_58, List.forall_mem_cons.2 ⟨subd9_2_59, List.forall_mem_cons.2 ⟨subd9_2_60, List.forall_mem_cons.2 ⟨subd9_2_61, List.forall_mem_cons.2 ⟨subd9_2_62, List.forall_mem_cons.2 ⟨subd9_2_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C128
