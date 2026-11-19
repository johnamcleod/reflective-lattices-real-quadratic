import ReflectZphi.Data.Cert5.C096.Base

namespace ReflectZphi.Data.Cert5.C096

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_3_512 : subd9_3 [-1, 3, -3] = true := by decide +kernel
theorem subd9_3_513 : subd9_3 [-1, 3, -2] = true := by decide +kernel
theorem subd9_3_514 : subd9_3 [-1, 3, -1] = true := by decide +kernel
theorem subd9_3_515 : subd9_3 [-1, 3, 0] = true := by decide +kernel
theorem subd9_3_516 : subd9_3 [-1, 3, 1] = true := by decide +kernel
theorem subd9_3_517 : subd9_3 [-1, 3, 2] = true := by decide +kernel
theorem subd9_3_518 : subd9_3 [-1, 3, 3] = true := by decide +kernel
theorem subd9_3_519 : subd9_3 [-1, 3, 4] = true := by decide +kernel
theorem subd9_3_520 : subd9_3 [-1, 3, 5] = true := by decide +kernel
theorem subd9_3_521 : subd9_3 [-1, 3, 6] = true := by decide +kernel
theorem subd9_3_522 : subd9_3 [-1, 3, 7] = true := by decide +kernel
theorem subd9_3_523 : subd9_3 [-1, 3, 8] = true := by decide +kernel
theorem subd9_3_524 : subd9_3 [-1, 4, -8] = true := by decide +kernel
theorem subd9_3_525 : subd9_3 [-1, 4, -7] = true := by decide +kernel
theorem subd9_3_526 : subd9_3 [-1, 4, -6] = true := by decide +kernel
theorem subd9_3_527 : subd9_3 [-1, 4, -5] = true := by decide +kernel
theorem subd9_3_528 : subd9_3 [-1, 4, -4] = true := by decide +kernel
theorem subd9_3_529 : subd9_3 [-1, 4, -3] = true := by decide +kernel
theorem subd9_3_530 : subd9_3 [-1, 4, -2] = true := by decide +kernel
theorem subd9_3_531 : subd9_3 [-1, 4, -1] = true := by decide +kernel
theorem subd9_3_532 : subd9_3 [-1, 4, 0] = true := by decide +kernel
theorem subd9_3_533 : subd9_3 [-1, 4, 1] = true := by decide +kernel
theorem subd9_3_534 : subd9_3 [-1, 4, 2] = true := by decide +kernel
theorem subd9_3_535 : subd9_3 [-1, 4, 3] = true := by decide +kernel
theorem subd9_3_536 : subd9_3 [-1, 4, 4] = true := by decide +kernel
theorem subd9_3_537 : subd9_3 [-1, 4, 5] = true := by decide +kernel
theorem subd9_3_538 : subd9_3 [-1, 4, 6] = true := by decide +kernel
theorem subd9_3_539 : subd9_3 [-1, 4, 7] = true := by decide +kernel
theorem subd9_3_540 : subd9_3 [-1, 5] = true := by decide +kernel
theorem subd9_3_541 : subd9_3 [-1, 6] = true := by decide +kernel
theorem subd9_3_542 : subd9_3 [0, -7] = true := by decide +kernel
theorem subd9_3_543 : subd9_3 [0, -6] = true := by decide +kernel
theorem sbd9_3_16 : ∀ q ∈ blkd9_3_16, subd9_3 q = true := by
  unfold blkd9_3_16
  exact List.forall_mem_cons.2 ⟨subd9_3_512, List.forall_mem_cons.2 ⟨subd9_3_513, List.forall_mem_cons.2 ⟨subd9_3_514, List.forall_mem_cons.2 ⟨subd9_3_515, List.forall_mem_cons.2 ⟨subd9_3_516, List.forall_mem_cons.2 ⟨subd9_3_517, List.forall_mem_cons.2 ⟨subd9_3_518, List.forall_mem_cons.2 ⟨subd9_3_519, List.forall_mem_cons.2 ⟨subd9_3_520, List.forall_mem_cons.2 ⟨subd9_3_521, List.forall_mem_cons.2 ⟨subd9_3_522, List.forall_mem_cons.2 ⟨subd9_3_523, List.forall_mem_cons.2 ⟨subd9_3_524, List.forall_mem_cons.2 ⟨subd9_3_525, List.forall_mem_cons.2 ⟨subd9_3_526, List.forall_mem_cons.2 ⟨subd9_3_527, List.forall_mem_cons.2 ⟨subd9_3_528, List.forall_mem_cons.2 ⟨subd9_3_529, List.forall_mem_cons.2 ⟨subd9_3_530, List.forall_mem_cons.2 ⟨subd9_3_531, List.forall_mem_cons.2 ⟨subd9_3_532, List.forall_mem_cons.2 ⟨subd9_3_533, List.forall_mem_cons.2 ⟨subd9_3_534, List.forall_mem_cons.2 ⟨subd9_3_535, List.forall_mem_cons.2 ⟨subd9_3_536, List.forall_mem_cons.2 ⟨subd9_3_537, List.forall_mem_cons.2 ⟨subd9_3_538, List.forall_mem_cons.2 ⟨subd9_3_539, List.forall_mem_cons.2 ⟨subd9_3_540, List.forall_mem_cons.2 ⟨subd9_3_541, List.forall_mem_cons.2 ⟨subd9_3_542, List.forall_mem_cons.2 ⟨subd9_3_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_544 : subd9_3 [0, -5] = true := by decide +kernel
theorem subd9_3_545 : subd9_3 [0, -4, -8] = true := by decide +kernel
theorem subd9_3_546 : subd9_3 [0, -4, -7] = true := by decide +kernel
theorem subd9_3_547 : subd9_3 [0, -4, -6] = true := by decide +kernel
theorem subd9_3_548 : subd9_3 [0, -4, -5] = true := by decide +kernel
theorem subd9_3_549 : subd9_3 [0, -4, -4] = true := by decide +kernel
theorem subd9_3_550 : subd9_3 [0, -4, -3] = true := by decide +kernel
theorem subd9_3_551 : subd9_3 [0, -4, -2] = true := by decide +kernel
theorem subd9_3_552 : subd9_3 [0, -4, -1] = true := by decide +kernel
theorem subd9_3_553 : subd9_3 [0, -4, 0] = true := by decide +kernel
theorem subd9_3_554 : subd9_3 [0, -4, 1] = true := by decide +kernel
theorem subd9_3_555 : subd9_3 [0, -4, 2] = true := by decide +kernel
theorem subd9_3_556 : subd9_3 [0, -4, 3] = true := by decide +kernel
theorem subd9_3_557 : subd9_3 [0, -4, 4] = true := by decide +kernel
theorem subd9_3_558 : subd9_3 [0, -4, 5] = true := by decide +kernel
theorem subd9_3_559 : subd9_3 [0, -4, 6] = true := by decide +kernel
theorem subd9_3_560 : subd9_3 [0, -4, 7] = true := by decide +kernel
theorem subd9_3_561 : subd9_3 [0, -3, -9] = true := by decide +kernel
theorem subd9_3_562 : subd9_3 [0, -3, -8] = true := by decide +kernel
theorem subd9_3_563 : subd9_3 [0, -3, -7] = true := by decide +kernel
theorem subd9_3_564 : subd9_3 [0, -3, -6] = true := by decide +kernel
theorem subd9_3_565 : subd9_3 [0, -3, -5] = true := by decide +kernel
theorem subd9_3_566 : subd9_3 [0, -3, -4] = true := by decide +kernel
theorem subd9_3_567 : subd9_3 [0, -3, -3] = true := by decide +kernel
theorem subd9_3_568 : subd9_3 [0, -3, -2] = true := by decide +kernel
theorem subd9_3_569 : subd9_3 [0, -3, -1] = true := by decide +kernel
theorem subd9_3_570 : subd9_3 [0, -3, 0] = true := by decide +kernel
theorem subd9_3_571 : subd9_3 [0, -3, 1] = true := by decide +kernel
theorem subd9_3_572 : subd9_3 [0, -3, 2] = true := by decide +kernel
theorem subd9_3_573 : subd9_3 [0, -3, 3] = true := by decide +kernel
theorem subd9_3_574 : subd9_3 [0, -3, 4] = true := by decide +kernel
theorem subd9_3_575 : subd9_3 [0, -3, 5] = true := by decide +kernel
theorem sbd9_3_17 : ∀ q ∈ blkd9_3_17, subd9_3 q = true := by
  unfold blkd9_3_17
  exact List.forall_mem_cons.2 ⟨subd9_3_544, List.forall_mem_cons.2 ⟨subd9_3_545, List.forall_mem_cons.2 ⟨subd9_3_546, List.forall_mem_cons.2 ⟨subd9_3_547, List.forall_mem_cons.2 ⟨subd9_3_548, List.forall_mem_cons.2 ⟨subd9_3_549, List.forall_mem_cons.2 ⟨subd9_3_550, List.forall_mem_cons.2 ⟨subd9_3_551, List.forall_mem_cons.2 ⟨subd9_3_552, List.forall_mem_cons.2 ⟨subd9_3_553, List.forall_mem_cons.2 ⟨subd9_3_554, List.forall_mem_cons.2 ⟨subd9_3_555, List.forall_mem_cons.2 ⟨subd9_3_556, List.forall_mem_cons.2 ⟨subd9_3_557, List.forall_mem_cons.2 ⟨subd9_3_558, List.forall_mem_cons.2 ⟨subd9_3_559, List.forall_mem_cons.2 ⟨subd9_3_560, List.forall_mem_cons.2 ⟨subd9_3_561, List.forall_mem_cons.2 ⟨subd9_3_562, List.forall_mem_cons.2 ⟨subd9_3_563, List.forall_mem_cons.2 ⟨subd9_3_564, List.forall_mem_cons.2 ⟨subd9_3_565, List.forall_mem_cons.2 ⟨subd9_3_566, List.forall_mem_cons.2 ⟨subd9_3_567, List.forall_mem_cons.2 ⟨subd9_3_568, List.forall_mem_cons.2 ⟨subd9_3_569, List.forall_mem_cons.2 ⟨subd9_3_570, List.forall_mem_cons.2 ⟨subd9_3_571, List.forall_mem_cons.2 ⟨subd9_3_572, List.forall_mem_cons.2 ⟨subd9_3_573, List.forall_mem_cons.2 ⟨subd9_3_574, List.forall_mem_cons.2 ⟨subd9_3_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_576 : subd9_3 [0, -3, 6] = true := by decide +kernel
theorem subd9_3_577 : subd9_3 [0, -3, 7] = true := by decide +kernel
theorem subd9_3_578 : subd9_3 [0, -3, 8] = true := by decide +kernel
theorem subd9_3_579 : subd9_3 [0, -2, -10] = true := by decide +kernel
theorem subd9_3_580 : subd9_3 [0, -2, -9] = true := by decide +kernel
theorem subd9_3_581 : subd9_3 [0, -2, -8] = true := by decide +kernel
theorem subd9_3_582 : subd9_3 [0, -2, -7] = true := by decide +kernel
theorem subd9_3_583 : subd9_3 [0, -2, -6] = true := by decide +kernel
theorem subd9_3_584 : subd9_3 [0, -2, -5] = true := by decide +kernel
theorem subd9_3_585 : subd9_3 [0, -2, -4] = true := by decide +kernel
theorem subd9_3_586 : subd9_3 [0, -2, -3] = true := by decide +kernel
theorem subd9_3_587 : subd9_3 [0, -2, -2] = true := by decide +kernel
theorem subd9_3_588 : subd9_3 [0, -2, -1] = true := by decide +kernel
theorem subd9_3_589 : subd9_3 [0, -2, 0] = true := by decide +kernel
theorem subd9_3_590 : subd9_3 [0, -2, 1] = true := by decide +kernel
theorem subd9_3_591 : subd9_3 [0, -2, 2] = true := by decide +kernel
theorem subd9_3_592 : subd9_3 [0, -2, 3] = true := by decide +kernel
theorem subd9_3_593 : subd9_3 [0, -2, 4] = true := by decide +kernel
theorem subd9_3_594 : subd9_3 [0, -2, 5] = true := by decide +kernel
theorem subd9_3_595 : subd9_3 [0, -2, 6] = true := by decide +kernel
theorem subd9_3_596 : subd9_3 [0, -2, 7] = true := by decide +kernel
theorem subd9_3_597 : subd9_3 [0, -2, 8] = true := by decide +kernel
theorem subd9_3_598 : subd9_3 [0, -2, 9] = true := by decide +kernel
theorem subd9_3_599 : subd9_3 [0, -1, -10] = true := by decide +kernel
theorem subd9_3_600 : subd9_3 [0, -1, -9] = true := by decide +kernel
theorem subd9_3_601 : subd9_3 [0, -1, -8] = true := by decide +kernel
theorem subd9_3_602 : subd9_3 [0, -1, -7] = true := by decide +kernel
theorem subd9_3_603 : subd9_3 [0, -1, -6] = true := by decide +kernel
theorem subd9_3_604 : subd9_3 [0, -1, -5] = true := by decide +kernel
theorem subd9_3_605 : subd9_3 [0, -1, -4] = true := by decide +kernel
theorem subd9_3_606 : subd9_3 [0, -1, -3] = true := by decide +kernel
theorem subd9_3_607 : subd9_3 [0, -1, -2] = true := by decide +kernel
theorem sbd9_3_18 : ∀ q ∈ blkd9_3_18, subd9_3 q = true := by
  unfold blkd9_3_18
  exact List.forall_mem_cons.2 ⟨subd9_3_576, List.forall_mem_cons.2 ⟨subd9_3_577, List.forall_mem_cons.2 ⟨subd9_3_578, List.forall_mem_cons.2 ⟨subd9_3_579, List.forall_mem_cons.2 ⟨subd9_3_580, List.forall_mem_cons.2 ⟨subd9_3_581, List.forall_mem_cons.2 ⟨subd9_3_582, List.forall_mem_cons.2 ⟨subd9_3_583, List.forall_mem_cons.2 ⟨subd9_3_584, List.forall_mem_cons.2 ⟨subd9_3_585, List.forall_mem_cons.2 ⟨subd9_3_586, List.forall_mem_cons.2 ⟨subd9_3_587, List.forall_mem_cons.2 ⟨subd9_3_588, List.forall_mem_cons.2 ⟨subd9_3_589, List.forall_mem_cons.2 ⟨subd9_3_590, List.forall_mem_cons.2 ⟨subd9_3_591, List.forall_mem_cons.2 ⟨subd9_3_592, List.forall_mem_cons.2 ⟨subd9_3_593, List.forall_mem_cons.2 ⟨subd9_3_594, List.forall_mem_cons.2 ⟨subd9_3_595, List.forall_mem_cons.2 ⟨subd9_3_596, List.forall_mem_cons.2 ⟨subd9_3_597, List.forall_mem_cons.2 ⟨subd9_3_598, List.forall_mem_cons.2 ⟨subd9_3_599, List.forall_mem_cons.2 ⟨subd9_3_600, List.forall_mem_cons.2 ⟨subd9_3_601, List.forall_mem_cons.2 ⟨subd9_3_602, List.forall_mem_cons.2 ⟨subd9_3_603, List.forall_mem_cons.2 ⟨subd9_3_604, List.forall_mem_cons.2 ⟨subd9_3_605, List.forall_mem_cons.2 ⟨subd9_3_606, List.forall_mem_cons.2 ⟨subd9_3_607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_608 : subd9_3 [0, -1, -1] = true := by decide +kernel
theorem subd9_3_609 : subd9_3 [0, -1, 0] = true := by decide +kernel
theorem subd9_3_610 : subd9_3 [0, -1, 1] = true := by decide +kernel
theorem subd9_3_611 : subd9_3 [0, -1, 2] = true := by decide +kernel
theorem subd9_3_612 : subd9_3 [0, -1, 3] = true := by decide +kernel
theorem subd9_3_613 : subd9_3 [0, -1, 4] = true := by decide +kernel
theorem subd9_3_614 : subd9_3 [0, -1, 5] = true := by decide +kernel
theorem subd9_3_615 : subd9_3 [0, -1, 6] = true := by decide +kernel
theorem subd9_3_616 : subd9_3 [0, -1, 7] = true := by decide +kernel
theorem subd9_3_617 : subd9_3 [0, -1, 8] = true := by decide +kernel
theorem subd9_3_618 : subd9_3 [0, -1, 9] = true := by decide +kernel
theorem subd9_3_619 : subd9_3 [0, 0, -10] = true := by decide +kernel
theorem subd9_3_620 : subd9_3 [0, 0, -9] = true := by decide +kernel
theorem subd9_3_621 : subd9_3 [0, 0, -8] = true := by decide +kernel
theorem subd9_3_622 : subd9_3 [0, 0, -7] = true := by decide +kernel
theorem subd9_3_623 : subd9_3 [0, 0, -6] = true := by decide +kernel
theorem subd9_3_624 : subd9_3 [0, 0, -5] = true := by decide +kernel
theorem subd9_3_625 : subd9_3 [0, 0, -4] = true := by decide +kernel
theorem subd9_3_626 : subd9_3 [0, 0, -3] = true := by decide +kernel
theorem subd9_3_627 : subd9_3 [0, 0, -2] = true := by decide +kernel
theorem subd9_3_628 : subd9_3 [0, 0, -1] = true := by decide +kernel
theorem subd9_3_629 : subd9_3 [0, 0, 0] = true := by decide +kernel
theorem subd9_3_630 : subd9_3 [0, 0, 1] = true := by decide +kernel
theorem subd9_3_631 : subd9_3 [0, 0, 2] = true := by decide +kernel
theorem subd9_3_632 : subd9_3 [0, 0, 3] = true := by decide +kernel
theorem subd9_3_633 : subd9_3 [0, 0, 4] = true := by decide +kernel
theorem subd9_3_634 : subd9_3 [0, 0, 5] = true := by decide +kernel
theorem subd9_3_635 : subd9_3 [0, 0, 6] = true := by decide +kernel
theorem subd9_3_636 : subd9_3 [0, 0, 7] = true := by decide +kernel
theorem subd9_3_637 : subd9_3 [0, 0, 8] = true := by decide +kernel
theorem subd9_3_638 : subd9_3 [0, 0, 9] = true := by decide +kernel
theorem subd9_3_639 : subd9_3 [0, 1, -10] = true := by decide +kernel
theorem sbd9_3_19 : ∀ q ∈ blkd9_3_19, subd9_3 q = true := by
  unfold blkd9_3_19
  exact List.forall_mem_cons.2 ⟨subd9_3_608, List.forall_mem_cons.2 ⟨subd9_3_609, List.forall_mem_cons.2 ⟨subd9_3_610, List.forall_mem_cons.2 ⟨subd9_3_611, List.forall_mem_cons.2 ⟨subd9_3_612, List.forall_mem_cons.2 ⟨subd9_3_613, List.forall_mem_cons.2 ⟨subd9_3_614, List.forall_mem_cons.2 ⟨subd9_3_615, List.forall_mem_cons.2 ⟨subd9_3_616, List.forall_mem_cons.2 ⟨subd9_3_617, List.forall_mem_cons.2 ⟨subd9_3_618, List.forall_mem_cons.2 ⟨subd9_3_619, List.forall_mem_cons.2 ⟨subd9_3_620, List.forall_mem_cons.2 ⟨subd9_3_621, List.forall_mem_cons.2 ⟨subd9_3_622, List.forall_mem_cons.2 ⟨subd9_3_623, List.forall_mem_cons.2 ⟨subd9_3_624, List.forall_mem_cons.2 ⟨subd9_3_625, List.forall_mem_cons.2 ⟨subd9_3_626, List.forall_mem_cons.2 ⟨subd9_3_627, List.forall_mem_cons.2 ⟨subd9_3_628, List.forall_mem_cons.2 ⟨subd9_3_629, List.forall_mem_cons.2 ⟨subd9_3_630, List.forall_mem_cons.2 ⟨subd9_3_631, List.forall_mem_cons.2 ⟨subd9_3_632, List.forall_mem_cons.2 ⟨subd9_3_633, List.forall_mem_cons.2 ⟨subd9_3_634, List.forall_mem_cons.2 ⟨subd9_3_635, List.forall_mem_cons.2 ⟨subd9_3_636, List.forall_mem_cons.2 ⟨subd9_3_637, List.forall_mem_cons.2 ⟨subd9_3_638, List.forall_mem_cons.2 ⟨subd9_3_639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_640 : subd9_3 [0, 1, -9] = true := by decide +kernel
theorem subd9_3_641 : subd9_3 [0, 1, -8] = true := by decide +kernel
theorem subd9_3_642 : subd9_3 [0, 1, -7] = true := by decide +kernel
theorem subd9_3_643 : subd9_3 [0, 1, -6] = true := by decide +kernel
theorem subd9_3_644 : subd9_3 [0, 1, -5] = true := by decide +kernel
theorem subd9_3_645 : subd9_3 [0, 1, -4] = true := by decide +kernel
theorem subd9_3_646 : subd9_3 [0, 1, -3] = true := by decide +kernel
theorem subd9_3_647 : subd9_3 [0, 1, -2] = true := by decide +kernel
theorem subd9_3_648 : subd9_3 [0, 1, -1] = true := by decide +kernel
theorem subd9_3_649 : subd9_3 [0, 1, 0] = true := by decide +kernel
theorem subd9_3_650 : subd9_3 [0, 1, 1] = true := by decide +kernel
theorem subd9_3_651 : subd9_3 [0, 1, 2] = true := by decide +kernel
theorem subd9_3_652 : subd9_3 [0, 1, 3] = true := by decide +kernel
theorem subd9_3_653 : subd9_3 [0, 1, 4] = true := by decide +kernel
theorem subd9_3_654 : subd9_3 [0, 1, 5] = true := by decide +kernel
theorem subd9_3_655 : subd9_3 [0, 1, 6] = true := by decide +kernel
theorem subd9_3_656 : subd9_3 [0, 1, 7] = true := by decide +kernel
theorem subd9_3_657 : subd9_3 [0, 1, 8] = true := by decide +kernel
theorem subd9_3_658 : subd9_3 [0, 1, 9] = true := by decide +kernel
theorem subd9_3_659 : subd9_3 [0, 2, -10] = true := by decide +kernel
theorem subd9_3_660 : subd9_3 [0, 2, -9] = true := by decide +kernel
theorem subd9_3_661 : subd9_3 [0, 2, -8] = true := by decide +kernel
theorem subd9_3_662 : subd9_3 [0, 2, -7] = true := by decide +kernel
theorem subd9_3_663 : subd9_3 [0, 2, -6] = true := by decide +kernel
theorem subd9_3_664 : subd9_3 [0, 2, -5] = true := by decide +kernel
theorem subd9_3_665 : subd9_3 [0, 2, -4] = true := by decide +kernel
theorem subd9_3_666 : subd9_3 [0, 2, -3] = true := by decide +kernel
theorem subd9_3_667 : subd9_3 [0, 2, -2] = true := by decide +kernel
theorem subd9_3_668 : subd9_3 [0, 2, -1] = true := by decide +kernel
theorem subd9_3_669 : subd9_3 [0, 2, 0] = true := by decide +kernel
theorem subd9_3_670 : subd9_3 [0, 2, 1] = true := by decide +kernel
theorem subd9_3_671 : subd9_3 [0, 2, 2] = true := by decide +kernel
theorem sbd9_3_20 : ∀ q ∈ blkd9_3_20, subd9_3 q = true := by
  unfold blkd9_3_20
  exact List.forall_mem_cons.2 ⟨subd9_3_640, List.forall_mem_cons.2 ⟨subd9_3_641, List.forall_mem_cons.2 ⟨subd9_3_642, List.forall_mem_cons.2 ⟨subd9_3_643, List.forall_mem_cons.2 ⟨subd9_3_644, List.forall_mem_cons.2 ⟨subd9_3_645, List.forall_mem_cons.2 ⟨subd9_3_646, List.forall_mem_cons.2 ⟨subd9_3_647, List.forall_mem_cons.2 ⟨subd9_3_648, List.forall_mem_cons.2 ⟨subd9_3_649, List.forall_mem_cons.2 ⟨subd9_3_650, List.forall_mem_cons.2 ⟨subd9_3_651, List.forall_mem_cons.2 ⟨subd9_3_652, List.forall_mem_cons.2 ⟨subd9_3_653, List.forall_mem_cons.2 ⟨subd9_3_654, List.forall_mem_cons.2 ⟨subd9_3_655, List.forall_mem_cons.2 ⟨subd9_3_656, List.forall_mem_cons.2 ⟨subd9_3_657, List.forall_mem_cons.2 ⟨subd9_3_658, List.forall_mem_cons.2 ⟨subd9_3_659, List.forall_mem_cons.2 ⟨subd9_3_660, List.forall_mem_cons.2 ⟨subd9_3_661, List.forall_mem_cons.2 ⟨subd9_3_662, List.forall_mem_cons.2 ⟨subd9_3_663, List.forall_mem_cons.2 ⟨subd9_3_664, List.forall_mem_cons.2 ⟨subd9_3_665, List.forall_mem_cons.2 ⟨subd9_3_666, List.forall_mem_cons.2 ⟨subd9_3_667, List.forall_mem_cons.2 ⟨subd9_3_668, List.forall_mem_cons.2 ⟨subd9_3_669, List.forall_mem_cons.2 ⟨subd9_3_670, List.forall_mem_cons.2 ⟨subd9_3_671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_672 : subd9_3 [0, 2, 3] = true := by decide +kernel
theorem subd9_3_673 : subd9_3 [0, 2, 4] = true := by decide +kernel
theorem subd9_3_674 : subd9_3 [0, 2, 5] = true := by decide +kernel
theorem subd9_3_675 : subd9_3 [0, 2, 6] = true := by decide +kernel
theorem subd9_3_676 : subd9_3 [0, 2, 7] = true := by decide +kernel
theorem subd9_3_677 : subd9_3 [0, 2, 8] = true := by decide +kernel
theorem subd9_3_678 : subd9_3 [0, 2, 9] = true := by decide +kernel
theorem subd9_3_679 : subd9_3 [0, 3, -9] = true := by decide +kernel
theorem subd9_3_680 : subd9_3 [0, 3, -8] = true := by decide +kernel
theorem subd9_3_681 : subd9_3 [0, 3, -7] = true := by decide +kernel
theorem subd9_3_682 : subd9_3 [0, 3, -6] = true := by decide +kernel
theorem subd9_3_683 : subd9_3 [0, 3, -5] = true := by decide +kernel
theorem subd9_3_684 : subd9_3 [0, 3, -4] = true := by decide +kernel
theorem subd9_3_685 : subd9_3 [0, 3, -3] = true := by decide +kernel
theorem subd9_3_686 : subd9_3 [0, 3, -2] = true := by decide +kernel
theorem subd9_3_687 : subd9_3 [0, 3, -1] = true := by decide +kernel
theorem subd9_3_688 : subd9_3 [0, 3, 0] = true := by decide +kernel
theorem subd9_3_689 : subd9_3 [0, 3, 1] = true := by decide +kernel
theorem subd9_3_690 : subd9_3 [0, 3, 2] = true := by decide +kernel
theorem subd9_3_691 : subd9_3 [0, 3, 3] = true := by decide +kernel
theorem subd9_3_692 : subd9_3 [0, 3, 4] = true := by decide +kernel
theorem subd9_3_693 : subd9_3 [0, 3, 5] = true := by decide +kernel
theorem subd9_3_694 : subd9_3 [0, 3, 6] = true := by decide +kernel
theorem subd9_3_695 : subd9_3 [0, 3, 7] = true := by decide +kernel
theorem subd9_3_696 : subd9_3 [0, 3, 8] = true := by decide +kernel
theorem subd9_3_697 : subd9_3 [0, 4, -8] = true := by decide +kernel
theorem subd9_3_698 : subd9_3 [0, 4, -7] = true := by decide +kernel
theorem subd9_3_699 : subd9_3 [0, 4, -6] = true := by decide +kernel
theorem subd9_3_700 : subd9_3 [0, 4, -5] = true := by decide +kernel
theorem subd9_3_701 : subd9_3 [0, 4, -4] = true := by decide +kernel
theorem subd9_3_702 : subd9_3 [0, 4, -3] = true := by decide +kernel
theorem subd9_3_703 : subd9_3 [0, 4, -2] = true := by decide +kernel
theorem sbd9_3_21 : ∀ q ∈ blkd9_3_21, subd9_3 q = true := by
  unfold blkd9_3_21
  exact List.forall_mem_cons.2 ⟨subd9_3_672, List.forall_mem_cons.2 ⟨subd9_3_673, List.forall_mem_cons.2 ⟨subd9_3_674, List.forall_mem_cons.2 ⟨subd9_3_675, List.forall_mem_cons.2 ⟨subd9_3_676, List.forall_mem_cons.2 ⟨subd9_3_677, List.forall_mem_cons.2 ⟨subd9_3_678, List.forall_mem_cons.2 ⟨subd9_3_679, List.forall_mem_cons.2 ⟨subd9_3_680, List.forall_mem_cons.2 ⟨subd9_3_681, List.forall_mem_cons.2 ⟨subd9_3_682, List.forall_mem_cons.2 ⟨subd9_3_683, List.forall_mem_cons.2 ⟨subd9_3_684, List.forall_mem_cons.2 ⟨subd9_3_685, List.forall_mem_cons.2 ⟨subd9_3_686, List.forall_mem_cons.2 ⟨subd9_3_687, List.forall_mem_cons.2 ⟨subd9_3_688, List.forall_mem_cons.2 ⟨subd9_3_689, List.forall_mem_cons.2 ⟨subd9_3_690, List.forall_mem_cons.2 ⟨subd9_3_691, List.forall_mem_cons.2 ⟨subd9_3_692, List.forall_mem_cons.2 ⟨subd9_3_693, List.forall_mem_cons.2 ⟨subd9_3_694, List.forall_mem_cons.2 ⟨subd9_3_695, List.forall_mem_cons.2 ⟨subd9_3_696, List.forall_mem_cons.2 ⟨subd9_3_697, List.forall_mem_cons.2 ⟨subd9_3_698, List.forall_mem_cons.2 ⟨subd9_3_699, List.forall_mem_cons.2 ⟨subd9_3_700, List.forall_mem_cons.2 ⟨subd9_3_701, List.forall_mem_cons.2 ⟨subd9_3_702, List.forall_mem_cons.2 ⟨subd9_3_703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_704 : subd9_3 [0, 4, -1] = true := by decide +kernel
theorem subd9_3_705 : subd9_3 [0, 4, 0] = true := by decide +kernel
theorem subd9_3_706 : subd9_3 [0, 4, 1] = true := by decide +kernel
theorem subd9_3_707 : subd9_3 [0, 4, 2] = true := by decide +kernel
theorem subd9_3_708 : subd9_3 [0, 4, 3] = true := by decide +kernel
theorem subd9_3_709 : subd9_3 [0, 4, 4] = true := by decide +kernel
theorem subd9_3_710 : subd9_3 [0, 4, 5] = true := by decide +kernel
theorem subd9_3_711 : subd9_3 [0, 4, 6] = true := by decide +kernel
theorem subd9_3_712 : subd9_3 [0, 4, 7] = true := by decide +kernel
theorem subd9_3_713 : subd9_3 [0, 5] = true := by decide +kernel
theorem subd9_3_714 : subd9_3 [0, 6] = true := by decide +kernel
theorem subd9_3_715 : subd9_3 [1, -7] = true := by decide +kernel
theorem subd9_3_716 : subd9_3 [1, -6] = true := by decide +kernel
theorem subd9_3_717 : subd9_3 [1, -5] = true := by decide +kernel
theorem subd9_3_718 : subd9_3 [1, -4, -8] = true := by decide +kernel
theorem subd9_3_719 : subd9_3 [1, -4, -7] = true := by decide +kernel
theorem subd9_3_720 : subd9_3 [1, -4, -6] = true := by decide +kernel
theorem subd9_3_721 : subd9_3 [1, -4, -5] = true := by decide +kernel
theorem subd9_3_722 : subd9_3 [1, -4, -4] = true := by decide +kernel
theorem subd9_3_723 : subd9_3 [1, -4, -3] = true := by decide +kernel
theorem subd9_3_724 : subd9_3 [1, -4, -2] = true := by decide +kernel
theorem subd9_3_725 : subd9_3 [1, -4, -1] = true := by decide +kernel
theorem subd9_3_726 : subd9_3 [1, -4, 0] = true := by decide +kernel
theorem subd9_3_727 : subd9_3 [1, -4, 1] = true := by decide +kernel
theorem subd9_3_728 : subd9_3 [1, -4, 2] = true := by decide +kernel
theorem subd9_3_729 : subd9_3 [1, -4, 3] = true := by decide +kernel
theorem subd9_3_730 : subd9_3 [1, -4, 4] = true := by decide +kernel
theorem subd9_3_731 : subd9_3 [1, -4, 5] = true := by decide +kernel
theorem subd9_3_732 : subd9_3 [1, -4, 6] = true := by decide +kernel
theorem subd9_3_733 : subd9_3 [1, -4, 7] = true := by decide +kernel
theorem subd9_3_734 : subd9_3 [1, -3, -9] = true := by decide +kernel
theorem subd9_3_735 : subd9_3 [1, -3, -8] = true := by decide +kernel
theorem sbd9_3_22 : ∀ q ∈ blkd9_3_22, subd9_3 q = true := by
  unfold blkd9_3_22
  exact List.forall_mem_cons.2 ⟨subd9_3_704, List.forall_mem_cons.2 ⟨subd9_3_705, List.forall_mem_cons.2 ⟨subd9_3_706, List.forall_mem_cons.2 ⟨subd9_3_707, List.forall_mem_cons.2 ⟨subd9_3_708, List.forall_mem_cons.2 ⟨subd9_3_709, List.forall_mem_cons.2 ⟨subd9_3_710, List.forall_mem_cons.2 ⟨subd9_3_711, List.forall_mem_cons.2 ⟨subd9_3_712, List.forall_mem_cons.2 ⟨subd9_3_713, List.forall_mem_cons.2 ⟨subd9_3_714, List.forall_mem_cons.2 ⟨subd9_3_715, List.forall_mem_cons.2 ⟨subd9_3_716, List.forall_mem_cons.2 ⟨subd9_3_717, List.forall_mem_cons.2 ⟨subd9_3_718, List.forall_mem_cons.2 ⟨subd9_3_719, List.forall_mem_cons.2 ⟨subd9_3_720, List.forall_mem_cons.2 ⟨subd9_3_721, List.forall_mem_cons.2 ⟨subd9_3_722, List.forall_mem_cons.2 ⟨subd9_3_723, List.forall_mem_cons.2 ⟨subd9_3_724, List.forall_mem_cons.2 ⟨subd9_3_725, List.forall_mem_cons.2 ⟨subd9_3_726, List.forall_mem_cons.2 ⟨subd9_3_727, List.forall_mem_cons.2 ⟨subd9_3_728, List.forall_mem_cons.2 ⟨subd9_3_729, List.forall_mem_cons.2 ⟨subd9_3_730, List.forall_mem_cons.2 ⟨subd9_3_731, List.forall_mem_cons.2 ⟨subd9_3_732, List.forall_mem_cons.2 ⟨subd9_3_733, List.forall_mem_cons.2 ⟨subd9_3_734, List.forall_mem_cons.2 ⟨subd9_3_735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_736 : subd9_3 [1, -3, -7] = true := by decide +kernel
theorem subd9_3_737 : subd9_3 [1, -3, -6] = true := by decide +kernel
theorem subd9_3_738 : subd9_3 [1, -3, -5] = true := by decide +kernel
theorem subd9_3_739 : subd9_3 [1, -3, -4] = true := by decide +kernel
theorem subd9_3_740 : subd9_3 [1, -3, -3] = true := by decide +kernel
theorem subd9_3_741 : subd9_3 [1, -3, -2] = true := by decide +kernel
theorem subd9_3_742 : subd9_3 [1, -3, -1] = true := by decide +kernel
theorem subd9_3_743 : subd9_3 [1, -3, 0] = true := by decide +kernel
theorem subd9_3_744 : subd9_3 [1, -3, 1] = true := by decide +kernel
theorem subd9_3_745 : subd9_3 [1, -3, 2] = true := by decide +kernel
theorem subd9_3_746 : subd9_3 [1, -3, 3] = true := by decide +kernel
theorem subd9_3_747 : subd9_3 [1, -3, 4] = true := by decide +kernel
theorem subd9_3_748 : subd9_3 [1, -3, 5] = true := by decide +kernel
theorem subd9_3_749 : subd9_3 [1, -3, 6] = true := by decide +kernel
theorem subd9_3_750 : subd9_3 [1, -3, 7] = true := by decide +kernel
theorem subd9_3_751 : subd9_3 [1, -3, 8] = true := by decide +kernel
theorem subd9_3_752 : subd9_3 [1, -2, -10] = true := by decide +kernel
theorem subd9_3_753 : subd9_3 [1, -2, -9] = true := by decide +kernel
theorem subd9_3_754 : subd9_3 [1, -2, -8] = true := by decide +kernel
theorem subd9_3_755 : subd9_3 [1, -2, -7] = true := by decide +kernel
theorem subd9_3_756 : subd9_3 [1, -2, -6] = true := by decide +kernel
theorem subd9_3_757 : subd9_3 [1, -2, -5] = true := by decide +kernel
theorem subd9_3_758 : subd9_3 [1, -2, -4] = true := by decide +kernel
theorem subd9_3_759 : subd9_3 [1, -2, -3] = true := by decide +kernel
theorem subd9_3_760 : subd9_3 [1, -2, -2] = true := by decide +kernel
theorem subd9_3_761 : subd9_3 [1, -2, -1] = true := by decide +kernel
theorem subd9_3_762 : subd9_3 [1, -2, 0] = true := by decide +kernel
theorem subd9_3_763 : subd9_3 [1, -2, 1] = true := by decide +kernel
theorem subd9_3_764 : subd9_3 [1, -2, 2] = true := by decide +kernel
theorem subd9_3_765 : subd9_3 [1, -2, 3] = true := by decide +kernel
theorem subd9_3_766 : subd9_3 [1, -2, 4] = true := by decide +kernel
theorem subd9_3_767 : subd9_3 [1, -2, 5] = true := by decide +kernel
theorem sbd9_3_23 : ∀ q ∈ blkd9_3_23, subd9_3 q = true := by
  unfold blkd9_3_23
  exact List.forall_mem_cons.2 ⟨subd9_3_736, List.forall_mem_cons.2 ⟨subd9_3_737, List.forall_mem_cons.2 ⟨subd9_3_738, List.forall_mem_cons.2 ⟨subd9_3_739, List.forall_mem_cons.2 ⟨subd9_3_740, List.forall_mem_cons.2 ⟨subd9_3_741, List.forall_mem_cons.2 ⟨subd9_3_742, List.forall_mem_cons.2 ⟨subd9_3_743, List.forall_mem_cons.2 ⟨subd9_3_744, List.forall_mem_cons.2 ⟨subd9_3_745, List.forall_mem_cons.2 ⟨subd9_3_746, List.forall_mem_cons.2 ⟨subd9_3_747, List.forall_mem_cons.2 ⟨subd9_3_748, List.forall_mem_cons.2 ⟨subd9_3_749, List.forall_mem_cons.2 ⟨subd9_3_750, List.forall_mem_cons.2 ⟨subd9_3_751, List.forall_mem_cons.2 ⟨subd9_3_752, List.forall_mem_cons.2 ⟨subd9_3_753, List.forall_mem_cons.2 ⟨subd9_3_754, List.forall_mem_cons.2 ⟨subd9_3_755, List.forall_mem_cons.2 ⟨subd9_3_756, List.forall_mem_cons.2 ⟨subd9_3_757, List.forall_mem_cons.2 ⟨subd9_3_758, List.forall_mem_cons.2 ⟨subd9_3_759, List.forall_mem_cons.2 ⟨subd9_3_760, List.forall_mem_cons.2 ⟨subd9_3_761, List.forall_mem_cons.2 ⟨subd9_3_762, List.forall_mem_cons.2 ⟨subd9_3_763, List.forall_mem_cons.2 ⟨subd9_3_764, List.forall_mem_cons.2 ⟨subd9_3_765, List.forall_mem_cons.2 ⟨subd9_3_766, List.forall_mem_cons.2 ⟨subd9_3_767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_768 : subd9_3 [1, -2, 6] = true := by decide +kernel
theorem subd9_3_769 : subd9_3 [1, -2, 7] = true := by decide +kernel
theorem subd9_3_770 : subd9_3 [1, -2, 8] = true := by decide +kernel
theorem subd9_3_771 : subd9_3 [1, -2, 9] = true := by decide +kernel
theorem subd9_3_772 : subd9_3 [1, -1, -10] = true := by decide +kernel
theorem subd9_3_773 : subd9_3 [1, -1, -9] = true := by decide +kernel
theorem subd9_3_774 : subd9_3 [1, -1, -8] = true := by decide +kernel
theorem subd9_3_775 : subd9_3 [1, -1, -7] = true := by decide +kernel
theorem subd9_3_776 : subd9_3 [1, -1, -6] = true := by decide +kernel
theorem subd9_3_777 : subd9_3 [1, -1, -5] = true := by decide +kernel
theorem subd9_3_778 : subd9_3 [1, -1, -4] = true := by decide +kernel
theorem subd9_3_779 : subd9_3 [1, -1, -3] = true := by decide +kernel
theorem subd9_3_780 : subd9_3 [1, -1, -2] = true := by decide +kernel
theorem subd9_3_781 : subd9_3 [1, -1, -1] = true := by decide +kernel
theorem subd9_3_782 : subd9_3 [1, -1, 0] = true := by decide +kernel
theorem subd9_3_783 : subd9_3 [1, -1, 1] = true := by decide +kernel
theorem subd9_3_784 : subd9_3 [1, -1, 2] = true := by decide +kernel
theorem subd9_3_785 : subd9_3 [1, -1, 3] = true := by decide +kernel
theorem subd9_3_786 : subd9_3 [1, -1, 4] = true := by decide +kernel
theorem subd9_3_787 : subd9_3 [1, -1, 5] = true := by decide +kernel
theorem subd9_3_788 : subd9_3 [1, -1, 6] = true := by decide +kernel
theorem subd9_3_789 : subd9_3 [1, -1, 7] = true := by decide +kernel
theorem subd9_3_790 : subd9_3 [1, -1, 8] = true := by decide +kernel
theorem subd9_3_791 : subd9_3 [1, -1, 9] = true := by decide +kernel
theorem subd9_3_792 : subd9_3 [1, 0, -10] = true := by decide +kernel
theorem subd9_3_793 : subd9_3 [1, 0, -9] = true := by decide +kernel
theorem subd9_3_794 : subd9_3 [1, 0, -8] = true := by decide +kernel
theorem subd9_3_795 : subd9_3 [1, 0, -7] = true := by decide +kernel
theorem subd9_3_796 : subd9_3 [1, 0, -6] = true := by decide +kernel
theorem subd9_3_797 : subd9_3 [1, 0, -5] = true := by decide +kernel
theorem subd9_3_798 : subd9_3 [1, 0, -4] = true := by decide +kernel
theorem subd9_3_799 : subd9_3 [1, 0, -3] = true := by decide +kernel
theorem sbd9_3_24 : ∀ q ∈ blkd9_3_24, subd9_3 q = true := by
  unfold blkd9_3_24
  exact List.forall_mem_cons.2 ⟨subd9_3_768, List.forall_mem_cons.2 ⟨subd9_3_769, List.forall_mem_cons.2 ⟨subd9_3_770, List.forall_mem_cons.2 ⟨subd9_3_771, List.forall_mem_cons.2 ⟨subd9_3_772, List.forall_mem_cons.2 ⟨subd9_3_773, List.forall_mem_cons.2 ⟨subd9_3_774, List.forall_mem_cons.2 ⟨subd9_3_775, List.forall_mem_cons.2 ⟨subd9_3_776, List.forall_mem_cons.2 ⟨subd9_3_777, List.forall_mem_cons.2 ⟨subd9_3_778, List.forall_mem_cons.2 ⟨subd9_3_779, List.forall_mem_cons.2 ⟨subd9_3_780, List.forall_mem_cons.2 ⟨subd9_3_781, List.forall_mem_cons.2 ⟨subd9_3_782, List.forall_mem_cons.2 ⟨subd9_3_783, List.forall_mem_cons.2 ⟨subd9_3_784, List.forall_mem_cons.2 ⟨subd9_3_785, List.forall_mem_cons.2 ⟨subd9_3_786, List.forall_mem_cons.2 ⟨subd9_3_787, List.forall_mem_cons.2 ⟨subd9_3_788, List.forall_mem_cons.2 ⟨subd9_3_789, List.forall_mem_cons.2 ⟨subd9_3_790, List.forall_mem_cons.2 ⟨subd9_3_791, List.forall_mem_cons.2 ⟨subd9_3_792, List.forall_mem_cons.2 ⟨subd9_3_793, List.forall_mem_cons.2 ⟨subd9_3_794, List.forall_mem_cons.2 ⟨subd9_3_795, List.forall_mem_cons.2 ⟨subd9_3_796, List.forall_mem_cons.2 ⟨subd9_3_797, List.forall_mem_cons.2 ⟨subd9_3_798, List.forall_mem_cons.2 ⟨subd9_3_799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_800 : subd9_3 [1, 0, -2] = true := by decide +kernel
theorem subd9_3_801 : subd9_3 [1, 0, -1] = true := by decide +kernel
theorem subd9_3_802 : subd9_3 [1, 0, 0] = true := by decide +kernel
theorem subd9_3_803 : subd9_3 [1, 0, 1] = true := by decide +kernel
theorem subd9_3_804 : subd9_3 [1, 0, 2] = true := by decide +kernel
theorem subd9_3_805 : subd9_3 [1, 0, 3] = true := by decide +kernel
theorem subd9_3_806 : subd9_3 [1, 0, 4] = true := by decide +kernel
theorem subd9_3_807 : subd9_3 [1, 0, 5] = true := by decide +kernel
theorem subd9_3_808 : subd9_3 [1, 0, 6] = true := by decide +kernel
theorem subd9_3_809 : subd9_3 [1, 0, 7] = true := by decide +kernel
theorem subd9_3_810 : subd9_3 [1, 0, 8] = true := by decide +kernel
theorem subd9_3_811 : subd9_3 [1, 0, 9] = true := by decide +kernel
theorem subd9_3_812 : subd9_3 [1, 1, -10] = true := by decide +kernel
theorem subd9_3_813 : subd9_3 [1, 1, -9] = true := by decide +kernel
theorem subd9_3_814 : subd9_3 [1, 1, -8] = true := by decide +kernel
theorem subd9_3_815 : subd9_3 [1, 1, -7] = true := by decide +kernel
theorem subd9_3_816 : subd9_3 [1, 1, -6] = true := by decide +kernel
theorem subd9_3_817 : subd9_3 [1, 1, -5] = true := by decide +kernel
theorem subd9_3_818 : subd9_3 [1, 1, -4] = true := by decide +kernel
theorem subd9_3_819 : subd9_3 [1, 1, -3] = true := by decide +kernel
theorem subd9_3_820 : subd9_3 [1, 1, -2] = true := by decide +kernel
theorem subd9_3_821 : subd9_3 [1, 1, -1] = true := by decide +kernel
theorem subd9_3_822 : subd9_3 [1, 1, 0] = true := by decide +kernel
theorem subd9_3_823 : subd9_3 [1, 1, 1] = true := by decide +kernel
theorem subd9_3_824 : subd9_3 [1, 1, 2] = true := by decide +kernel
theorem subd9_3_825 : subd9_3 [1, 1, 3] = true := by decide +kernel
theorem subd9_3_826 : subd9_3 [1, 1, 4] = true := by decide +kernel
theorem subd9_3_827 : subd9_3 [1, 1, 5] = true := by decide +kernel
theorem subd9_3_828 : subd9_3 [1, 1, 6] = true := by decide +kernel
theorem subd9_3_829 : subd9_3 [1, 1, 7] = true := by decide +kernel
theorem subd9_3_830 : subd9_3 [1, 1, 8] = true := by decide +kernel
theorem subd9_3_831 : subd9_3 [1, 1, 9] = true := by decide +kernel
theorem sbd9_3_25 : ∀ q ∈ blkd9_3_25, subd9_3 q = true := by
  unfold blkd9_3_25
  exact List.forall_mem_cons.2 ⟨subd9_3_800, List.forall_mem_cons.2 ⟨subd9_3_801, List.forall_mem_cons.2 ⟨subd9_3_802, List.forall_mem_cons.2 ⟨subd9_3_803, List.forall_mem_cons.2 ⟨subd9_3_804, List.forall_mem_cons.2 ⟨subd9_3_805, List.forall_mem_cons.2 ⟨subd9_3_806, List.forall_mem_cons.2 ⟨subd9_3_807, List.forall_mem_cons.2 ⟨subd9_3_808, List.forall_mem_cons.2 ⟨subd9_3_809, List.forall_mem_cons.2 ⟨subd9_3_810, List.forall_mem_cons.2 ⟨subd9_3_811, List.forall_mem_cons.2 ⟨subd9_3_812, List.forall_mem_cons.2 ⟨subd9_3_813, List.forall_mem_cons.2 ⟨subd9_3_814, List.forall_mem_cons.2 ⟨subd9_3_815, List.forall_mem_cons.2 ⟨subd9_3_816, List.forall_mem_cons.2 ⟨subd9_3_817, List.forall_mem_cons.2 ⟨subd9_3_818, List.forall_mem_cons.2 ⟨subd9_3_819, List.forall_mem_cons.2 ⟨subd9_3_820, List.forall_mem_cons.2 ⟨subd9_3_821, List.forall_mem_cons.2 ⟨subd9_3_822, List.forall_mem_cons.2 ⟨subd9_3_823, List.forall_mem_cons.2 ⟨subd9_3_824, List.forall_mem_cons.2 ⟨subd9_3_825, List.forall_mem_cons.2 ⟨subd9_3_826, List.forall_mem_cons.2 ⟨subd9_3_827, List.forall_mem_cons.2 ⟨subd9_3_828, List.forall_mem_cons.2 ⟨subd9_3_829, List.forall_mem_cons.2 ⟨subd9_3_830, List.forall_mem_cons.2 ⟨subd9_3_831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_832 : subd9_3 [1, 2, -9] = true := by decide +kernel
theorem subd9_3_833 : subd9_3 [1, 2, -8] = true := by decide +kernel
theorem subd9_3_834 : subd9_3 [1, 2, -7] = true := by decide +kernel
theorem subd9_3_835 : subd9_3 [1, 2, -6] = true := by decide +kernel
theorem subd9_3_836 : subd9_3 [1, 2, -5] = true := by decide +kernel
theorem subd9_3_837 : subd9_3 [1, 2, -4] = true := by decide +kernel
theorem subd9_3_838 : subd9_3 [1, 2, -3] = true := by decide +kernel
theorem subd9_3_839 : subd9_3 [1, 2, -2] = true := by decide +kernel
theorem subd9_3_840 : subd9_3 [1, 2, -1] = true := by decide +kernel
theorem subd9_3_841 : subd9_3 [1, 2, 0] = true := by decide +kernel
theorem subd9_3_842 : subd9_3 [1, 2, 1] = true := by decide +kernel
theorem subd9_3_843 : subd9_3 [1, 2, 2] = true := by decide +kernel
theorem subd9_3_844 : subd9_3 [1, 2, 3] = true := by decide +kernel
theorem subd9_3_845 : subd9_3 [1, 2, 4] = true := by decide +kernel
theorem subd9_3_846 : subd9_3 [1, 2, 5] = true := by decide +kernel
theorem subd9_3_847 : subd9_3 [1, 2, 6] = true := by decide +kernel
theorem subd9_3_848 : subd9_3 [1, 2, 7] = true := by decide +kernel
theorem subd9_3_849 : subd9_3 [1, 2, 8] = true := by decide +kernel
theorem subd9_3_850 : subd9_3 [1, 2, 9] = true := by decide +kernel
theorem subd9_3_851 : subd9_3 [1, 3, -9] = true := by decide +kernel
theorem subd9_3_852 : subd9_3 [1, 3, -8] = true := by decide +kernel
theorem subd9_3_853 : subd9_3 [1, 3, -7] = true := by decide +kernel
theorem subd9_3_854 : subd9_3 [1, 3, -6] = true := by decide +kernel
theorem subd9_3_855 : subd9_3 [1, 3, -5] = true := by decide +kernel
theorem subd9_3_856 : subd9_3 [1, 3, -4] = true := by decide +kernel
theorem subd9_3_857 : subd9_3 [1, 3, -3] = true := by decide +kernel
theorem subd9_3_858 : subd9_3 [1, 3, -2] = true := by decide +kernel
theorem subd9_3_859 : subd9_3 [1, 3, -1] = true := by decide +kernel
theorem subd9_3_860 : subd9_3 [1, 3, 0] = true := by decide +kernel
theorem subd9_3_861 : subd9_3 [1, 3, 1] = true := by decide +kernel
theorem subd9_3_862 : subd9_3 [1, 3, 2] = true := by decide +kernel
theorem subd9_3_863 : subd9_3 [1, 3, 3] = true := by decide +kernel
theorem sbd9_3_26 : ∀ q ∈ blkd9_3_26, subd9_3 q = true := by
  unfold blkd9_3_26
  exact List.forall_mem_cons.2 ⟨subd9_3_832, List.forall_mem_cons.2 ⟨subd9_3_833, List.forall_mem_cons.2 ⟨subd9_3_834, List.forall_mem_cons.2 ⟨subd9_3_835, List.forall_mem_cons.2 ⟨subd9_3_836, List.forall_mem_cons.2 ⟨subd9_3_837, List.forall_mem_cons.2 ⟨subd9_3_838, List.forall_mem_cons.2 ⟨subd9_3_839, List.forall_mem_cons.2 ⟨subd9_3_840, List.forall_mem_cons.2 ⟨subd9_3_841, List.forall_mem_cons.2 ⟨subd9_3_842, List.forall_mem_cons.2 ⟨subd9_3_843, List.forall_mem_cons.2 ⟨subd9_3_844, List.forall_mem_cons.2 ⟨subd9_3_845, List.forall_mem_cons.2 ⟨subd9_3_846, List.forall_mem_cons.2 ⟨subd9_3_847, List.forall_mem_cons.2 ⟨subd9_3_848, List.forall_mem_cons.2 ⟨subd9_3_849, List.forall_mem_cons.2 ⟨subd9_3_850, List.forall_mem_cons.2 ⟨subd9_3_851, List.forall_mem_cons.2 ⟨subd9_3_852, List.forall_mem_cons.2 ⟨subd9_3_853, List.forall_mem_cons.2 ⟨subd9_3_854, List.forall_mem_cons.2 ⟨subd9_3_855, List.forall_mem_cons.2 ⟨subd9_3_856, List.forall_mem_cons.2 ⟨subd9_3_857, List.forall_mem_cons.2 ⟨subd9_3_858, List.forall_mem_cons.2 ⟨subd9_3_859, List.forall_mem_cons.2 ⟨subd9_3_860, List.forall_mem_cons.2 ⟨subd9_3_861, List.forall_mem_cons.2 ⟨subd9_3_862, List.forall_mem_cons.2 ⟨subd9_3_863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_864 : subd9_3 [1, 3, 4] = true := by decide +kernel
theorem subd9_3_865 : subd9_3 [1, 3, 5] = true := by decide +kernel
theorem subd9_3_866 : subd9_3 [1, 3, 6] = true := by decide +kernel
theorem subd9_3_867 : subd9_3 [1, 3, 7] = true := by decide +kernel
theorem subd9_3_868 : subd9_3 [1, 3, 8] = true := by decide +kernel
theorem subd9_3_869 : subd9_3 [1, 4, -7] = true := by decide +kernel
theorem subd9_3_870 : subd9_3 [1, 4, -6] = true := by decide +kernel
theorem subd9_3_871 : subd9_3 [1, 4, -5] = true := by decide +kernel
theorem subd9_3_872 : subd9_3 [1, 4, -4] = true := by decide +kernel
theorem subd9_3_873 : subd9_3 [1, 4, -3] = true := by decide +kernel
theorem subd9_3_874 : subd9_3 [1, 4, -2] = true := by decide +kernel
theorem subd9_3_875 : subd9_3 [1, 4, -1] = true := by decide +kernel
theorem subd9_3_876 : subd9_3 [1, 4, 0] = true := by decide +kernel
theorem subd9_3_877 : subd9_3 [1, 4, 1] = true := by decide +kernel
theorem subd9_3_878 : subd9_3 [1, 4, 2] = true := by decide +kernel
theorem subd9_3_879 : subd9_3 [1, 4, 3] = true := by decide +kernel
theorem subd9_3_880 : subd9_3 [1, 4, 4] = true := by decide +kernel
theorem subd9_3_881 : subd9_3 [1, 4, 5] = true := by decide +kernel
theorem subd9_3_882 : subd9_3 [1, 4, 6] = true := by decide +kernel
theorem subd9_3_883 : subd9_3 [1, 4, 7] = true := by decide +kernel
theorem subd9_3_884 : subd9_3 [1, 5] = true := by decide +kernel
theorem subd9_3_885 : subd9_3 [2, -6] = true := by decide +kernel
theorem subd9_3_886 : subd9_3 [2, -5] = true := by decide +kernel
theorem subd9_3_887 : subd9_3 [2, -4, -7] = true := by decide +kernel
theorem subd9_3_888 : subd9_3 [2, -4, -6] = true := by decide +kernel
theorem subd9_3_889 : subd9_3 [2, -4, -5] = true := by decide +kernel
theorem subd9_3_890 : subd9_3 [2, -4, -4] = true := by decide +kernel
theorem subd9_3_891 : subd9_3 [2, -4, -3] = true := by decide +kernel
theorem subd9_3_892 : subd9_3 [2, -4, -2] = true := by decide +kernel
theorem subd9_3_893 : subd9_3 [2, -4, -1] = true := by decide +kernel
theorem subd9_3_894 : subd9_3 [2, -4, 0] = true := by decide +kernel
theorem subd9_3_895 : subd9_3 [2, -4, 1] = true := by decide +kernel
theorem sbd9_3_27 : ∀ q ∈ blkd9_3_27, subd9_3 q = true := by
  unfold blkd9_3_27
  exact List.forall_mem_cons.2 ⟨subd9_3_864, List.forall_mem_cons.2 ⟨subd9_3_865, List.forall_mem_cons.2 ⟨subd9_3_866, List.forall_mem_cons.2 ⟨subd9_3_867, List.forall_mem_cons.2 ⟨subd9_3_868, List.forall_mem_cons.2 ⟨subd9_3_869, List.forall_mem_cons.2 ⟨subd9_3_870, List.forall_mem_cons.2 ⟨subd9_3_871, List.forall_mem_cons.2 ⟨subd9_3_872, List.forall_mem_cons.2 ⟨subd9_3_873, List.forall_mem_cons.2 ⟨subd9_3_874, List.forall_mem_cons.2 ⟨subd9_3_875, List.forall_mem_cons.2 ⟨subd9_3_876, List.forall_mem_cons.2 ⟨subd9_3_877, List.forall_mem_cons.2 ⟨subd9_3_878, List.forall_mem_cons.2 ⟨subd9_3_879, List.forall_mem_cons.2 ⟨subd9_3_880, List.forall_mem_cons.2 ⟨subd9_3_881, List.forall_mem_cons.2 ⟨subd9_3_882, List.forall_mem_cons.2 ⟨subd9_3_883, List.forall_mem_cons.2 ⟨subd9_3_884, List.forall_mem_cons.2 ⟨subd9_3_885, List.forall_mem_cons.2 ⟨subd9_3_886, List.forall_mem_cons.2 ⟨subd9_3_887, List.forall_mem_cons.2 ⟨subd9_3_888, List.forall_mem_cons.2 ⟨subd9_3_889, List.forall_mem_cons.2 ⟨subd9_3_890, List.forall_mem_cons.2 ⟨subd9_3_891, List.forall_mem_cons.2 ⟨subd9_3_892, List.forall_mem_cons.2 ⟨subd9_3_893, List.forall_mem_cons.2 ⟨subd9_3_894, List.forall_mem_cons.2 ⟨subd9_3_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_896 : subd9_3 [2, -4, 2] = true := by decide +kernel
theorem subd9_3_897 : subd9_3 [2, -4, 3] = true := by decide +kernel
theorem subd9_3_898 : subd9_3 [2, -4, 4] = true := by decide +kernel
theorem subd9_3_899 : subd9_3 [2, -4, 5] = true := by decide +kernel
theorem subd9_3_900 : subd9_3 [2, -4, 6] = true := by decide +kernel
theorem subd9_3_901 : subd9_3 [2, -3, -8] = true := by decide +kernel
theorem subd9_3_902 : subd9_3 [2, -3, -7] = true := by decide +kernel
theorem subd9_3_903 : subd9_3 [2, -3, -6] = true := by decide +kernel
theorem subd9_3_904 : subd9_3 [2, -3, -5] = true := by decide +kernel
theorem subd9_3_905 : subd9_3 [2, -3, -4] = true := by decide +kernel
theorem subd9_3_906 : subd9_3 [2, -3, -3] = true := by decide +kernel
theorem subd9_3_907 : subd9_3 [2, -3, -2] = true := by decide +kernel
theorem subd9_3_908 : subd9_3 [2, -3, -1] = true := by decide +kernel
theorem subd9_3_909 : subd9_3 [2, -3, 0] = true := by decide +kernel
theorem subd9_3_910 : subd9_3 [2, -3, 1] = true := by decide +kernel
theorem subd9_3_911 : subd9_3 [2, -3, 2] = true := by decide +kernel
theorem subd9_3_912 : subd9_3 [2, -3, 3] = true := by decide +kernel
theorem subd9_3_913 : subd9_3 [2, -3, 4] = true := by decide +kernel
theorem subd9_3_914 : subd9_3 [2, -3, 5] = true := by decide +kernel
theorem subd9_3_915 : subd9_3 [2, -3, 6] = true := by decide +kernel
theorem subd9_3_916 : subd9_3 [2, -3, 7] = true := by decide +kernel
theorem subd9_3_917 : subd9_3 [2, -3, 8] = true := by decide +kernel
theorem subd9_3_918 : subd9_3 [2, -2, -9] = true := by decide +kernel
theorem subd9_3_919 : subd9_3 [2, -2, -8] = true := by decide +kernel
theorem subd9_3_920 : subd9_3 [2, -2, -7] = true := by decide +kernel
theorem subd9_3_921 : subd9_3 [2, -2, -6] = true := by decide +kernel
theorem subd9_3_922 : subd9_3 [2, -2, -5] = true := by decide +kernel
theorem subd9_3_923 : subd9_3 [2, -2, -4] = true := by decide +kernel
theorem subd9_3_924 : subd9_3 [2, -2, -3] = true := by decide +kernel
theorem subd9_3_925 : subd9_3 [2, -2, -2] = true := by decide +kernel
theorem subd9_3_926 : subd9_3 [2, -2, -1] = true := by decide +kernel
theorem subd9_3_927 : subd9_3 [2, -2, 0] = true := by decide +kernel
theorem sbd9_3_28 : ∀ q ∈ blkd9_3_28, subd9_3 q = true := by
  unfold blkd9_3_28
  exact List.forall_mem_cons.2 ⟨subd9_3_896, List.forall_mem_cons.2 ⟨subd9_3_897, List.forall_mem_cons.2 ⟨subd9_3_898, List.forall_mem_cons.2 ⟨subd9_3_899, List.forall_mem_cons.2 ⟨subd9_3_900, List.forall_mem_cons.2 ⟨subd9_3_901, List.forall_mem_cons.2 ⟨subd9_3_902, List.forall_mem_cons.2 ⟨subd9_3_903, List.forall_mem_cons.2 ⟨subd9_3_904, List.forall_mem_cons.2 ⟨subd9_3_905, List.forall_mem_cons.2 ⟨subd9_3_906, List.forall_mem_cons.2 ⟨subd9_3_907, List.forall_mem_cons.2 ⟨subd9_3_908, List.forall_mem_cons.2 ⟨subd9_3_909, List.forall_mem_cons.2 ⟨subd9_3_910, List.forall_mem_cons.2 ⟨subd9_3_911, List.forall_mem_cons.2 ⟨subd9_3_912, List.forall_mem_cons.2 ⟨subd9_3_913, List.forall_mem_cons.2 ⟨subd9_3_914, List.forall_mem_cons.2 ⟨subd9_3_915, List.forall_mem_cons.2 ⟨subd9_3_916, List.forall_mem_cons.2 ⟨subd9_3_917, List.forall_mem_cons.2 ⟨subd9_3_918, List.forall_mem_cons.2 ⟨subd9_3_919, List.forall_mem_cons.2 ⟨subd9_3_920, List.forall_mem_cons.2 ⟨subd9_3_921, List.forall_mem_cons.2 ⟨subd9_3_922, List.forall_mem_cons.2 ⟨subd9_3_923, List.forall_mem_cons.2 ⟨subd9_3_924, List.forall_mem_cons.2 ⟨subd9_3_925, List.forall_mem_cons.2 ⟨subd9_3_926, List.forall_mem_cons.2 ⟨subd9_3_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_3_928 : subd9_3 [2, -2, 1] = true := by decide +kernel
theorem subd9_3_929 : subd9_3 [2, -2, 2] = true := by decide +kernel
theorem subd9_3_930 : subd9_3 [2, -2, 3] = true := by decide +kernel
theorem subd9_3_931 : subd9_3 [2, -2, 4] = true := by decide +kernel
theorem subd9_3_932 : subd9_3 [2, -2, 5] = true := by decide +kernel
theorem subd9_3_933 : subd9_3 [2, -2, 6] = true := by decide +kernel
theorem subd9_3_934 : subd9_3 [2, -2, 7] = true := by decide +kernel
theorem subd9_3_935 : subd9_3 [2, -2, 8] = true := by decide +kernel
theorem subd9_3_936 : subd9_3 [2, -1, -9] = true := by decide +kernel
theorem subd9_3_937 : subd9_3 [2, -1, -8] = true := by decide +kernel
theorem subd9_3_938 : subd9_3 [2, -1, -7] = true := by decide +kernel
theorem subd9_3_939 : subd9_3 [2, -1, -6] = true := by decide +kernel
theorem subd9_3_940 : subd9_3 [2, -1, -5] = true := by decide +kernel
theorem subd9_3_941 : subd9_3 [2, -1, -4] = true := by decide +kernel
theorem subd9_3_942 : subd9_3 [2, -1, -3] = true := by decide +kernel
theorem subd9_3_943 : subd9_3 [2, -1, -2] = true := by decide +kernel
theorem subd9_3_944 : subd9_3 [2, -1, -1] = true := by decide +kernel
theorem subd9_3_945 : subd9_3 [2, -1, 0] = true := by decide +kernel
theorem subd9_3_946 : subd9_3 [2, -1, 1] = true := by decide +kernel
theorem subd9_3_947 : subd9_3 [2, -1, 2] = true := by decide +kernel
theorem subd9_3_948 : subd9_3 [2, -1, 3] = true := by decide +kernel
theorem subd9_3_949 : subd9_3 [2, -1, 4] = true := by decide +kernel
theorem subd9_3_950 : subd9_3 [2, -1, 5] = true := by decide +kernel
theorem subd9_3_951 : subd9_3 [2, -1, 6] = true := by decide +kernel
theorem subd9_3_952 : subd9_3 [2, -1, 7] = true := by decide +kernel
theorem subd9_3_953 : subd9_3 [2, -1, 8] = true := by decide +kernel
theorem subd9_3_954 : subd9_3 [2, -1, 9] = true := by decide +kernel
theorem subd9_3_955 : subd9_3 [2, 0, -9] = true := by decide +kernel
theorem subd9_3_956 : subd9_3 [2, 0, -8] = true := by decide +kernel
theorem subd9_3_957 : subd9_3 [2, 0, -7] = true := by decide +kernel
theorem subd9_3_958 : subd9_3 [2, 0, -6] = true := by decide +kernel
theorem subd9_3_959 : subd9_3 [2, 0, -5] = true := by decide +kernel
theorem sbd9_3_29 : ∀ q ∈ blkd9_3_29, subd9_3 q = true := by
  unfold blkd9_3_29
  exact List.forall_mem_cons.2 ⟨subd9_3_928, List.forall_mem_cons.2 ⟨subd9_3_929, List.forall_mem_cons.2 ⟨subd9_3_930, List.forall_mem_cons.2 ⟨subd9_3_931, List.forall_mem_cons.2 ⟨subd9_3_932, List.forall_mem_cons.2 ⟨subd9_3_933, List.forall_mem_cons.2 ⟨subd9_3_934, List.forall_mem_cons.2 ⟨subd9_3_935, List.forall_mem_cons.2 ⟨subd9_3_936, List.forall_mem_cons.2 ⟨subd9_3_937, List.forall_mem_cons.2 ⟨subd9_3_938, List.forall_mem_cons.2 ⟨subd9_3_939, List.forall_mem_cons.2 ⟨subd9_3_940, List.forall_mem_cons.2 ⟨subd9_3_941, List.forall_mem_cons.2 ⟨subd9_3_942, List.forall_mem_cons.2 ⟨subd9_3_943, List.forall_mem_cons.2 ⟨subd9_3_944, List.forall_mem_cons.2 ⟨subd9_3_945, List.forall_mem_cons.2 ⟨subd9_3_946, List.forall_mem_cons.2 ⟨subd9_3_947, List.forall_mem_cons.2 ⟨subd9_3_948, List.forall_mem_cons.2 ⟨subd9_3_949, List.forall_mem_cons.2 ⟨subd9_3_950, List.forall_mem_cons.2 ⟨subd9_3_951, List.forall_mem_cons.2 ⟨subd9_3_952, List.forall_mem_cons.2 ⟨subd9_3_953, List.forall_mem_cons.2 ⟨subd9_3_954, List.forall_mem_cons.2 ⟨subd9_3_955, List.forall_mem_cons.2 ⟨subd9_3_956, List.forall_mem_cons.2 ⟨subd9_3_957, List.forall_mem_cons.2 ⟨subd9_3_958, List.forall_mem_cons.2 ⟨subd9_3_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C096
