import ReflectZphi.Data.Cert5.C060.Base

namespace ReflectZphi.Data.Cert5.C060
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub5_480 : sub5 [2, 0, 2] = true := by decide +kernel
theorem sub5_481 : sub5 [2, 0, 3] = true := by decide +kernel
theorem sub5_482 : sub5 [2, 0, 4] = true := by decide +kernel
theorem sub5_483 : sub5 [2, 0, 5] = true := by decide +kernel
theorem sub5_484 : sub5 [2, 0, 6] = true := by decide +kernel
theorem sub5_485 : sub5 [2, 0, 7] = true := by decide +kernel
theorem sub5_486 : sub5 [2, 1, -7] = true := by decide +kernel
theorem sub5_487 : sub5 [2, 1, -6] = true := by decide +kernel
theorem sub5_488 : sub5 [2, 1, -5] = true := by decide +kernel
theorem sub5_489 : sub5 [2, 1, -4] = true := by decide +kernel
theorem sub5_490 : sub5 [2, 1, -3] = true := by decide +kernel
theorem sub5_491 : sub5 [2, 1, -2] = true := by decide +kernel
theorem sub5_492 : sub5 [2, 1, -1] = true := by decide +kernel
theorem sub5_493 : sub5 [2, 1, 0] = true := by decide +kernel
theorem sub5_494 : sub5 [2, 1, 1] = true := by decide +kernel
theorem sub5_495 : sub5 [2, 1, 2] = true := by decide +kernel
theorem sub5_496 : sub5 [2, 1, 3] = true := by decide +kernel
theorem sub5_497 : sub5 [2, 1, 4] = true := by decide +kernel
theorem sub5_498 : sub5 [2, 1, 5] = true := by decide +kernel
theorem sub5_499 : sub5 [2, 1, 6] = true := by decide +kernel
theorem sub5_500 : sub5 [2, 1, 7] = true := by decide +kernel
theorem sub5_501 : sub5 [2, 2, -6] = true := by decide +kernel
theorem sub5_502 : sub5 [2, 2, -5] = true := by decide +kernel
theorem sub5_503 : sub5 [2, 2, -4] = true := by decide +kernel
theorem sub5_504 : sub5 [2, 2, -3] = true := by decide +kernel
theorem sub5_505 : sub5 [2, 2, -2] = true := by decide +kernel
theorem sub5_506 : sub5 [2, 2, -1] = true := by decide +kernel
theorem sub5_507 : sub5 [2, 2, 0] = true := by decide +kernel
theorem sub5_508 : sub5 [2, 2, 1] = true := by decide +kernel
theorem sub5_509 : sub5 [2, 2, 2] = true := by decide +kernel
theorem sub5_510 : sub5 [2, 2, 3] = true := by decide +kernel
theorem sub5_511 : sub5 [2, 2, 4] = true := by decide +kernel
theorem sb5_15 : ∀ q ∈ blk5_15, sub5 q = true := by
  unfold blk5_15
  exact List.forall_mem_cons.2 ⟨sub5_480, List.forall_mem_cons.2 ⟨sub5_481, List.forall_mem_cons.2 ⟨sub5_482, List.forall_mem_cons.2 ⟨sub5_483, List.forall_mem_cons.2 ⟨sub5_484, List.forall_mem_cons.2 ⟨sub5_485, List.forall_mem_cons.2 ⟨sub5_486, List.forall_mem_cons.2 ⟨sub5_487, List.forall_mem_cons.2 ⟨sub5_488, List.forall_mem_cons.2 ⟨sub5_489, List.forall_mem_cons.2 ⟨sub5_490, List.forall_mem_cons.2 ⟨sub5_491, List.forall_mem_cons.2 ⟨sub5_492, List.forall_mem_cons.2 ⟨sub5_493, List.forall_mem_cons.2 ⟨sub5_494, List.forall_mem_cons.2 ⟨sub5_495, List.forall_mem_cons.2 ⟨sub5_496, List.forall_mem_cons.2 ⟨sub5_497, List.forall_mem_cons.2 ⟨sub5_498, List.forall_mem_cons.2 ⟨sub5_499, List.forall_mem_cons.2 ⟨sub5_500, List.forall_mem_cons.2 ⟨sub5_501, List.forall_mem_cons.2 ⟨sub5_502, List.forall_mem_cons.2 ⟨sub5_503, List.forall_mem_cons.2 ⟨sub5_504, List.forall_mem_cons.2 ⟨sub5_505, List.forall_mem_cons.2 ⟨sub5_506, List.forall_mem_cons.2 ⟨sub5_507, List.forall_mem_cons.2 ⟨sub5_508, List.forall_mem_cons.2 ⟨sub5_509, List.forall_mem_cons.2 ⟨sub5_510, List.forall_mem_cons.2 ⟨sub5_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_512 : sub5 [2, 2, 5] = true := by decide +kernel
theorem sub5_513 : sub5 [2, 2, 6] = true := by decide +kernel
theorem sub5_514 : sub5 [2, 2, 7] = true := by decide +kernel
theorem sub5_515 : sub5 [2, 2, 8] = true := by decide +kernel
theorem sub5_516 : sub5 [2, 3, -5] = true := by decide +kernel
theorem sub5_517 : sub5 [2, 3, -4] = true := by decide +kernel
theorem sub5_518 : sub5 [2, 3, -3] = true := by decide +kernel
theorem sub5_519 : sub5 [2, 3, -2] = true := by decide +kernel
theorem sub5_520 : sub5 [2, 3, -1] = true := by decide +kernel
theorem sub5_521 : sub5 [2, 3, 0] = true := by decide +kernel
theorem sub5_522 : sub5 [2, 3, 1] = true := by decide +kernel
theorem sub5_523 : sub5 [2, 3, 2] = true := by decide +kernel
theorem sub5_524 : sub5 [2, 3, 3] = true := by decide +kernel
theorem sub5_525 : sub5 [2, 3, 4] = true := by decide +kernel
theorem sub5_526 : sub5 [2, 3, 5] = true := by decide +kernel
theorem sub5_527 : sub5 [2, 3, 6] = true := by decide +kernel
theorem sub5_528 : sub5 [2, 3, 7] = true := by decide +kernel
theorem sub5_529 : sub5 [2, 3, 8] = true := by decide +kernel
theorem sub5_530 : sub5 [2, 4] = true := by decide +kernel
theorem sub5_531 : sub5 [2, 5] = true := by decide +kernel
theorem sub5_532 : sub5 [2, 6] = true := by decide +kernel
theorem sub5_533 : sub5 [2, 7] = true := by decide +kernel
theorem sub5_534 : sub5 [3, -6] = true := by decide +kernel
theorem sub5_535 : sub5 [3, -5] = true := by decide +kernel
theorem sub5_536 : sub5 [3, -4] = true := by decide +kernel
theorem sub5_537 : sub5 [3, -3] = true := by decide +kernel
theorem sub5_538 : sub5 [3, -2] = true := by decide +kernel
theorem sub5_539 : sub5 [3, -1] = true := by decide +kernel
theorem sub5_540 : sub5 [3, 0] = true := by decide +kernel
theorem sub5_541 : sub5 [3, 1, -6] = true := by decide +kernel
theorem sub5_542 : sub5 [3, 1, -5] = true := by decide +kernel
theorem sub5_543 : sub5 [3, 1, -4] = true := by decide +kernel
theorem sb5_16 : ∀ q ∈ blk5_16, sub5 q = true := by
  unfold blk5_16
  exact List.forall_mem_cons.2 ⟨sub5_512, List.forall_mem_cons.2 ⟨sub5_513, List.forall_mem_cons.2 ⟨sub5_514, List.forall_mem_cons.2 ⟨sub5_515, List.forall_mem_cons.2 ⟨sub5_516, List.forall_mem_cons.2 ⟨sub5_517, List.forall_mem_cons.2 ⟨sub5_518, List.forall_mem_cons.2 ⟨sub5_519, List.forall_mem_cons.2 ⟨sub5_520, List.forall_mem_cons.2 ⟨sub5_521, List.forall_mem_cons.2 ⟨sub5_522, List.forall_mem_cons.2 ⟨sub5_523, List.forall_mem_cons.2 ⟨sub5_524, List.forall_mem_cons.2 ⟨sub5_525, List.forall_mem_cons.2 ⟨sub5_526, List.forall_mem_cons.2 ⟨sub5_527, List.forall_mem_cons.2 ⟨sub5_528, List.forall_mem_cons.2 ⟨sub5_529, List.forall_mem_cons.2 ⟨sub5_530, List.forall_mem_cons.2 ⟨sub5_531, List.forall_mem_cons.2 ⟨sub5_532, List.forall_mem_cons.2 ⟨sub5_533, List.forall_mem_cons.2 ⟨sub5_534, List.forall_mem_cons.2 ⟨sub5_535, List.forall_mem_cons.2 ⟨sub5_536, List.forall_mem_cons.2 ⟨sub5_537, List.forall_mem_cons.2 ⟨sub5_538, List.forall_mem_cons.2 ⟨sub5_539, List.forall_mem_cons.2 ⟨sub5_540, List.forall_mem_cons.2 ⟨sub5_541, List.forall_mem_cons.2 ⟨sub5_542, List.forall_mem_cons.2 ⟨sub5_543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_544 : sub5 [3, 1, -3] = true := by decide +kernel
theorem sub5_545 : sub5 [3, 1, -2] = true := by decide +kernel
theorem sub5_546 : sub5 [3, 1, -1] = true := by decide +kernel
theorem sub5_547 : sub5 [3, 1, 0] = true := by decide +kernel
theorem sub5_548 : sub5 [3, 1, 1] = true := by decide +kernel
theorem sub5_549 : sub5 [3, 1, 2] = true := by decide +kernel
theorem sub5_550 : sub5 [3, 1, 3] = true := by decide +kernel
theorem sub5_551 : sub5 [3, 1, 4] = true := by decide +kernel
theorem sub5_552 : sub5 [3, 1, 5] = true := by decide +kernel
theorem sub5_553 : sub5 [3, 1, 6] = true := by decide +kernel
theorem sub5_554 : sub5 [3, 1, 7] = true := by decide +kernel
theorem sub5_555 : sub5 [3, 2] = true := by decide +kernel
theorem sub5_556 : sub5 [3, 3] = true := by decide +kernel
theorem sub5_557 : sub5 [3, 4] = true := by decide +kernel
theorem sub5_558 : sub5 [3, 5] = true := by decide +kernel
theorem sub5_559 : sub5 [3, 6] = true := by decide +kernel
theorem sub5_560 : sub5 [3, 7] = true := by decide +kernel
theorem sub5_561 : sub5 [4, -4] = true := by decide +kernel
theorem sub5_562 : sub5 [4, -3] = true := by decide +kernel
theorem sub5_563 : sub5 [4, -2] = true := by decide +kernel
theorem sub5_564 : sub5 [4, -1] = true := by decide +kernel
theorem sub5_565 : sub5 [4, 0] = true := by decide +kernel
theorem sub5_566 : sub5 [4, 1] = true := by decide +kernel
theorem sub5_567 : sub5 [4, 2] = true := by decide +kernel
theorem sub5_568 : sub5 [4, 3] = true := by decide +kernel
theorem sub5_569 : sub5 [4, 4] = true := by decide +kernel
theorem sub5_570 : sub5 [4, 5] = true := by decide +kernel
theorem sub5_571 : sub5 [4, 6] = true := by decide +kernel
theorem sub5_572 : sub5 [4, 7] = true := by decide +kernel
theorem sub5_573 : sub5 [5, -3] = true := by decide +kernel
theorem sub5_574 : sub5 [5, -2] = true := by decide +kernel
theorem sub5_575 : sub5 [5, -1] = true := by decide +kernel
theorem sb5_17 : ∀ q ∈ blk5_17, sub5 q = true := by
  unfold blk5_17
  exact List.forall_mem_cons.2 ⟨sub5_544, List.forall_mem_cons.2 ⟨sub5_545, List.forall_mem_cons.2 ⟨sub5_546, List.forall_mem_cons.2 ⟨sub5_547, List.forall_mem_cons.2 ⟨sub5_548, List.forall_mem_cons.2 ⟨sub5_549, List.forall_mem_cons.2 ⟨sub5_550, List.forall_mem_cons.2 ⟨sub5_551, List.forall_mem_cons.2 ⟨sub5_552, List.forall_mem_cons.2 ⟨sub5_553, List.forall_mem_cons.2 ⟨sub5_554, List.forall_mem_cons.2 ⟨sub5_555, List.forall_mem_cons.2 ⟨sub5_556, List.forall_mem_cons.2 ⟨sub5_557, List.forall_mem_cons.2 ⟨sub5_558, List.forall_mem_cons.2 ⟨sub5_559, List.forall_mem_cons.2 ⟨sub5_560, List.forall_mem_cons.2 ⟨sub5_561, List.forall_mem_cons.2 ⟨sub5_562, List.forall_mem_cons.2 ⟨sub5_563, List.forall_mem_cons.2 ⟨sub5_564, List.forall_mem_cons.2 ⟨sub5_565, List.forall_mem_cons.2 ⟨sub5_566, List.forall_mem_cons.2 ⟨sub5_567, List.forall_mem_cons.2 ⟨sub5_568, List.forall_mem_cons.2 ⟨sub5_569, List.forall_mem_cons.2 ⟨sub5_570, List.forall_mem_cons.2 ⟨sub5_571, List.forall_mem_cons.2 ⟨sub5_572, List.forall_mem_cons.2 ⟨sub5_573, List.forall_mem_cons.2 ⟨sub5_574, List.forall_mem_cons.2 ⟨sub5_575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub5_576 : sub5 [5, 0] = true := by decide +kernel
theorem sub5_577 : sub5 [5, 1] = true := by decide +kernel
theorem sub5_578 : sub5 [5, 2] = true := by decide +kernel
theorem sub5_579 : sub5 [5, 3] = true := by decide +kernel
theorem sub5_580 : sub5 [5, 4] = true := by decide +kernel
theorem sub5_581 : sub5 [5, 5] = true := by decide +kernel
theorem sub5_582 : sub5 [5, 6] = true := by decide +kernel
theorem sub5_583 : sub5 [5, 7] = true := by decide +kernel
theorem sub5_584 : sub5 [6, -1] = true := by decide +kernel
theorem sub5_585 : sub5 [6, 0] = true := by decide +kernel
theorem sub5_586 : sub5 [6, 1] = true := by decide +kernel
theorem sub5_587 : sub5 [6, 2] = true := by decide +kernel
theorem sub5_588 : sub5 [6, 3] = true := by decide +kernel
theorem sub5_589 : sub5 [6, 4] = true := by decide +kernel
theorem sub5_590 : sub5 [6, 5] = true := by decide +kernel
theorem sb5_18 : ∀ q ∈ blk5_18, sub5 q = true := by
  unfold blk5_18
  exact List.forall_mem_cons.2 ⟨sub5_576, List.forall_mem_cons.2 ⟨sub5_577, List.forall_mem_cons.2 ⟨sub5_578, List.forall_mem_cons.2 ⟨sub5_579, List.forall_mem_cons.2 ⟨sub5_580, List.forall_mem_cons.2 ⟨sub5_581, List.forall_mem_cons.2 ⟨sub5_582, List.forall_mem_cons.2 ⟨sub5_583, List.forall_mem_cons.2 ⟨sub5_584, List.forall_mem_cons.2 ⟨sub5_585, List.forall_mem_cons.2 ⟨sub5_586, List.forall_mem_cons.2 ⟨sub5_587, List.forall_mem_cons.2 ⟨sub5_588, List.forall_mem_cons.2 ⟨sub5_589, List.forall_mem_cons.2 ⟨sub5_590, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_0 : sub6 [-4] = true := by decide +kernel
theorem sub6_1 : sub6 [-3, -4] = true := by decide +kernel
theorem sub6_2 : sub6 [-3, -3] = true := by decide +kernel
theorem sub6_3 : sub6 [-3, -2] = true := by decide +kernel
theorem sub6_4 : sub6 [-3, -1] = true := by decide +kernel
theorem sub6_5 : sub6 [-3, 0] = true := by decide +kernel
theorem sub6_6 : sub6 [-3, 1] = true := by decide +kernel
theorem sub6_7 : sub6 [-3, 2] = true := by decide +kernel
theorem sub6_8 : sub6 [-2, -5] = true := by decide +kernel
theorem sub6_9 : sub6 [-2, -4] = true := by decide +kernel
theorem sub6_10 : sub6 [-2, -3] = true := by decide +kernel
theorem sub6_11 : sub6 [-2, -2] = true := by decide +kernel
theorem sub6_12 : sub6 [-2, -1] = true := by decide +kernel
theorem sub6_13 : sub6 [-2, 0] = true := by decide +kernel
theorem sub6_14 : sub6 [-2, 1] = true := by decide +kernel
theorem sub6_15 : sub6 [-2, 2] = true := by decide +kernel
theorem sub6_16 : sub6 [-2, 3] = true := by decide +kernel
theorem sub6_17 : sub6 [-1, -5] = true := by decide +kernel
theorem sub6_18 : sub6 [-1, -4] = true := by decide +kernel
theorem sub6_19 : sub6 [-1, -3] = true := by decide +kernel
theorem sub6_20 : sub6 [-1, -2] = true := by decide +kernel
theorem sub6_21 : sub6 [-1, -1] = true := by decide +kernel
theorem sub6_22 : sub6 [-1, 0] = true := by decide +kernel
theorem sub6_23 : sub6 [-1, 1] = true := by decide +kernel
theorem sub6_24 : sub6 [-1, 2] = true := by decide +kernel
theorem sub6_25 : sub6 [-1, 3] = true := by decide +kernel
theorem sub6_26 : sub6 [-1, 4] = true := by decide +kernel
theorem sub6_27 : sub6 [0, -5] = true := by decide +kernel
theorem sub6_28 : sub6 [0, -4] = true := by decide +kernel
theorem sub6_29 : sub6 [0, -3] = true := by decide +kernel
theorem sub6_30 : sub6 [0, -2] = true := by decide +kernel
theorem sub6_31 : sub6 [0, -1] = true := by decide +kernel
theorem sb6_0 : ∀ q ∈ blk6_0, sub6 q = true := by
  unfold blk6_0
  exact List.forall_mem_cons.2 ⟨sub6_0, List.forall_mem_cons.2 ⟨sub6_1, List.forall_mem_cons.2 ⟨sub6_2, List.forall_mem_cons.2 ⟨sub6_3, List.forall_mem_cons.2 ⟨sub6_4, List.forall_mem_cons.2 ⟨sub6_5, List.forall_mem_cons.2 ⟨sub6_6, List.forall_mem_cons.2 ⟨sub6_7, List.forall_mem_cons.2 ⟨sub6_8, List.forall_mem_cons.2 ⟨sub6_9, List.forall_mem_cons.2 ⟨sub6_10, List.forall_mem_cons.2 ⟨sub6_11, List.forall_mem_cons.2 ⟨sub6_12, List.forall_mem_cons.2 ⟨sub6_13, List.forall_mem_cons.2 ⟨sub6_14, List.forall_mem_cons.2 ⟨sub6_15, List.forall_mem_cons.2 ⟨sub6_16, List.forall_mem_cons.2 ⟨sub6_17, List.forall_mem_cons.2 ⟨sub6_18, List.forall_mem_cons.2 ⟨sub6_19, List.forall_mem_cons.2 ⟨sub6_20, List.forall_mem_cons.2 ⟨sub6_21, List.forall_mem_cons.2 ⟨sub6_22, List.forall_mem_cons.2 ⟨sub6_23, List.forall_mem_cons.2 ⟨sub6_24, List.forall_mem_cons.2 ⟨sub6_25, List.forall_mem_cons.2 ⟨sub6_26, List.forall_mem_cons.2 ⟨sub6_27, List.forall_mem_cons.2 ⟨sub6_28, List.forall_mem_cons.2 ⟨sub6_29, List.forall_mem_cons.2 ⟨sub6_30, List.forall_mem_cons.2 ⟨sub6_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C060
