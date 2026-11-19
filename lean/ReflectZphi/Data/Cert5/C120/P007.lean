import ReflectZphi.Data.Cert5.C120.Base

namespace ReflectZphi.Data.Cert5.C120
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub7_384 : sub7 [1, 1, -1] = true := by decide +kernel
theorem sub7_385 : sub7 [1, 1, 0] = true := by decide +kernel
theorem sub7_386 : sub7 [1, 1, 1] = true := by decide +kernel
theorem sub7_387 : sub7 [1, 1, 2] = true := by decide +kernel
theorem sub7_388 : sub7 [1, 1, 3] = true := by decide +kernel
theorem sub7_389 : sub7 [1, 1, 4] = true := by decide +kernel
theorem sub7_390 : sub7 [1, 1, 5] = true := by decide +kernel
theorem sub7_391 : sub7 [1, 1, 6] = true := by decide +kernel
theorem sub7_392 : sub7 [1, 2, -9] = true := by decide +kernel
theorem sub7_393 : sub7 [1, 2, -8] = true := by decide +kernel
theorem sub7_394 : sub7 [1, 2, -7] = true := by decide +kernel
theorem sub7_395 : sub7 [1, 2, -6] = true := by decide +kernel
theorem sub7_396 : sub7 [1, 2, -5] = true := by decide +kernel
theorem sub7_397 : sub7 [1, 2, -4] = true := by decide +kernel
theorem sub7_398 : sub7 [1, 2, -3] = true := by decide +kernel
theorem sub7_399 : sub7 [1, 2, -2] = true := by decide +kernel
theorem sub7_400 : sub7 [1, 2, -1] = true := by decide +kernel
theorem sub7_401 : sub7 [1, 2, 0] = true := by decide +kernel
theorem sub7_402 : sub7 [1, 2, 1] = true := by decide +kernel
theorem sub7_403 : sub7 [1, 2, 2] = true := by decide +kernel
theorem sub7_404 : sub7 [1, 2, 3] = true := by decide +kernel
theorem sub7_405 : sub7 [1, 2, 4] = true := by decide +kernel
theorem sub7_406 : sub7 [1, 2, 5] = true := by decide +kernel
theorem sub7_407 : sub7 [1, 3, -9] = true := by decide +kernel
theorem sub7_408 : sub7 [1, 3, -8] = true := by decide +kernel
theorem sub7_409 : sub7 [1, 3, -7] = true := by decide +kernel
theorem sub7_410 : sub7 [1, 3, -6] = true := by decide +kernel
theorem sub7_411 : sub7 [1, 3, -5] = true := by decide +kernel
theorem sub7_412 : sub7 [1, 3, -4] = true := by decide +kernel
theorem sub7_413 : sub7 [1, 3, -3] = true := by decide +kernel
theorem sub7_414 : sub7 [1, 3, -2] = true := by decide +kernel
theorem sub7_415 : sub7 [1, 3, -1] = true := by decide +kernel
theorem sb7_12 : ∀ q ∈ blk7_12, sub7 q = true := by
  unfold blk7_12
  exact List.forall_mem_cons.2 ⟨sub7_384, List.forall_mem_cons.2 ⟨sub7_385, List.forall_mem_cons.2 ⟨sub7_386, List.forall_mem_cons.2 ⟨sub7_387, List.forall_mem_cons.2 ⟨sub7_388, List.forall_mem_cons.2 ⟨sub7_389, List.forall_mem_cons.2 ⟨sub7_390, List.forall_mem_cons.2 ⟨sub7_391, List.forall_mem_cons.2 ⟨sub7_392, List.forall_mem_cons.2 ⟨sub7_393, List.forall_mem_cons.2 ⟨sub7_394, List.forall_mem_cons.2 ⟨sub7_395, List.forall_mem_cons.2 ⟨sub7_396, List.forall_mem_cons.2 ⟨sub7_397, List.forall_mem_cons.2 ⟨sub7_398, List.forall_mem_cons.2 ⟨sub7_399, List.forall_mem_cons.2 ⟨sub7_400, List.forall_mem_cons.2 ⟨sub7_401, List.forall_mem_cons.2 ⟨sub7_402, List.forall_mem_cons.2 ⟨sub7_403, List.forall_mem_cons.2 ⟨sub7_404, List.forall_mem_cons.2 ⟨sub7_405, List.forall_mem_cons.2 ⟨sub7_406, List.forall_mem_cons.2 ⟨sub7_407, List.forall_mem_cons.2 ⟨sub7_408, List.forall_mem_cons.2 ⟨sub7_409, List.forall_mem_cons.2 ⟨sub7_410, List.forall_mem_cons.2 ⟨sub7_411, List.forall_mem_cons.2 ⟨sub7_412, List.forall_mem_cons.2 ⟨sub7_413, List.forall_mem_cons.2 ⟨sub7_414, List.forall_mem_cons.2 ⟨sub7_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_416 : sub7 [1, 3, 0] = true := by decide +kernel
theorem sub7_417 : sub7 [1, 3, 1] = true := by decide +kernel
theorem sub7_418 : sub7 [1, 3, 2] = true := by decide +kernel
theorem sub7_419 : sub7 [1, 3, 3] = true := by decide +kernel
theorem sub7_420 : sub7 [1, 3, 4] = true := by decide +kernel
theorem sub7_421 : sub7 [1, 4] = true := by decide +kernel
theorem sub7_422 : sub7 [1, 5] = true := by decide +kernel
theorem sub7_423 : sub7 [1, 6] = true := by decide +kernel
theorem sub7_424 : sub7 [2, -6] = true := by decide +kernel
theorem sub7_425 : sub7 [2, -5] = true := by decide +kernel
theorem sub7_426 : sub7 [2, -4] = true := by decide +kernel
theorem sub7_427 : sub7 [2, -3] = true := by decide +kernel
theorem sub7_428 : sub7 [2, -2, -6] = true := by decide +kernel
theorem sub7_429 : sub7 [2, -2, -5] = true := by decide +kernel
theorem sub7_430 : sub7 [2, -2, -4] = true := by decide +kernel
theorem sub7_431 : sub7 [2, -2, -3] = true := by decide +kernel
theorem sub7_432 : sub7 [2, -2, -2] = true := by decide +kernel
theorem sub7_433 : sub7 [2, -2, -1] = true := by decide +kernel
theorem sub7_434 : sub7 [2, -2, 0] = true := by decide +kernel
theorem sub7_435 : sub7 [2, -2, 1] = true := by decide +kernel
theorem sub7_436 : sub7 [2, -2, 2] = true := by decide +kernel
theorem sub7_437 : sub7 [2, -2, 3] = true := by decide +kernel
theorem sub7_438 : sub7 [2, -2, 4] = true := by decide +kernel
theorem sub7_439 : sub7 [2, -2, 5] = true := by decide +kernel
theorem sub7_440 : sub7 [2, -2, 6] = true := by decide +kernel
theorem sub7_441 : sub7 [2, -1, -7] = true := by decide +kernel
theorem sub7_442 : sub7 [2, -1, -6] = true := by decide +kernel
theorem sub7_443 : sub7 [2, -1, -5] = true := by decide +kernel
theorem sub7_444 : sub7 [2, -1, -4] = true := by decide +kernel
theorem sub7_445 : sub7 [2, -1, -3] = true := by decide +kernel
theorem sub7_446 : sub7 [2, -1, -2] = true := by decide +kernel
theorem sub7_447 : sub7 [2, -1, -1] = true := by decide +kernel
theorem sb7_13 : ∀ q ∈ blk7_13, sub7 q = true := by
  unfold blk7_13
  exact List.forall_mem_cons.2 ⟨sub7_416, List.forall_mem_cons.2 ⟨sub7_417, List.forall_mem_cons.2 ⟨sub7_418, List.forall_mem_cons.2 ⟨sub7_419, List.forall_mem_cons.2 ⟨sub7_420, List.forall_mem_cons.2 ⟨sub7_421, List.forall_mem_cons.2 ⟨sub7_422, List.forall_mem_cons.2 ⟨sub7_423, List.forall_mem_cons.2 ⟨sub7_424, List.forall_mem_cons.2 ⟨sub7_425, List.forall_mem_cons.2 ⟨sub7_426, List.forall_mem_cons.2 ⟨sub7_427, List.forall_mem_cons.2 ⟨sub7_428, List.forall_mem_cons.2 ⟨sub7_429, List.forall_mem_cons.2 ⟨sub7_430, List.forall_mem_cons.2 ⟨sub7_431, List.forall_mem_cons.2 ⟨sub7_432, List.forall_mem_cons.2 ⟨sub7_433, List.forall_mem_cons.2 ⟨sub7_434, List.forall_mem_cons.2 ⟨sub7_435, List.forall_mem_cons.2 ⟨sub7_436, List.forall_mem_cons.2 ⟨sub7_437, List.forall_mem_cons.2 ⟨sub7_438, List.forall_mem_cons.2 ⟨sub7_439, List.forall_mem_cons.2 ⟨sub7_440, List.forall_mem_cons.2 ⟨sub7_441, List.forall_mem_cons.2 ⟨sub7_442, List.forall_mem_cons.2 ⟨sub7_443, List.forall_mem_cons.2 ⟨sub7_444, List.forall_mem_cons.2 ⟨sub7_445, List.forall_mem_cons.2 ⟨sub7_446, List.forall_mem_cons.2 ⟨sub7_447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_448 : sub7 [2, -1, 0] = true := by decide +kernel
theorem sub7_449 : sub7 [2, -1, 1] = true := by decide +kernel
theorem sub7_450 : sub7 [2, -1, 2] = true := by decide +kernel
theorem sub7_451 : sub7 [2, -1, 3] = true := by decide +kernel
theorem sub7_452 : sub7 [2, -1, 4] = true := by decide +kernel
theorem sub7_453 : sub7 [2, -1, 5] = true := by decide +kernel
theorem sub7_454 : sub7 [2, -1, 6] = true := by decide +kernel
theorem sub7_455 : sub7 [2, 0, -8] = true := by decide +kernel
theorem sub7_456 : sub7 [2, 0, -7] = true := by decide +kernel
theorem sub7_457 : sub7 [2, 0, -6] = true := by decide +kernel
theorem sub7_458 : sub7 [2, 0, -5] = true := by decide +kernel
theorem sub7_459 : sub7 [2, 0, -4] = true := by decide +kernel
theorem sub7_460 : sub7 [2, 0, -3] = true := by decide +kernel
theorem sub7_461 : sub7 [2, 0, -2] = true := by decide +kernel
theorem sub7_462 : sub7 [2, 0, -1] = true := by decide +kernel
theorem sub7_463 : sub7 [2, 0, 0] = true := by decide +kernel
theorem sub7_464 : sub7 [2, 0, 1] = true := by decide +kernel
theorem sub7_465 : sub7 [2, 0, 2] = true := by decide +kernel
theorem sub7_466 : sub7 [2, 0, 3] = true := by decide +kernel
theorem sub7_467 : sub7 [2, 0, 4] = true := by decide +kernel
theorem sub7_468 : sub7 [2, 0, 5] = true := by decide +kernel
theorem sub7_469 : sub7 [2, 0, 6] = true := by decide +kernel
theorem sub7_470 : sub7 [2, 1, -8] = true := by decide +kernel
theorem sub7_471 : sub7 [2, 1, -7] = true := by decide +kernel
theorem sub7_472 : sub7 [2, 1, -6] = true := by decide +kernel
theorem sub7_473 : sub7 [2, 1, -5] = true := by decide +kernel
theorem sub7_474 : sub7 [2, 1, -4] = true := by decide +kernel
theorem sub7_475 : sub7 [2, 1, -3] = true := by decide +kernel
theorem sub7_476 : sub7 [2, 1, -2] = true := by decide +kernel
theorem sub7_477 : sub7 [2, 1, -1] = true := by decide +kernel
theorem sub7_478 : sub7 [2, 1, 0] = true := by decide +kernel
theorem sub7_479 : sub7 [2, 1, 1] = true := by decide +kernel
theorem sb7_14 : ∀ q ∈ blk7_14, sub7 q = true := by
  unfold blk7_14
  exact List.forall_mem_cons.2 ⟨sub7_448, List.forall_mem_cons.2 ⟨sub7_449, List.forall_mem_cons.2 ⟨sub7_450, List.forall_mem_cons.2 ⟨sub7_451, List.forall_mem_cons.2 ⟨sub7_452, List.forall_mem_cons.2 ⟨sub7_453, List.forall_mem_cons.2 ⟨sub7_454, List.forall_mem_cons.2 ⟨sub7_455, List.forall_mem_cons.2 ⟨sub7_456, List.forall_mem_cons.2 ⟨sub7_457, List.forall_mem_cons.2 ⟨sub7_458, List.forall_mem_cons.2 ⟨sub7_459, List.forall_mem_cons.2 ⟨sub7_460, List.forall_mem_cons.2 ⟨sub7_461, List.forall_mem_cons.2 ⟨sub7_462, List.forall_mem_cons.2 ⟨sub7_463, List.forall_mem_cons.2 ⟨sub7_464, List.forall_mem_cons.2 ⟨sub7_465, List.forall_mem_cons.2 ⟨sub7_466, List.forall_mem_cons.2 ⟨sub7_467, List.forall_mem_cons.2 ⟨sub7_468, List.forall_mem_cons.2 ⟨sub7_469, List.forall_mem_cons.2 ⟨sub7_470, List.forall_mem_cons.2 ⟨sub7_471, List.forall_mem_cons.2 ⟨sub7_472, List.forall_mem_cons.2 ⟨sub7_473, List.forall_mem_cons.2 ⟨sub7_474, List.forall_mem_cons.2 ⟨sub7_475, List.forall_mem_cons.2 ⟨sub7_476, List.forall_mem_cons.2 ⟨sub7_477, List.forall_mem_cons.2 ⟨sub7_478, List.forall_mem_cons.2 ⟨sub7_479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_480 : sub7 [2, 1, 2] = true := by decide +kernel
theorem sub7_481 : sub7 [2, 1, 3] = true := by decide +kernel
theorem sub7_482 : sub7 [2, 1, 4] = true := by decide +kernel
theorem sub7_483 : sub7 [2, 1, 5] = true := by decide +kernel
theorem sub7_484 : sub7 [2, 2, -9] = true := by decide +kernel
theorem sub7_485 : sub7 [2, 2, -8] = true := by decide +kernel
theorem sub7_486 : sub7 [2, 2, -7] = true := by decide +kernel
theorem sub7_487 : sub7 [2, 2, -6] = true := by decide +kernel
theorem sub7_488 : sub7 [2, 2, -5] = true := by decide +kernel
theorem sub7_489 : sub7 [2, 2, -4] = true := by decide +kernel
theorem sub7_490 : sub7 [2, 2, -3] = true := by decide +kernel
theorem sub7_491 : sub7 [2, 2, -2] = true := by decide +kernel
theorem sub7_492 : sub7 [2, 2, -1] = true := by decide +kernel
theorem sub7_493 : sub7 [2, 2, 0] = true := by decide +kernel
theorem sub7_494 : sub7 [2, 2, 1] = true := by decide +kernel
theorem sub7_495 : sub7 [2, 2, 2] = true := by decide +kernel
theorem sub7_496 : sub7 [2, 2, 3] = true := by decide +kernel
theorem sub7_497 : sub7 [2, 2, 4] = true := by decide +kernel
theorem sub7_498 : sub7 [2, 2, 5] = true := by decide +kernel
theorem sub7_499 : sub7 [2, 3] = true := by decide +kernel
theorem sub7_500 : sub7 [2, 4] = true := by decide +kernel
theorem sub7_501 : sub7 [2, 5] = true := by decide +kernel
theorem sub7_502 : sub7 [2, 6] = true := by decide +kernel
theorem sub7_503 : sub7 [3, -5] = true := by decide +kernel
theorem sub7_504 : sub7 [3, -4] = true := by decide +kernel
theorem sub7_505 : sub7 [3, -3] = true := by decide +kernel
theorem sub7_506 : sub7 [3, -2] = true := by decide +kernel
theorem sub7_507 : sub7 [3, -1] = true := by decide +kernel
theorem sub7_508 : sub7 [3, 0] = true := by decide +kernel
theorem sub7_509 : sub7 [3, 1, -8] = true := by decide +kernel
theorem sub7_510 : sub7 [3, 1, -7] = true := by decide +kernel
theorem sub7_511 : sub7 [3, 1, -6] = true := by decide +kernel
theorem sb7_15 : ∀ q ∈ blk7_15, sub7 q = true := by
  unfold blk7_15
  exact List.forall_mem_cons.2 ⟨sub7_480, List.forall_mem_cons.2 ⟨sub7_481, List.forall_mem_cons.2 ⟨sub7_482, List.forall_mem_cons.2 ⟨sub7_483, List.forall_mem_cons.2 ⟨sub7_484, List.forall_mem_cons.2 ⟨sub7_485, List.forall_mem_cons.2 ⟨sub7_486, List.forall_mem_cons.2 ⟨sub7_487, List.forall_mem_cons.2 ⟨sub7_488, List.forall_mem_cons.2 ⟨sub7_489, List.forall_mem_cons.2 ⟨sub7_490, List.forall_mem_cons.2 ⟨sub7_491, List.forall_mem_cons.2 ⟨sub7_492, List.forall_mem_cons.2 ⟨sub7_493, List.forall_mem_cons.2 ⟨sub7_494, List.forall_mem_cons.2 ⟨sub7_495, List.forall_mem_cons.2 ⟨sub7_496, List.forall_mem_cons.2 ⟨sub7_497, List.forall_mem_cons.2 ⟨sub7_498, List.forall_mem_cons.2 ⟨sub7_499, List.forall_mem_cons.2 ⟨sub7_500, List.forall_mem_cons.2 ⟨sub7_501, List.forall_mem_cons.2 ⟨sub7_502, List.forall_mem_cons.2 ⟨sub7_503, List.forall_mem_cons.2 ⟨sub7_504, List.forall_mem_cons.2 ⟨sub7_505, List.forall_mem_cons.2 ⟨sub7_506, List.forall_mem_cons.2 ⟨sub7_507, List.forall_mem_cons.2 ⟨sub7_508, List.forall_mem_cons.2 ⟨sub7_509, List.forall_mem_cons.2 ⟨sub7_510, List.forall_mem_cons.2 ⟨sub7_511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_512 : sub7 [3, 1, -5] = true := by decide +kernel
theorem sub7_513 : sub7 [3, 1, -4] = true := by decide +kernel
theorem sub7_514 : sub7 [3, 1, -3] = true := by decide +kernel
theorem sub7_515 : sub7 [3, 1, -2] = true := by decide +kernel
theorem sub7_516 : sub7 [3, 1, -1] = true := by decide +kernel
theorem sub7_517 : sub7 [3, 1, 0] = true := by decide +kernel
theorem sub7_518 : sub7 [3, 1, 1] = true := by decide +kernel
theorem sub7_519 : sub7 [3, 1, 2] = true := by decide +kernel
theorem sub7_520 : sub7 [3, 1, 3] = true := by decide +kernel
theorem sub7_521 : sub7 [3, 1, 4] = true := by decide +kernel
theorem sub7_522 : sub7 [3, 1, 5] = true := by decide +kernel
theorem sub7_523 : sub7 [3, 2] = true := by decide +kernel
theorem sub7_524 : sub7 [3, 3] = true := by decide +kernel
theorem sub7_525 : sub7 [3, 4] = true := by decide +kernel
theorem sub7_526 : sub7 [3, 5] = true := by decide +kernel
theorem sub7_527 : sub7 [4, -4] = true := by decide +kernel
theorem sub7_528 : sub7 [4, -3] = true := by decide +kernel
theorem sub7_529 : sub7 [4, -2] = true := by decide +kernel
theorem sub7_530 : sub7 [4, -1] = true := by decide +kernel
theorem sub7_531 : sub7 [4, 0] = true := by decide +kernel
theorem sub7_532 : sub7 [4, 1] = true := by decide +kernel
theorem sub7_533 : sub7 [4, 2] = true := by decide +kernel
theorem sub7_534 : sub7 [4, 3] = true := by decide +kernel
theorem sub7_535 : sub7 [4, 4] = true := by decide +kernel
theorem sub7_536 : sub7 [4, 5] = true := by decide +kernel
theorem sub7_537 : sub7 [5, -2] = true := by decide +kernel
theorem sub7_538 : sub7 [5, -1] = true := by decide +kernel
theorem sub7_539 : sub7 [5, 0] = true := by decide +kernel
theorem sub7_540 : sub7 [5, 1] = true := by decide +kernel
theorem sub7_541 : sub7 [5, 2] = true := by decide +kernel
theorem sub7_542 : sub7 [5, 3] = true := by decide +kernel
theorem sb7_16 : ∀ q ∈ blk7_16, sub7 q = true := by
  unfold blk7_16
  exact List.forall_mem_cons.2 ⟨sub7_512, List.forall_mem_cons.2 ⟨sub7_513, List.forall_mem_cons.2 ⟨sub7_514, List.forall_mem_cons.2 ⟨sub7_515, List.forall_mem_cons.2 ⟨sub7_516, List.forall_mem_cons.2 ⟨sub7_517, List.forall_mem_cons.2 ⟨sub7_518, List.forall_mem_cons.2 ⟨sub7_519, List.forall_mem_cons.2 ⟨sub7_520, List.forall_mem_cons.2 ⟨sub7_521, List.forall_mem_cons.2 ⟨sub7_522, List.forall_mem_cons.2 ⟨sub7_523, List.forall_mem_cons.2 ⟨sub7_524, List.forall_mem_cons.2 ⟨sub7_525, List.forall_mem_cons.2 ⟨sub7_526, List.forall_mem_cons.2 ⟨sub7_527, List.forall_mem_cons.2 ⟨sub7_528, List.forall_mem_cons.2 ⟨sub7_529, List.forall_mem_cons.2 ⟨sub7_530, List.forall_mem_cons.2 ⟨sub7_531, List.forall_mem_cons.2 ⟨sub7_532, List.forall_mem_cons.2 ⟨sub7_533, List.forall_mem_cons.2 ⟨sub7_534, List.forall_mem_cons.2 ⟨sub7_535, List.forall_mem_cons.2 ⟨sub7_536, List.forall_mem_cons.2 ⟨sub7_537, List.forall_mem_cons.2 ⟨sub7_538, List.forall_mem_cons.2 ⟨sub7_539, List.forall_mem_cons.2 ⟨sub7_540, List.forall_mem_cons.2 ⟨sub7_541, List.forall_mem_cons.2 ⟨sub7_542, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_0 : sub8 [-4, -3] = true := by decide +kernel
theorem sub8_1 : sub8 [-4, -2] = true := by decide +kernel
theorem sub8_2 : sub8 [-4, -1] = true := by decide +kernel
theorem sub8_3 : sub8 [-4, 0, -7] = true := by decide +kernel
theorem sub8_4 : sub8 [-4, 0, -6] = true := by decide +kernel
theorem sub8_5 : sub8 [-4, 0, -5] = true := by decide +kernel
theorem sub8_6 : sub8 [-4, 0, -4] = true := by decide +kernel
theorem sub8_7 : sub8 [-4, 0, -3] = true := by decide +kernel
theorem sub8_8 : sub8 [-4, 0, -2] = true := by decide +kernel
theorem sub8_9 : sub8 [-4, 0, -1] = true := by decide +kernel
theorem sub8_10 : sub8 [-4, 0, 0] = true := by decide +kernel
theorem sub8_11 : sub8 [-4, 0, 1] = true := by decide +kernel
theorem sub8_12 : sub8 [-4, 0, 2] = true := by decide +kernel
theorem sub8_13 : sub8 [-4, 0, 3] = true := by decide +kernel
theorem sub8_14 : sub8 [-4, 0, 4] = true := by decide +kernel
theorem sub8_15 : sub8 [-4, 0, 5] = true := by decide +kernel
theorem sub8_16 : sub8 [-4, 0, 6] = true := by decide +kernel
theorem sub8_17 : sub8 [-4, 1, -7] = true := by decide +kernel
theorem sub8_18 : sub8 [-4, 1, -6] = true := by decide +kernel
theorem sub8_19 : sub8 [-4, 1, -5] = true := by decide +kernel
theorem sub8_20 : sub8 [-4, 1, -4] = true := by decide +kernel
theorem sub8_21 : sub8 [-4, 1, -3] = true := by decide +kernel
theorem sub8_22 : sub8 [-4, 1, -2] = true := by decide +kernel
theorem sub8_23 : sub8 [-4, 1, -1] = true := by decide +kernel
theorem sub8_24 : sub8 [-4, 1, 0] = true := by decide +kernel
theorem sub8_25 : sub8 [-4, 1, 1] = true := by decide +kernel
theorem sub8_26 : sub8 [-4, 1, 2] = true := by decide +kernel
theorem sub8_27 : sub8 [-4, 1, 3] = true := by decide +kernel
theorem sub8_28 : sub8 [-4, 1, 4] = true := by decide +kernel
theorem sub8_29 : sub8 [-4, 1, 5] = true := by decide +kernel
theorem sub8_30 : sub8 [-4, 1, 6] = true := by decide +kernel
theorem sub8_31 : sub8 [-4, 2] = true := by decide +kernel
theorem sb8_0 : ∀ q ∈ blk8_0, sub8 q = true := by
  unfold blk8_0
  exact List.forall_mem_cons.2 ⟨sub8_0, List.forall_mem_cons.2 ⟨sub8_1, List.forall_mem_cons.2 ⟨sub8_2, List.forall_mem_cons.2 ⟨sub8_3, List.forall_mem_cons.2 ⟨sub8_4, List.forall_mem_cons.2 ⟨sub8_5, List.forall_mem_cons.2 ⟨sub8_6, List.forall_mem_cons.2 ⟨sub8_7, List.forall_mem_cons.2 ⟨sub8_8, List.forall_mem_cons.2 ⟨sub8_9, List.forall_mem_cons.2 ⟨sub8_10, List.forall_mem_cons.2 ⟨sub8_11, List.forall_mem_cons.2 ⟨sub8_12, List.forall_mem_cons.2 ⟨sub8_13, List.forall_mem_cons.2 ⟨sub8_14, List.forall_mem_cons.2 ⟨sub8_15, List.forall_mem_cons.2 ⟨sub8_16, List.forall_mem_cons.2 ⟨sub8_17, List.forall_mem_cons.2 ⟨sub8_18, List.forall_mem_cons.2 ⟨sub8_19, List.forall_mem_cons.2 ⟨sub8_20, List.forall_mem_cons.2 ⟨sub8_21, List.forall_mem_cons.2 ⟨sub8_22, List.forall_mem_cons.2 ⟨sub8_23, List.forall_mem_cons.2 ⟨sub8_24, List.forall_mem_cons.2 ⟨sub8_25, List.forall_mem_cons.2 ⟨sub8_26, List.forall_mem_cons.2 ⟨sub8_27, List.forall_mem_cons.2 ⟨sub8_28, List.forall_mem_cons.2 ⟨sub8_29, List.forall_mem_cons.2 ⟨sub8_30, List.forall_mem_cons.2 ⟨sub8_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_32 : sub8 [-4, 3] = true := by decide +kernel
theorem sub8_33 : sub8 [-3, -4] = true := by decide +kernel
theorem sub8_34 : sub8 [-3, -3] = true := by decide +kernel
theorem sub8_35 : sub8 [-3, -2, -8] = true := by decide +kernel
theorem sub8_36 : sub8 [-3, -2, -7] = true := by decide +kernel
theorem sub8_37 : sub8 [-3, -2, -6] = true := by decide +kernel
theorem sub8_38 : sub8 [-3, -2, -5] = true := by decide +kernel
theorem sub8_39 : sub8 [-3, -2, -4] = true := by decide +kernel
theorem sub8_40 : sub8 [-3, -2, -3] = true := by decide +kernel
theorem sub8_41 : sub8 [-3, -2, -2] = true := by decide +kernel
theorem sub8_42 : sub8 [-3, -2, -1] = true := by decide +kernel
theorem sub8_43 : sub8 [-3, -2, 0] = true := by decide +kernel
theorem sub8_44 : sub8 [-3, -2, 1] = true := by decide +kernel
theorem sub8_45 : sub8 [-3, -2, 2] = true := by decide +kernel
theorem sub8_46 : sub8 [-3, -2, 3] = true := by decide +kernel
theorem sub8_47 : sub8 [-3, -2, 4] = true := by decide +kernel
theorem sub8_48 : sub8 [-3, -2, 5] = true := by decide +kernel
theorem sub8_49 : sub8 [-3, -2, 6] = true := by decide +kernel
theorem sub8_50 : sub8 [-3, -2, 7] = true := by decide +kernel
theorem sub8_51 : sub8 [-3, -1, -9] = true := by decide +kernel
theorem sub8_52 : sub8 [-3, -1, -8] = true := by decide +kernel
theorem sub8_53 : sub8 [-3, -1, -7] = true := by decide +kernel
theorem sub8_54 : sub8 [-3, -1, -6] = true := by decide +kernel
theorem sub8_55 : sub8 [-3, -1, -5] = true := by decide +kernel
theorem sub8_56 : sub8 [-3, -1, -4] = true := by decide +kernel
theorem sub8_57 : sub8 [-3, -1, -3] = true := by decide +kernel
theorem sub8_58 : sub8 [-3, -1, -2] = true := by decide +kernel
theorem sub8_59 : sub8 [-3, -1, -1] = true := by decide +kernel
theorem sub8_60 : sub8 [-3, -1, 0] = true := by decide +kernel
theorem sub8_61 : sub8 [-3, -1, 1] = true := by decide +kernel
theorem sub8_62 : sub8 [-3, -1, 2] = true := by decide +kernel
theorem sub8_63 : sub8 [-3, -1, 3] = true := by decide +kernel
theorem sb8_1 : ∀ q ∈ blk8_1, sub8 q = true := by
  unfold blk8_1
  exact List.forall_mem_cons.2 ⟨sub8_32, List.forall_mem_cons.2 ⟨sub8_33, List.forall_mem_cons.2 ⟨sub8_34, List.forall_mem_cons.2 ⟨sub8_35, List.forall_mem_cons.2 ⟨sub8_36, List.forall_mem_cons.2 ⟨sub8_37, List.forall_mem_cons.2 ⟨sub8_38, List.forall_mem_cons.2 ⟨sub8_39, List.forall_mem_cons.2 ⟨sub8_40, List.forall_mem_cons.2 ⟨sub8_41, List.forall_mem_cons.2 ⟨sub8_42, List.forall_mem_cons.2 ⟨sub8_43, List.forall_mem_cons.2 ⟨sub8_44, List.forall_mem_cons.2 ⟨sub8_45, List.forall_mem_cons.2 ⟨sub8_46, List.forall_mem_cons.2 ⟨sub8_47, List.forall_mem_cons.2 ⟨sub8_48, List.forall_mem_cons.2 ⟨sub8_49, List.forall_mem_cons.2 ⟨sub8_50, List.forall_mem_cons.2 ⟨sub8_51, List.forall_mem_cons.2 ⟨sub8_52, List.forall_mem_cons.2 ⟨sub8_53, List.forall_mem_cons.2 ⟨sub8_54, List.forall_mem_cons.2 ⟨sub8_55, List.forall_mem_cons.2 ⟨sub8_56, List.forall_mem_cons.2 ⟨sub8_57, List.forall_mem_cons.2 ⟨sub8_58, List.forall_mem_cons.2 ⟨sub8_59, List.forall_mem_cons.2 ⟨sub8_60, List.forall_mem_cons.2 ⟨sub8_61, List.forall_mem_cons.2 ⟨sub8_62, List.forall_mem_cons.2 ⟨sub8_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_64 : sub8 [-3, -1, 4] = true := by decide +kernel
theorem sub8_65 : sub8 [-3, -1, 5] = true := by decide +kernel
theorem sub8_66 : sub8 [-3, -1, 6] = true := by decide +kernel
theorem sub8_67 : sub8 [-3, -1, 7] = true := by decide +kernel
theorem sub8_68 : sub8 [-3, -1, 8] = true := by decide +kernel
theorem sub8_69 : sub8 [-3, 0, -10] = true := by decide +kernel
theorem sub8_70 : sub8 [-3, 0, -9] = true := by decide +kernel
theorem sub8_71 : sub8 [-3, 0, -8] = true := by decide +kernel
theorem sub8_72 : sub8 [-3, 0, -7] = true := by decide +kernel
theorem sub8_73 : sub8 [-3, 0, -6] = true := by decide +kernel
theorem sub8_74 : sub8 [-3, 0, -5] = true := by decide +kernel
theorem sub8_75 : sub8 [-3, 0, -4] = true := by decide +kernel
theorem sub8_76 : sub8 [-3, 0, -3] = true := by decide +kernel
theorem sub8_77 : sub8 [-3, 0, -2] = true := by decide +kernel
theorem sub8_78 : sub8 [-3, 0, -1] = true := by decide +kernel
theorem sub8_79 : sub8 [-3, 0, 0] = true := by decide +kernel
theorem sub8_80 : sub8 [-3, 0, 1] = true := by decide +kernel
theorem sub8_81 : sub8 [-3, 0, 2] = true := by decide +kernel
theorem sub8_82 : sub8 [-3, 0, 3] = true := by decide +kernel
theorem sub8_83 : sub8 [-3, 0, 4] = true := by decide +kernel
theorem sub8_84 : sub8 [-3, 0, 5] = true := by decide +kernel
theorem sub8_85 : sub8 [-3, 0, 6] = true := by decide +kernel
theorem sub8_86 : sub8 [-3, 0, 7] = true := by decide +kernel
theorem sub8_87 : sub8 [-3, 0, 8] = true := by decide +kernel
theorem sub8_88 : sub8 [-3, 1, -10] = true := by decide +kernel
theorem sub8_89 : sub8 [-3, 1, -9] = true := by decide +kernel
theorem sub8_90 : sub8 [-3, 1, -8] = true := by decide +kernel
theorem sub8_91 : sub8 [-3, 1, -7] = true := by decide +kernel
theorem sub8_92 : sub8 [-3, 1, -6] = true := by decide +kernel
theorem sub8_93 : sub8 [-3, 1, -5] = true := by decide +kernel
theorem sub8_94 : sub8 [-3, 1, -4] = true := by decide +kernel
theorem sub8_95 : sub8 [-3, 1, -3] = true := by decide +kernel
theorem sb8_2 : ∀ q ∈ blk8_2, sub8 q = true := by
  unfold blk8_2
  exact List.forall_mem_cons.2 ⟨sub8_64, List.forall_mem_cons.2 ⟨sub8_65, List.forall_mem_cons.2 ⟨sub8_66, List.forall_mem_cons.2 ⟨sub8_67, List.forall_mem_cons.2 ⟨sub8_68, List.forall_mem_cons.2 ⟨sub8_69, List.forall_mem_cons.2 ⟨sub8_70, List.forall_mem_cons.2 ⟨sub8_71, List.forall_mem_cons.2 ⟨sub8_72, List.forall_mem_cons.2 ⟨sub8_73, List.forall_mem_cons.2 ⟨sub8_74, List.forall_mem_cons.2 ⟨sub8_75, List.forall_mem_cons.2 ⟨sub8_76, List.forall_mem_cons.2 ⟨sub8_77, List.forall_mem_cons.2 ⟨sub8_78, List.forall_mem_cons.2 ⟨sub8_79, List.forall_mem_cons.2 ⟨sub8_80, List.forall_mem_cons.2 ⟨sub8_81, List.forall_mem_cons.2 ⟨sub8_82, List.forall_mem_cons.2 ⟨sub8_83, List.forall_mem_cons.2 ⟨sub8_84, List.forall_mem_cons.2 ⟨sub8_85, List.forall_mem_cons.2 ⟨sub8_86, List.forall_mem_cons.2 ⟨sub8_87, List.forall_mem_cons.2 ⟨sub8_88, List.forall_mem_cons.2 ⟨sub8_89, List.forall_mem_cons.2 ⟨sub8_90, List.forall_mem_cons.2 ⟨sub8_91, List.forall_mem_cons.2 ⟨sub8_92, List.forall_mem_cons.2 ⟨sub8_93, List.forall_mem_cons.2 ⟨sub8_94, List.forall_mem_cons.2 ⟨sub8_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_96 : sub8 [-3, 1, -2] = true := by decide +kernel
theorem sub8_97 : sub8 [-3, 1, -1] = true := by decide +kernel
theorem sub8_98 : sub8 [-3, 1, 0] = true := by decide +kernel
theorem sub8_99 : sub8 [-3, 1, 1] = true := by decide +kernel
theorem sub8_100 : sub8 [-3, 1, 2] = true := by decide +kernel
theorem sub8_101 : sub8 [-3, 1, 3] = true := by decide +kernel
theorem sub8_102 : sub8 [-3, 1, 4] = true := by decide +kernel
theorem sub8_103 : sub8 [-3, 1, 5] = true := by decide +kernel
theorem sub8_104 : sub8 [-3, 1, 6] = true := by decide +kernel
theorem sub8_105 : sub8 [-3, 1, 7] = true := by decide +kernel
theorem sub8_106 : sub8 [-3, 1, 8] = true := by decide +kernel
theorem sub8_107 : sub8 [-3, 2, -9] = true := by decide +kernel
theorem sub8_108 : sub8 [-3, 2, -8] = true := by decide +kernel
theorem sub8_109 : sub8 [-3, 2, -7] = true := by decide +kernel
theorem sub8_110 : sub8 [-3, 2, -6] = true := by decide +kernel
theorem sub8_111 : sub8 [-3, 2, -5] = true := by decide +kernel
theorem sub8_112 : sub8 [-3, 2, -4] = true := by decide +kernel
theorem sub8_113 : sub8 [-3, 2, -3] = true := by decide +kernel
theorem sub8_114 : sub8 [-3, 2, -2] = true := by decide +kernel
theorem sub8_115 : sub8 [-3, 2, -1] = true := by decide +kernel
theorem sub8_116 : sub8 [-3, 2, 0] = true := by decide +kernel
theorem sub8_117 : sub8 [-3, 2, 1] = true := by decide +kernel
theorem sub8_118 : sub8 [-3, 2, 2] = true := by decide +kernel
theorem sub8_119 : sub8 [-3, 2, 3] = true := by decide +kernel
theorem sub8_120 : sub8 [-3, 2, 4] = true := by decide +kernel
theorem sub8_121 : sub8 [-3, 2, 5] = true := by decide +kernel
theorem sub8_122 : sub8 [-3, 2, 6] = true := by decide +kernel
theorem sub8_123 : sub8 [-3, 2, 7] = true := by decide +kernel
theorem sub8_124 : sub8 [-3, 2, 8] = true := by decide +kernel
theorem sub8_125 : sub8 [-3, 3, -7] = true := by decide +kernel
theorem sub8_126 : sub8 [-3, 3, -6] = true := by decide +kernel
theorem sub8_127 : sub8 [-3, 3, -5] = true := by decide +kernel
theorem sb8_3 : ∀ q ∈ blk8_3, sub8 q = true := by
  unfold blk8_3
  exact List.forall_mem_cons.2 ⟨sub8_96, List.forall_mem_cons.2 ⟨sub8_97, List.forall_mem_cons.2 ⟨sub8_98, List.forall_mem_cons.2 ⟨sub8_99, List.forall_mem_cons.2 ⟨sub8_100, List.forall_mem_cons.2 ⟨sub8_101, List.forall_mem_cons.2 ⟨sub8_102, List.forall_mem_cons.2 ⟨sub8_103, List.forall_mem_cons.2 ⟨sub8_104, List.forall_mem_cons.2 ⟨sub8_105, List.forall_mem_cons.2 ⟨sub8_106, List.forall_mem_cons.2 ⟨sub8_107, List.forall_mem_cons.2 ⟨sub8_108, List.forall_mem_cons.2 ⟨sub8_109, List.forall_mem_cons.2 ⟨sub8_110, List.forall_mem_cons.2 ⟨sub8_111, List.forall_mem_cons.2 ⟨sub8_112, List.forall_mem_cons.2 ⟨sub8_113, List.forall_mem_cons.2 ⟨sub8_114, List.forall_mem_cons.2 ⟨sub8_115, List.forall_mem_cons.2 ⟨sub8_116, List.forall_mem_cons.2 ⟨sub8_117, List.forall_mem_cons.2 ⟨sub8_118, List.forall_mem_cons.2 ⟨sub8_119, List.forall_mem_cons.2 ⟨sub8_120, List.forall_mem_cons.2 ⟨sub8_121, List.forall_mem_cons.2 ⟨sub8_122, List.forall_mem_cons.2 ⟨sub8_123, List.forall_mem_cons.2 ⟨sub8_124, List.forall_mem_cons.2 ⟨sub8_125, List.forall_mem_cons.2 ⟨sub8_126, List.forall_mem_cons.2 ⟨sub8_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_128 : sub8 [-3, 3, -4] = true := by decide +kernel
theorem sub8_129 : sub8 [-3, 3, -3] = true := by decide +kernel
theorem sub8_130 : sub8 [-3, 3, -2] = true := by decide +kernel
theorem sub8_131 : sub8 [-3, 3, -1] = true := by decide +kernel
theorem sub8_132 : sub8 [-3, 3, 0] = true := by decide +kernel
theorem sub8_133 : sub8 [-3, 3, 1] = true := by decide +kernel
theorem sub8_134 : sub8 [-3, 3, 2] = true := by decide +kernel
theorem sub8_135 : sub8 [-3, 3, 3] = true := by decide +kernel
theorem sub8_136 : sub8 [-3, 3, 4] = true := by decide +kernel
theorem sub8_137 : sub8 [-3, 3, 5] = true := by decide +kernel
theorem sub8_138 : sub8 [-3, 3, 6] = true := by decide +kernel
theorem sub8_139 : sub8 [-3, 4] = true := by decide +kernel
theorem sub8_140 : sub8 [-2, -5] = true := by decide +kernel
theorem sub8_141 : sub8 [-2, -4] = true := by decide +kernel
theorem sub8_142 : sub8 [-2, -3, -8] = true := by decide +kernel
theorem sub8_143 : sub8 [-2, -3, -7] = true := by decide +kernel
theorem sub8_144 : sub8 [-2, -3, -6] = true := by decide +kernel
theorem sub8_145 : sub8 [-2, -3, -5] = true := by decide +kernel
theorem sub8_146 : sub8 [-2, -3, -4] = true := by decide +kernel
theorem sub8_147 : sub8 [-2, -3, -3] = true := by decide +kernel
theorem sub8_148 : sub8 [-2, -3, -2] = true := by decide +kernel
theorem sub8_149 : sub8 [-2, -3, -1] = true := by decide +kernel
theorem sub8_150 : sub8 [-2, -3, 0] = true := by decide +kernel
theorem sub8_151 : sub8 [-2, -3, 1] = true := by decide +kernel
theorem sub8_152 : sub8 [-2, -3, 2] = true := by decide +kernel
theorem sub8_153 : sub8 [-2, -3, 3] = true := by decide +kernel
theorem sub8_154 : sub8 [-2, -3, 4] = true := by decide +kernel
theorem sub8_155 : sub8 [-2, -3, 5] = true := by decide +kernel
theorem sub8_156 : sub8 [-2, -3, 6] = true := by decide +kernel
theorem sub8_157 : sub8 [-2, -3, 7] = true := by decide +kernel
theorem sub8_158 : sub8 [-2, -2, -10] = true := by decide +kernel
theorem sub8_159 : sub8 [-2, -2, -9] = true := by decide +kernel
theorem sb8_4 : ∀ q ∈ blk8_4, sub8 q = true := by
  unfold blk8_4
  exact List.forall_mem_cons.2 ⟨sub8_128, List.forall_mem_cons.2 ⟨sub8_129, List.forall_mem_cons.2 ⟨sub8_130, List.forall_mem_cons.2 ⟨sub8_131, List.forall_mem_cons.2 ⟨sub8_132, List.forall_mem_cons.2 ⟨sub8_133, List.forall_mem_cons.2 ⟨sub8_134, List.forall_mem_cons.2 ⟨sub8_135, List.forall_mem_cons.2 ⟨sub8_136, List.forall_mem_cons.2 ⟨sub8_137, List.forall_mem_cons.2 ⟨sub8_138, List.forall_mem_cons.2 ⟨sub8_139, List.forall_mem_cons.2 ⟨sub8_140, List.forall_mem_cons.2 ⟨sub8_141, List.forall_mem_cons.2 ⟨sub8_142, List.forall_mem_cons.2 ⟨sub8_143, List.forall_mem_cons.2 ⟨sub8_144, List.forall_mem_cons.2 ⟨sub8_145, List.forall_mem_cons.2 ⟨sub8_146, List.forall_mem_cons.2 ⟨sub8_147, List.forall_mem_cons.2 ⟨sub8_148, List.forall_mem_cons.2 ⟨sub8_149, List.forall_mem_cons.2 ⟨sub8_150, List.forall_mem_cons.2 ⟨sub8_151, List.forall_mem_cons.2 ⟨sub8_152, List.forall_mem_cons.2 ⟨sub8_153, List.forall_mem_cons.2 ⟨sub8_154, List.forall_mem_cons.2 ⟨sub8_155, List.forall_mem_cons.2 ⟨sub8_156, List.forall_mem_cons.2 ⟨sub8_157, List.forall_mem_cons.2 ⟨sub8_158, List.forall_mem_cons.2 ⟨sub8_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_160 : sub8 [-2, -2, -8] = true := by decide +kernel
theorem sub8_161 : sub8 [-2, -2, -7] = true := by decide +kernel
theorem sub8_162 : sub8 [-2, -2, -6] = true := by decide +kernel
theorem sub8_163 : sub8 [-2, -2, -5] = true := by decide +kernel
theorem sub8_164 : sub8 [-2, -2, -4] = true := by decide +kernel
theorem sub8_165 : sub8 [-2, -2, -3] = true := by decide +kernel
theorem sub8_166 : sub8 [-2, -2, -2] = true := by decide +kernel
theorem sub8_167 : sub8 [-2, -2, -1] = true := by decide +kernel
theorem sub8_168 : sub8 [-2, -2, 0] = true := by decide +kernel
theorem sub8_169 : sub8 [-2, -2, 1] = true := by decide +kernel
theorem sub8_170 : sub8 [-2, -2, 2] = true := by decide +kernel
theorem sub8_171 : sub8 [-2, -2, 3] = true := by decide +kernel
theorem sub8_172 : sub8 [-2, -2, 4] = true := by decide +kernel
theorem sub8_173 : sub8 [-2, -2, 5] = true := by decide +kernel
theorem sub8_174 : sub8 [-2, -2, 6] = true := by decide +kernel
theorem sub8_175 : sub8 [-2, -2, 7] = true := by decide +kernel
theorem sub8_176 : sub8 [-2, -2, 8] = true := by decide +kernel
theorem sub8_177 : sub8 [-2, -2, 9] = true := by decide +kernel
theorem sub8_178 : sub8 [-2, -1, -11] = true := by decide +kernel
theorem sub8_179 : sub8 [-2, -1, -10] = true := by decide +kernel
theorem sub8_180 : sub8 [-2, -1, -9] = true := by decide +kernel
theorem sub8_181 : sub8 [-2, -1, -8] = true := by decide +kernel
theorem sub8_182 : sub8 [-2, -1, -7] = true := by decide +kernel
theorem sub8_183 : sub8 [-2, -1, -6] = true := by decide +kernel
theorem sub8_184 : sub8 [-2, -1, -5] = true := by decide +kernel
theorem sub8_185 : sub8 [-2, -1, -4] = true := by decide +kernel
theorem sub8_186 : sub8 [-2, -1, -3] = true := by decide +kernel
theorem sub8_187 : sub8 [-2, -1, -2] = true := by decide +kernel
theorem sub8_188 : sub8 [-2, -1, -1] = true := by decide +kernel
theorem sub8_189 : sub8 [-2, -1, 0] = true := by decide +kernel
theorem sub8_190 : sub8 [-2, -1, 1] = true := by decide +kernel
theorem sub8_191 : sub8 [-2, -1, 2] = true := by decide +kernel
theorem sb8_5 : ∀ q ∈ blk8_5, sub8 q = true := by
  unfold blk8_5
  exact List.forall_mem_cons.2 ⟨sub8_160, List.forall_mem_cons.2 ⟨sub8_161, List.forall_mem_cons.2 ⟨sub8_162, List.forall_mem_cons.2 ⟨sub8_163, List.forall_mem_cons.2 ⟨sub8_164, List.forall_mem_cons.2 ⟨sub8_165, List.forall_mem_cons.2 ⟨sub8_166, List.forall_mem_cons.2 ⟨sub8_167, List.forall_mem_cons.2 ⟨sub8_168, List.forall_mem_cons.2 ⟨sub8_169, List.forall_mem_cons.2 ⟨sub8_170, List.forall_mem_cons.2 ⟨sub8_171, List.forall_mem_cons.2 ⟨sub8_172, List.forall_mem_cons.2 ⟨sub8_173, List.forall_mem_cons.2 ⟨sub8_174, List.forall_mem_cons.2 ⟨sub8_175, List.forall_mem_cons.2 ⟨sub8_176, List.forall_mem_cons.2 ⟨sub8_177, List.forall_mem_cons.2 ⟨sub8_178, List.forall_mem_cons.2 ⟨sub8_179, List.forall_mem_cons.2 ⟨sub8_180, List.forall_mem_cons.2 ⟨sub8_181, List.forall_mem_cons.2 ⟨sub8_182, List.forall_mem_cons.2 ⟨sub8_183, List.forall_mem_cons.2 ⟨sub8_184, List.forall_mem_cons.2 ⟨sub8_185, List.forall_mem_cons.2 ⟨sub8_186, List.forall_mem_cons.2 ⟨sub8_187, List.forall_mem_cons.2 ⟨sub8_188, List.forall_mem_cons.2 ⟨sub8_189, List.forall_mem_cons.2 ⟨sub8_190, List.forall_mem_cons.2 ⟨sub8_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C120
