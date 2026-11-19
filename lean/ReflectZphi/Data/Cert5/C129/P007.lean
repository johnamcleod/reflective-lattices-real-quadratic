import ReflectZphi.Data.Cert5.C129.Base

namespace ReflectZphi.Data.Cert5.C129

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_0_352 : subd6_0 [2, -3] = true := by decide +kernel
theorem subd6_0_353 : subd6_0 [2, -2, -8] = true := by decide +kernel
theorem subd6_0_354 : subd6_0 [2, -2, -7] = true := by decide +kernel
theorem subd6_0_355 : subd6_0 [2, -2, -6] = true := by decide +kernel
theorem subd6_0_356 : subd6_0 [2, -2, -5] = true := by decide +kernel
theorem subd6_0_357 : subd6_0 [2, -2, -4] = true := by decide +kernel
theorem subd6_0_358 : subd6_0 [2, -2, -3] = true := by decide +kernel
theorem subd6_0_359 : subd6_0 [2, -2, -2] = true := by decide +kernel
theorem subd6_0_360 : subd6_0 [2, -2, -1] = true := by decide +kernel
theorem subd6_0_361 : subd6_0 [2, -2, 0] = true := by decide +kernel
theorem subd6_0_362 : subd6_0 [2, -2, 1] = true := by decide +kernel
theorem subd6_0_363 : subd6_0 [2, -2, 2] = true := by decide +kernel
theorem subd6_0_364 : subd6_0 [2, -2, 3] = true := by decide +kernel
theorem subd6_0_365 : subd6_0 [2, -2, 4] = true := by decide +kernel
theorem subd6_0_366 : subd6_0 [2, -2, 5] = true := by decide +kernel
theorem subd6_0_367 : subd6_0 [2, -2, 6] = true := by decide +kernel
theorem subd6_0_368 : subd6_0 [2, -1, -7] = true := by decide +kernel
theorem subd6_0_369 : subd6_0 [2, -1, -6] = true := by decide +kernel
theorem subd6_0_370 : subd6_0 [2, -1, -5] = true := by decide +kernel
theorem subd6_0_371 : subd6_0 [2, -1, -4] = true := by decide +kernel
theorem subd6_0_372 : subd6_0 [2, -1, -3] = true := by decide +kernel
theorem subd6_0_373 : subd6_0 [2, -1, -2] = true := by decide +kernel
theorem subd6_0_374 : subd6_0 [2, -1, -1] = true := by decide +kernel
theorem subd6_0_375 : subd6_0 [2, -1, 0] = true := by decide +kernel
theorem subd6_0_376 : subd6_0 [2, -1, 1] = true := by decide +kernel
theorem subd6_0_377 : subd6_0 [2, -1, 2] = true := by decide +kernel
theorem subd6_0_378 : subd6_0 [2, -1, 3] = true := by decide +kernel
theorem subd6_0_379 : subd6_0 [2, -1, 4] = true := by decide +kernel
theorem subd6_0_380 : subd6_0 [2, -1, 5] = true := by decide +kernel
theorem subd6_0_381 : subd6_0 [2, -1, 6] = true := by decide +kernel
theorem subd6_0_382 : subd6_0 [2, 0, -7] = true := by decide +kernel
theorem subd6_0_383 : subd6_0 [2, 0, -6] = true := by decide +kernel
theorem sbd6_0_11 : ∀ q ∈ blkd6_0_11, subd6_0 q = true := by
  unfold blkd6_0_11
  exact List.forall_mem_cons.2 ⟨subd6_0_352, List.forall_mem_cons.2 ⟨subd6_0_353, List.forall_mem_cons.2 ⟨subd6_0_354, List.forall_mem_cons.2 ⟨subd6_0_355, List.forall_mem_cons.2 ⟨subd6_0_356, List.forall_mem_cons.2 ⟨subd6_0_357, List.forall_mem_cons.2 ⟨subd6_0_358, List.forall_mem_cons.2 ⟨subd6_0_359, List.forall_mem_cons.2 ⟨subd6_0_360, List.forall_mem_cons.2 ⟨subd6_0_361, List.forall_mem_cons.2 ⟨subd6_0_362, List.forall_mem_cons.2 ⟨subd6_0_363, List.forall_mem_cons.2 ⟨subd6_0_364, List.forall_mem_cons.2 ⟨subd6_0_365, List.forall_mem_cons.2 ⟨subd6_0_366, List.forall_mem_cons.2 ⟨subd6_0_367, List.forall_mem_cons.2 ⟨subd6_0_368, List.forall_mem_cons.2 ⟨subd6_0_369, List.forall_mem_cons.2 ⟨subd6_0_370, List.forall_mem_cons.2 ⟨subd6_0_371, List.forall_mem_cons.2 ⟨subd6_0_372, List.forall_mem_cons.2 ⟨subd6_0_373, List.forall_mem_cons.2 ⟨subd6_0_374, List.forall_mem_cons.2 ⟨subd6_0_375, List.forall_mem_cons.2 ⟨subd6_0_376, List.forall_mem_cons.2 ⟨subd6_0_377, List.forall_mem_cons.2 ⟨subd6_0_378, List.forall_mem_cons.2 ⟨subd6_0_379, List.forall_mem_cons.2 ⟨subd6_0_380, List.forall_mem_cons.2 ⟨subd6_0_381, List.forall_mem_cons.2 ⟨subd6_0_382, List.forall_mem_cons.2 ⟨subd6_0_383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_384 : subd6_0 [2, 0, -5] = true := by decide +kernel
theorem subd6_0_385 : subd6_0 [2, 0, -4] = true := by decide +kernel
theorem subd6_0_386 : subd6_0 [2, 0, -3] = true := by decide +kernel
theorem subd6_0_387 : subd6_0 [2, 0, -2] = true := by decide +kernel
theorem subd6_0_388 : subd6_0 [2, 0, -1] = true := by decide +kernel
theorem subd6_0_389 : subd6_0 [2, 0, 0] = true := by decide +kernel
theorem subd6_0_390 : subd6_0 [2, 0, 1] = true := by decide +kernel
theorem subd6_0_391 : subd6_0 [2, 0, 2] = true := by decide +kernel
theorem subd6_0_392 : subd6_0 [2, 0, 3] = true := by decide +kernel
theorem subd6_0_393 : subd6_0 [2, 0, 4] = true := by decide +kernel
theorem subd6_0_394 : subd6_0 [2, 0, 5] = true := by decide +kernel
theorem subd6_0_395 : subd6_0 [2, 0, 6] = true := by decide +kernel
theorem subd6_0_396 : subd6_0 [2, 0, 7] = true := by decide +kernel
theorem subd6_0_397 : subd6_0 [2, 1, -7] = true := by decide +kernel
theorem subd6_0_398 : subd6_0 [2, 1, -6] = true := by decide +kernel
theorem subd6_0_399 : subd6_0 [2, 1, -5] = true := by decide +kernel
theorem subd6_0_400 : subd6_0 [2, 1, -4] = true := by decide +kernel
theorem subd6_0_401 : subd6_0 [2, 1, -3] = true := by decide +kernel
theorem subd6_0_402 : subd6_0 [2, 1, -2] = true := by decide +kernel
theorem subd6_0_403 : subd6_0 [2, 1, -1] = true := by decide +kernel
theorem subd6_0_404 : subd6_0 [2, 1, 0] = true := by decide +kernel
theorem subd6_0_405 : subd6_0 [2, 1, 1] = true := by decide +kernel
theorem subd6_0_406 : subd6_0 [2, 1, 2] = true := by decide +kernel
theorem subd6_0_407 : subd6_0 [2, 1, 3] = true := by decide +kernel
theorem subd6_0_408 : subd6_0 [2, 1, 4] = true := by decide +kernel
theorem subd6_0_409 : subd6_0 [2, 1, 5] = true := by decide +kernel
theorem subd6_0_410 : subd6_0 [2, 1, 6] = true := by decide +kernel
theorem subd6_0_411 : subd6_0 [2, 1, 7] = true := by decide +kernel
theorem subd6_0_412 : subd6_0 [2, 2] = true := by decide +kernel
theorem subd6_0_413 : subd6_0 [2, 3] = true := by decide +kernel
theorem subd6_0_414 : subd6_0 [2, 4] = true := by decide +kernel
theorem subd6_0_415 : subd6_0 [2, 5] = true := by decide +kernel
theorem sbd6_0_12 : ∀ q ∈ blkd6_0_12, subd6_0 q = true := by
  unfold blkd6_0_12
  exact List.forall_mem_cons.2 ⟨subd6_0_384, List.forall_mem_cons.2 ⟨subd6_0_385, List.forall_mem_cons.2 ⟨subd6_0_386, List.forall_mem_cons.2 ⟨subd6_0_387, List.forall_mem_cons.2 ⟨subd6_0_388, List.forall_mem_cons.2 ⟨subd6_0_389, List.forall_mem_cons.2 ⟨subd6_0_390, List.forall_mem_cons.2 ⟨subd6_0_391, List.forall_mem_cons.2 ⟨subd6_0_392, List.forall_mem_cons.2 ⟨subd6_0_393, List.forall_mem_cons.2 ⟨subd6_0_394, List.forall_mem_cons.2 ⟨subd6_0_395, List.forall_mem_cons.2 ⟨subd6_0_396, List.forall_mem_cons.2 ⟨subd6_0_397, List.forall_mem_cons.2 ⟨subd6_0_398, List.forall_mem_cons.2 ⟨subd6_0_399, List.forall_mem_cons.2 ⟨subd6_0_400, List.forall_mem_cons.2 ⟨subd6_0_401, List.forall_mem_cons.2 ⟨subd6_0_402, List.forall_mem_cons.2 ⟨subd6_0_403, List.forall_mem_cons.2 ⟨subd6_0_404, List.forall_mem_cons.2 ⟨subd6_0_405, List.forall_mem_cons.2 ⟨subd6_0_406, List.forall_mem_cons.2 ⟨subd6_0_407, List.forall_mem_cons.2 ⟨subd6_0_408, List.forall_mem_cons.2 ⟨subd6_0_409, List.forall_mem_cons.2 ⟨subd6_0_410, List.forall_mem_cons.2 ⟨subd6_0_411, List.forall_mem_cons.2 ⟨subd6_0_412, List.forall_mem_cons.2 ⟨subd6_0_413, List.forall_mem_cons.2 ⟨subd6_0_414, List.forall_mem_cons.2 ⟨subd6_0_415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_416 : subd6_0 [3, -6] = true := by decide +kernel
theorem subd6_0_417 : subd6_0 [3, -5] = true := by decide +kernel
theorem subd6_0_418 : subd6_0 [3, -4] = true := by decide +kernel
theorem subd6_0_419 : subd6_0 [3, -3] = true := by decide +kernel
theorem subd6_0_420 : subd6_0 [3, -2] = true := by decide +kernel
theorem subd6_0_421 : subd6_0 [3, -1] = true := by decide +kernel
theorem subd6_0_422 : subd6_0 [3, 0] = true := by decide +kernel
theorem subd6_0_423 : subd6_0 [3, 1] = true := by decide +kernel
theorem subd6_0_424 : subd6_0 [3, 2] = true := by decide +kernel
theorem subd6_0_425 : subd6_0 [3, 3] = true := by decide +kernel
theorem subd6_0_426 : subd6_0 [3, 4] = true := by decide +kernel
theorem subd6_0_427 : subd6_0 [4, -6] = true := by decide +kernel
theorem subd6_0_428 : subd6_0 [4, -5] = true := by decide +kernel
theorem subd6_0_429 : subd6_0 [4, -4] = true := by decide +kernel
theorem subd6_0_430 : subd6_0 [4, -3] = true := by decide +kernel
theorem subd6_0_431 : subd6_0 [4, -2] = true := by decide +kernel
theorem subd6_0_432 : subd6_0 [4, -1] = true := by decide +kernel
theorem subd6_0_433 : subd6_0 [4, 0] = true := by decide +kernel
theorem subd6_0_434 : subd6_0 [4, 1] = true := by decide +kernel
theorem subd6_0_435 : subd6_0 [4, 2] = true := by decide +kernel
theorem subd6_0_436 : subd6_0 [4, 3] = true := by decide +kernel
theorem subd6_0_437 : subd6_0 [5, -4] = true := by decide +kernel
theorem subd6_0_438 : subd6_0 [5, -3] = true := by decide +kernel
theorem subd6_0_439 : subd6_0 [5, -2] = true := by decide +kernel
theorem subd6_0_440 : subd6_0 [5, -1] = true := by decide +kernel
theorem subd6_0_441 : subd6_0 [5, 0] = true := by decide +kernel
theorem subd6_0_442 : subd6_0 [5, 1] = true := by decide +kernel
theorem sbd6_0_13 : ∀ q ∈ blkd6_0_13, subd6_0 q = true := by
  unfold blkd6_0_13
  exact List.forall_mem_cons.2 ⟨subd6_0_416, List.forall_mem_cons.2 ⟨subd6_0_417, List.forall_mem_cons.2 ⟨subd6_0_418, List.forall_mem_cons.2 ⟨subd6_0_419, List.forall_mem_cons.2 ⟨subd6_0_420, List.forall_mem_cons.2 ⟨subd6_0_421, List.forall_mem_cons.2 ⟨subd6_0_422, List.forall_mem_cons.2 ⟨subd6_0_423, List.forall_mem_cons.2 ⟨subd6_0_424, List.forall_mem_cons.2 ⟨subd6_0_425, List.forall_mem_cons.2 ⟨subd6_0_426, List.forall_mem_cons.2 ⟨subd6_0_427, List.forall_mem_cons.2 ⟨subd6_0_428, List.forall_mem_cons.2 ⟨subd6_0_429, List.forall_mem_cons.2 ⟨subd6_0_430, List.forall_mem_cons.2 ⟨subd6_0_431, List.forall_mem_cons.2 ⟨subd6_0_432, List.forall_mem_cons.2 ⟨subd6_0_433, List.forall_mem_cons.2 ⟨subd6_0_434, List.forall_mem_cons.2 ⟨subd6_0_435, List.forall_mem_cons.2 ⟨subd6_0_436, List.forall_mem_cons.2 ⟨subd6_0_437, List.forall_mem_cons.2 ⟨subd6_0_438, List.forall_mem_cons.2 ⟨subd6_0_439, List.forall_mem_cons.2 ⟨subd6_0_440, List.forall_mem_cons.2 ⟨subd6_0_441, List.forall_mem_cons.2 ⟨subd6_0_442, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-6] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [-5, -2] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [-5, -1] = true := by decide +kernel
theorem subd6_1_3 : subd6_1 [-5, 0] = true := by decide +kernel
theorem subd6_1_4 : subd6_1 [-5, 1] = true := by decide +kernel
theorem subd6_1_5 : subd6_1 [-5, 2] = true := by decide +kernel
theorem subd6_1_6 : subd6_1 [-5, 3] = true := by decide +kernel
theorem subd6_1_7 : subd6_1 [-5, 4] = true := by decide +kernel
theorem subd6_1_8 : subd6_1 [-5, 5] = true := by decide +kernel
theorem subd6_1_9 : subd6_1 [-4, -3] = true := by decide +kernel
theorem subd6_1_10 : subd6_1 [-4, -2] = true := by decide +kernel
theorem subd6_1_11 : subd6_1 [-4, -1] = true := by decide +kernel
theorem subd6_1_12 : subd6_1 [-4, 0] = true := by decide +kernel
theorem subd6_1_13 : subd6_1 [-4, 1] = true := by decide +kernel
theorem subd6_1_14 : subd6_1 [-4, 2] = true := by decide +kernel
theorem subd6_1_15 : subd6_1 [-4, 3] = true := by decide +kernel
theorem subd6_1_16 : subd6_1 [-4, 4] = true := by decide +kernel
theorem subd6_1_17 : subd6_1 [-4, 5] = true := by decide +kernel
theorem subd6_1_18 : subd6_1 [-3, -4] = true := by decide +kernel
theorem subd6_1_19 : subd6_1 [-3, -3] = true := by decide +kernel
theorem subd6_1_20 : subd6_1 [-3, -2] = true := by decide +kernel
theorem subd6_1_21 : subd6_1 [-3, -1] = true := by decide +kernel
theorem subd6_1_22 : subd6_1 [-3, 0] = true := by decide +kernel
theorem subd6_1_23 : subd6_1 [-3, 1] = true := by decide +kernel
theorem subd6_1_24 : subd6_1 [-3, 2] = true := by decide +kernel
theorem subd6_1_25 : subd6_1 [-3, 3] = true := by decide +kernel
theorem subd6_1_26 : subd6_1 [-3, 4] = true := by decide +kernel
theorem subd6_1_27 : subd6_1 [-3, 5] = true := by decide +kernel
theorem subd6_1_28 : subd6_1 [-3, 6] = true := by decide +kernel
theorem subd6_1_29 : subd6_1 [-2, -5] = true := by decide +kernel
theorem subd6_1_30 : subd6_1 [-2, -4] = true := by decide +kernel
theorem subd6_1_31 : subd6_1 [-2, -3] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_cons.2 ⟨subd6_1_3, List.forall_mem_cons.2 ⟨subd6_1_4, List.forall_mem_cons.2 ⟨subd6_1_5, List.forall_mem_cons.2 ⟨subd6_1_6, List.forall_mem_cons.2 ⟨subd6_1_7, List.forall_mem_cons.2 ⟨subd6_1_8, List.forall_mem_cons.2 ⟨subd6_1_9, List.forall_mem_cons.2 ⟨subd6_1_10, List.forall_mem_cons.2 ⟨subd6_1_11, List.forall_mem_cons.2 ⟨subd6_1_12, List.forall_mem_cons.2 ⟨subd6_1_13, List.forall_mem_cons.2 ⟨subd6_1_14, List.forall_mem_cons.2 ⟨subd6_1_15, List.forall_mem_cons.2 ⟨subd6_1_16, List.forall_mem_cons.2 ⟨subd6_1_17, List.forall_mem_cons.2 ⟨subd6_1_18, List.forall_mem_cons.2 ⟨subd6_1_19, List.forall_mem_cons.2 ⟨subd6_1_20, List.forall_mem_cons.2 ⟨subd6_1_21, List.forall_mem_cons.2 ⟨subd6_1_22, List.forall_mem_cons.2 ⟨subd6_1_23, List.forall_mem_cons.2 ⟨subd6_1_24, List.forall_mem_cons.2 ⟨subd6_1_25, List.forall_mem_cons.2 ⟨subd6_1_26, List.forall_mem_cons.2 ⟨subd6_1_27, List.forall_mem_cons.2 ⟨subd6_1_28, List.forall_mem_cons.2 ⟨subd6_1_29, List.forall_mem_cons.2 ⟨subd6_1_30, List.forall_mem_cons.2 ⟨subd6_1_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_32 : subd6_1 [-2, -2] = true := by decide +kernel
theorem subd6_1_33 : subd6_1 [-2, -1] = true := by decide +kernel
theorem subd6_1_34 : subd6_1 [-2, 0] = true := by decide +kernel
theorem subd6_1_35 : subd6_1 [-2, 1] = true := by decide +kernel
theorem subd6_1_36 : subd6_1 [-2, 2] = true := by decide +kernel
theorem subd6_1_37 : subd6_1 [-2, 3] = true := by decide +kernel
theorem subd6_1_38 : subd6_1 [-2, 4] = true := by decide +kernel
theorem subd6_1_39 : subd6_1 [-2, 5] = true := by decide +kernel
theorem subd6_1_40 : subd6_1 [-2, 6] = true := by decide +kernel
theorem subd6_1_41 : subd6_1 [-1, -6] = true := by decide +kernel
theorem subd6_1_42 : subd6_1 [-1, -5] = true := by decide +kernel
theorem subd6_1_43 : subd6_1 [-1, -4] = true := by decide +kernel
theorem subd6_1_44 : subd6_1 [-1, -3] = true := by decide +kernel
theorem subd6_1_45 : subd6_1 [-1, -2] = true := by decide +kernel
theorem subd6_1_46 : subd6_1 [-1, -1] = true := by decide +kernel
theorem subd6_1_47 : subd6_1 [-1, 0] = true := by decide +kernel
theorem subd6_1_48 : subd6_1 [-1, 1] = true := by decide +kernel
theorem subd6_1_49 : subd6_1 [-1, 2] = true := by decide +kernel
theorem subd6_1_50 : subd6_1 [-1, 3] = true := by decide +kernel
theorem subd6_1_51 : subd6_1 [-1, 4] = true := by decide +kernel
theorem subd6_1_52 : subd6_1 [-1, 5] = true := by decide +kernel
theorem subd6_1_53 : subd6_1 [-1, 6] = true := by decide +kernel
theorem subd6_1_54 : subd6_1 [0, -6] = true := by decide +kernel
theorem subd6_1_55 : subd6_1 [0, -5] = true := by decide +kernel
theorem subd6_1_56 : subd6_1 [0, -4] = true := by decide +kernel
theorem subd6_1_57 : subd6_1 [0, -3] = true := by decide +kernel
theorem subd6_1_58 : subd6_1 [0, -2] = true := by decide +kernel
theorem subd6_1_59 : subd6_1 [0, -1] = true := by decide +kernel
theorem subd6_1_60 : subd6_1 [0, 0] = true := by decide +kernel
theorem subd6_1_61 : subd6_1 [0, 1] = true := by decide +kernel
theorem subd6_1_62 : subd6_1 [0, 2] = true := by decide +kernel
theorem subd6_1_63 : subd6_1 [0, 3] = true := by decide +kernel
theorem sbd6_1_1 : ∀ q ∈ blkd6_1_1, subd6_1 q = true := by
  unfold blkd6_1_1
  exact List.forall_mem_cons.2 ⟨subd6_1_32, List.forall_mem_cons.2 ⟨subd6_1_33, List.forall_mem_cons.2 ⟨subd6_1_34, List.forall_mem_cons.2 ⟨subd6_1_35, List.forall_mem_cons.2 ⟨subd6_1_36, List.forall_mem_cons.2 ⟨subd6_1_37, List.forall_mem_cons.2 ⟨subd6_1_38, List.forall_mem_cons.2 ⟨subd6_1_39, List.forall_mem_cons.2 ⟨subd6_1_40, List.forall_mem_cons.2 ⟨subd6_1_41, List.forall_mem_cons.2 ⟨subd6_1_42, List.forall_mem_cons.2 ⟨subd6_1_43, List.forall_mem_cons.2 ⟨subd6_1_44, List.forall_mem_cons.2 ⟨subd6_1_45, List.forall_mem_cons.2 ⟨subd6_1_46, List.forall_mem_cons.2 ⟨subd6_1_47, List.forall_mem_cons.2 ⟨subd6_1_48, List.forall_mem_cons.2 ⟨subd6_1_49, List.forall_mem_cons.2 ⟨subd6_1_50, List.forall_mem_cons.2 ⟨subd6_1_51, List.forall_mem_cons.2 ⟨subd6_1_52, List.forall_mem_cons.2 ⟨subd6_1_53, List.forall_mem_cons.2 ⟨subd6_1_54, List.forall_mem_cons.2 ⟨subd6_1_55, List.forall_mem_cons.2 ⟨subd6_1_56, List.forall_mem_cons.2 ⟨subd6_1_57, List.forall_mem_cons.2 ⟨subd6_1_58, List.forall_mem_cons.2 ⟨subd6_1_59, List.forall_mem_cons.2 ⟨subd6_1_60, List.forall_mem_cons.2 ⟨subd6_1_61, List.forall_mem_cons.2 ⟨subd6_1_62, List.forall_mem_cons.2 ⟨subd6_1_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C129
