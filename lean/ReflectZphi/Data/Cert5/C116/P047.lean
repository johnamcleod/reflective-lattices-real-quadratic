import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_4288 : subd9_1 [5, 2, 5] = true := by decide +kernel
theorem subd9_1_4289 : subd9_1 [5, 2, 6] = true := by decide +kernel
theorem subd9_1_4290 : subd9_1 [5, 2, 7] = true := by decide +kernel
theorem subd9_1_4291 : subd9_1 [5, 2, 8] = true := by decide +kernel
theorem subd9_1_4292 : subd9_1 [5, 2, 9] = true := by decide +kernel
theorem subd9_1_4293 : subd9_1 [5, 2, 10] = true := by decide +kernel
theorem subd9_1_4294 : subd9_1 [5, 3, -8] = true := by decide +kernel
theorem subd9_1_4295 : subd9_1 [5, 3, -7] = true := by decide +kernel
theorem subd9_1_4296 : subd9_1 [5, 3, -6] = true := by decide +kernel
theorem subd9_1_4297 : subd9_1 [5, 3, -5] = true := by decide +kernel
theorem subd9_1_4298 : subd9_1 [5, 3, -4] = true := by decide +kernel
theorem subd9_1_4299 : subd9_1 [5, 3, -3] = true := by decide +kernel
theorem subd9_1_4300 : subd9_1 [5, 3, -2] = true := by decide +kernel
theorem subd9_1_4301 : subd9_1 [5, 3, -1] = true := by decide +kernel
theorem subd9_1_4302 : subd9_1 [5, 3, 0] = true := by decide +kernel
theorem subd9_1_4303 : subd9_1 [5, 3, 1] = true := by decide +kernel
theorem subd9_1_4304 : subd9_1 [5, 3, 2] = true := by decide +kernel
theorem subd9_1_4305 : subd9_1 [5, 3, 3] = true := by decide +kernel
theorem subd9_1_4306 : subd9_1 [5, 3, 4] = true := by decide +kernel
theorem subd9_1_4307 : subd9_1 [5, 3, 5] = true := by decide +kernel
theorem subd9_1_4308 : subd9_1 [5, 3, 6] = true := by decide +kernel
theorem subd9_1_4309 : subd9_1 [5, 3, 7] = true := by decide +kernel
theorem subd9_1_4310 : subd9_1 [5, 3, 8] = true := by decide +kernel
theorem subd9_1_4311 : subd9_1 [5, 3, 9] = true := by decide +kernel
theorem subd9_1_4312 : subd9_1 [5, 3, 10] = true := by decide +kernel
theorem subd9_1_4313 : subd9_1 [5, 4, -8] = true := by decide +kernel
theorem subd9_1_4314 : subd9_1 [5, 4, -7] = true := by decide +kernel
theorem subd9_1_4315 : subd9_1 [5, 4, -6] = true := by decide +kernel
theorem subd9_1_4316 : subd9_1 [5, 4, -5] = true := by decide +kernel
theorem subd9_1_4317 : subd9_1 [5, 4, -4] = true := by decide +kernel
theorem subd9_1_4318 : subd9_1 [5, 4, -3] = true := by decide +kernel
theorem subd9_1_4319 : subd9_1 [5, 4, -2] = true := by decide +kernel
theorem sbd9_1_134 : ∀ q ∈ blkd9_1_134, subd9_1 q = true := by
  unfold blkd9_1_134
  exact List.forall_mem_cons.2 ⟨subd9_1_4288, List.forall_mem_cons.2 ⟨subd9_1_4289, List.forall_mem_cons.2 ⟨subd9_1_4290, List.forall_mem_cons.2 ⟨subd9_1_4291, List.forall_mem_cons.2 ⟨subd9_1_4292, List.forall_mem_cons.2 ⟨subd9_1_4293, List.forall_mem_cons.2 ⟨subd9_1_4294, List.forall_mem_cons.2 ⟨subd9_1_4295, List.forall_mem_cons.2 ⟨subd9_1_4296, List.forall_mem_cons.2 ⟨subd9_1_4297, List.forall_mem_cons.2 ⟨subd9_1_4298, List.forall_mem_cons.2 ⟨subd9_1_4299, List.forall_mem_cons.2 ⟨subd9_1_4300, List.forall_mem_cons.2 ⟨subd9_1_4301, List.forall_mem_cons.2 ⟨subd9_1_4302, List.forall_mem_cons.2 ⟨subd9_1_4303, List.forall_mem_cons.2 ⟨subd9_1_4304, List.forall_mem_cons.2 ⟨subd9_1_4305, List.forall_mem_cons.2 ⟨subd9_1_4306, List.forall_mem_cons.2 ⟨subd9_1_4307, List.forall_mem_cons.2 ⟨subd9_1_4308, List.forall_mem_cons.2 ⟨subd9_1_4309, List.forall_mem_cons.2 ⟨subd9_1_4310, List.forall_mem_cons.2 ⟨subd9_1_4311, List.forall_mem_cons.2 ⟨subd9_1_4312, List.forall_mem_cons.2 ⟨subd9_1_4313, List.forall_mem_cons.2 ⟨subd9_1_4314, List.forall_mem_cons.2 ⟨subd9_1_4315, List.forall_mem_cons.2 ⟨subd9_1_4316, List.forall_mem_cons.2 ⟨subd9_1_4317, List.forall_mem_cons.2 ⟨subd9_1_4318, List.forall_mem_cons.2 ⟨subd9_1_4319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4320 : subd9_1 [5, 4, -1] = true := by decide +kernel
theorem subd9_1_4321 : subd9_1 [5, 4, 0] = true := by decide +kernel
theorem subd9_1_4322 : subd9_1 [5, 4, 1] = true := by decide +kernel
theorem subd9_1_4323 : subd9_1 [5, 4, 2] = true := by decide +kernel
theorem subd9_1_4324 : subd9_1 [5, 4, 3] = true := by decide +kernel
theorem subd9_1_4325 : subd9_1 [5, 4, 4] = true := by decide +kernel
theorem subd9_1_4326 : subd9_1 [5, 4, 5] = true := by decide +kernel
theorem subd9_1_4327 : subd9_1 [5, 4, 6] = true := by decide +kernel
theorem subd9_1_4328 : subd9_1 [5, 4, 7] = true := by decide +kernel
theorem subd9_1_4329 : subd9_1 [5, 4, 8] = true := by decide +kernel
theorem subd9_1_4330 : subd9_1 [5, 4, 9] = true := by decide +kernel
theorem subd9_1_4331 : subd9_1 [5, 4, 10] = true := by decide +kernel
theorem subd9_1_4332 : subd9_1 [5, 5, -7] = true := by decide +kernel
theorem subd9_1_4333 : subd9_1 [5, 5, -6] = true := by decide +kernel
theorem subd9_1_4334 : subd9_1 [5, 5, -5] = true := by decide +kernel
theorem subd9_1_4335 : subd9_1 [5, 5, -4] = true := by decide +kernel
theorem subd9_1_4336 : subd9_1 [5, 5, -3] = true := by decide +kernel
theorem subd9_1_4337 : subd9_1 [5, 5, -2] = true := by decide +kernel
theorem subd9_1_4338 : subd9_1 [5, 5, -1] = true := by decide +kernel
theorem subd9_1_4339 : subd9_1 [5, 5, 0] = true := by decide +kernel
theorem subd9_1_4340 : subd9_1 [5, 5, 1] = true := by decide +kernel
theorem subd9_1_4341 : subd9_1 [5, 5, 2] = true := by decide +kernel
theorem subd9_1_4342 : subd9_1 [5, 5, 3] = true := by decide +kernel
theorem subd9_1_4343 : subd9_1 [5, 5, 4] = true := by decide +kernel
theorem subd9_1_4344 : subd9_1 [5, 5, 5] = true := by decide +kernel
theorem subd9_1_4345 : subd9_1 [5, 5, 6] = true := by decide +kernel
theorem subd9_1_4346 : subd9_1 [5, 5, 7] = true := by decide +kernel
theorem subd9_1_4347 : subd9_1 [5, 5, 8] = true := by decide +kernel
theorem subd9_1_4348 : subd9_1 [5, 5, 9] = true := by decide +kernel
theorem subd9_1_4349 : subd9_1 [5, 5, 10] = true := by decide +kernel
theorem subd9_1_4350 : subd9_1 [5, 5, 11] = true := by decide +kernel
theorem subd9_1_4351 : subd9_1 [5, 6, -6] = true := by decide +kernel
theorem sbd9_1_135 : ∀ q ∈ blkd9_1_135, subd9_1 q = true := by
  unfold blkd9_1_135
  exact List.forall_mem_cons.2 ⟨subd9_1_4320, List.forall_mem_cons.2 ⟨subd9_1_4321, List.forall_mem_cons.2 ⟨subd9_1_4322, List.forall_mem_cons.2 ⟨subd9_1_4323, List.forall_mem_cons.2 ⟨subd9_1_4324, List.forall_mem_cons.2 ⟨subd9_1_4325, List.forall_mem_cons.2 ⟨subd9_1_4326, List.forall_mem_cons.2 ⟨subd9_1_4327, List.forall_mem_cons.2 ⟨subd9_1_4328, List.forall_mem_cons.2 ⟨subd9_1_4329, List.forall_mem_cons.2 ⟨subd9_1_4330, List.forall_mem_cons.2 ⟨subd9_1_4331, List.forall_mem_cons.2 ⟨subd9_1_4332, List.forall_mem_cons.2 ⟨subd9_1_4333, List.forall_mem_cons.2 ⟨subd9_1_4334, List.forall_mem_cons.2 ⟨subd9_1_4335, List.forall_mem_cons.2 ⟨subd9_1_4336, List.forall_mem_cons.2 ⟨subd9_1_4337, List.forall_mem_cons.2 ⟨subd9_1_4338, List.forall_mem_cons.2 ⟨subd9_1_4339, List.forall_mem_cons.2 ⟨subd9_1_4340, List.forall_mem_cons.2 ⟨subd9_1_4341, List.forall_mem_cons.2 ⟨subd9_1_4342, List.forall_mem_cons.2 ⟨subd9_1_4343, List.forall_mem_cons.2 ⟨subd9_1_4344, List.forall_mem_cons.2 ⟨subd9_1_4345, List.forall_mem_cons.2 ⟨subd9_1_4346, List.forall_mem_cons.2 ⟨subd9_1_4347, List.forall_mem_cons.2 ⟨subd9_1_4348, List.forall_mem_cons.2 ⟨subd9_1_4349, List.forall_mem_cons.2 ⟨subd9_1_4350, List.forall_mem_cons.2 ⟨subd9_1_4351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4352 : subd9_1 [5, 6, -5] = true := by decide +kernel
theorem subd9_1_4353 : subd9_1 [5, 6, -4] = true := by decide +kernel
theorem subd9_1_4354 : subd9_1 [5, 6, -3] = true := by decide +kernel
theorem subd9_1_4355 : subd9_1 [5, 6, -2] = true := by decide +kernel
theorem subd9_1_4356 : subd9_1 [5, 6, -1] = true := by decide +kernel
theorem subd9_1_4357 : subd9_1 [5, 6, 0] = true := by decide +kernel
theorem subd9_1_4358 : subd9_1 [5, 6, 1] = true := by decide +kernel
theorem subd9_1_4359 : subd9_1 [5, 6, 2] = true := by decide +kernel
theorem subd9_1_4360 : subd9_1 [5, 6, 3] = true := by decide +kernel
theorem subd9_1_4361 : subd9_1 [5, 6, 4] = true := by decide +kernel
theorem subd9_1_4362 : subd9_1 [5, 6, 5] = true := by decide +kernel
theorem subd9_1_4363 : subd9_1 [5, 6, 6] = true := by decide +kernel
theorem subd9_1_4364 : subd9_1 [5, 6, 7] = true := by decide +kernel
theorem subd9_1_4365 : subd9_1 [5, 6, 8] = true := by decide +kernel
theorem subd9_1_4366 : subd9_1 [5, 6, 9] = true := by decide +kernel
theorem subd9_1_4367 : subd9_1 [5, 6, 10] = true := by decide +kernel
theorem subd9_1_4368 : subd9_1 [5, 6, 11] = true := by decide +kernel
theorem subd9_1_4369 : subd9_1 [5, 7, -6] = true := by decide +kernel
theorem subd9_1_4370 : subd9_1 [5, 7, -5] = true := by decide +kernel
theorem subd9_1_4371 : subd9_1 [5, 7, -4] = true := by decide +kernel
theorem subd9_1_4372 : subd9_1 [5, 7, -3] = true := by decide +kernel
theorem subd9_1_4373 : subd9_1 [5, 7, -2] = true := by decide +kernel
theorem subd9_1_4374 : subd9_1 [5, 7, -1] = true := by decide +kernel
theorem subd9_1_4375 : subd9_1 [5, 7, 0] = true := by decide +kernel
theorem subd9_1_4376 : subd9_1 [5, 7, 1] = true := by decide +kernel
theorem subd9_1_4377 : subd9_1 [5, 7, 2] = true := by decide +kernel
theorem subd9_1_4378 : subd9_1 [5, 7, 3] = true := by decide +kernel
theorem subd9_1_4379 : subd9_1 [5, 7, 4] = true := by decide +kernel
theorem subd9_1_4380 : subd9_1 [5, 7, 5] = true := by decide +kernel
theorem subd9_1_4381 : subd9_1 [5, 7, 6] = true := by decide +kernel
theorem subd9_1_4382 : subd9_1 [5, 7, 7] = true := by decide +kernel
theorem subd9_1_4383 : subd9_1 [5, 7, 8] = true := by decide +kernel
theorem sbd9_1_136 : ∀ q ∈ blkd9_1_136, subd9_1 q = true := by
  unfold blkd9_1_136
  exact List.forall_mem_cons.2 ⟨subd9_1_4352, List.forall_mem_cons.2 ⟨subd9_1_4353, List.forall_mem_cons.2 ⟨subd9_1_4354, List.forall_mem_cons.2 ⟨subd9_1_4355, List.forall_mem_cons.2 ⟨subd9_1_4356, List.forall_mem_cons.2 ⟨subd9_1_4357, List.forall_mem_cons.2 ⟨subd9_1_4358, List.forall_mem_cons.2 ⟨subd9_1_4359, List.forall_mem_cons.2 ⟨subd9_1_4360, List.forall_mem_cons.2 ⟨subd9_1_4361, List.forall_mem_cons.2 ⟨subd9_1_4362, List.forall_mem_cons.2 ⟨subd9_1_4363, List.forall_mem_cons.2 ⟨subd9_1_4364, List.forall_mem_cons.2 ⟨subd9_1_4365, List.forall_mem_cons.2 ⟨subd9_1_4366, List.forall_mem_cons.2 ⟨subd9_1_4367, List.forall_mem_cons.2 ⟨subd9_1_4368, List.forall_mem_cons.2 ⟨subd9_1_4369, List.forall_mem_cons.2 ⟨subd9_1_4370, List.forall_mem_cons.2 ⟨subd9_1_4371, List.forall_mem_cons.2 ⟨subd9_1_4372, List.forall_mem_cons.2 ⟨subd9_1_4373, List.forall_mem_cons.2 ⟨subd9_1_4374, List.forall_mem_cons.2 ⟨subd9_1_4375, List.forall_mem_cons.2 ⟨subd9_1_4376, List.forall_mem_cons.2 ⟨subd9_1_4377, List.forall_mem_cons.2 ⟨subd9_1_4378, List.forall_mem_cons.2 ⟨subd9_1_4379, List.forall_mem_cons.2 ⟨subd9_1_4380, List.forall_mem_cons.2 ⟨subd9_1_4381, List.forall_mem_cons.2 ⟨subd9_1_4382, List.forall_mem_cons.2 ⟨subd9_1_4383, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4384 : subd9_1 [5, 7, 9] = true := by decide +kernel
theorem subd9_1_4385 : subd9_1 [5, 7, 10] = true := by decide +kernel
theorem subd9_1_4386 : subd9_1 [5, 7, 11] = true := by decide +kernel
theorem subd9_1_4387 : subd9_1 [5, 8, -5] = true := by decide +kernel
theorem subd9_1_4388 : subd9_1 [5, 8, -4] = true := by decide +kernel
theorem subd9_1_4389 : subd9_1 [5, 8, -3] = true := by decide +kernel
theorem subd9_1_4390 : subd9_1 [5, 8, -2] = true := by decide +kernel
theorem subd9_1_4391 : subd9_1 [5, 8, -1] = true := by decide +kernel
theorem subd9_1_4392 : subd9_1 [5, 8, 0] = true := by decide +kernel
theorem subd9_1_4393 : subd9_1 [5, 8, 1] = true := by decide +kernel
theorem subd9_1_4394 : subd9_1 [5, 8, 2] = true := by decide +kernel
theorem subd9_1_4395 : subd9_1 [5, 8, 3] = true := by decide +kernel
theorem subd9_1_4396 : subd9_1 [5, 8, 4] = true := by decide +kernel
theorem subd9_1_4397 : subd9_1 [5, 8, 5] = true := by decide +kernel
theorem subd9_1_4398 : subd9_1 [5, 8, 6] = true := by decide +kernel
theorem subd9_1_4399 : subd9_1 [5, 8, 7] = true := by decide +kernel
theorem subd9_1_4400 : subd9_1 [5, 8, 8] = true := by decide +kernel
theorem subd9_1_4401 : subd9_1 [5, 8, 9] = true := by decide +kernel
theorem subd9_1_4402 : subd9_1 [5, 8, 10] = true := by decide +kernel
theorem subd9_1_4403 : subd9_1 [5, 8, 11] = true := by decide +kernel
theorem subd9_1_4404 : subd9_1 [5, 9, -3] = true := by decide +kernel
theorem subd9_1_4405 : subd9_1 [5, 9, -2] = true := by decide +kernel
theorem subd9_1_4406 : subd9_1 [5, 9, -1] = true := by decide +kernel
theorem subd9_1_4407 : subd9_1 [5, 9, 0] = true := by decide +kernel
theorem subd9_1_4408 : subd9_1 [5, 9, 1] = true := by decide +kernel
theorem subd9_1_4409 : subd9_1 [5, 9, 2] = true := by decide +kernel
theorem subd9_1_4410 : subd9_1 [5, 9, 3] = true := by decide +kernel
theorem subd9_1_4411 : subd9_1 [5, 9, 4] = true := by decide +kernel
theorem subd9_1_4412 : subd9_1 [5, 9, 5] = true := by decide +kernel
theorem subd9_1_4413 : subd9_1 [5, 9, 6] = true := by decide +kernel
theorem subd9_1_4414 : subd9_1 [5, 9, 7] = true := by decide +kernel
theorem subd9_1_4415 : subd9_1 [5, 9, 8] = true := by decide +kernel
theorem sbd9_1_137 : ∀ q ∈ blkd9_1_137, subd9_1 q = true := by
  unfold blkd9_1_137
  exact List.forall_mem_cons.2 ⟨subd9_1_4384, List.forall_mem_cons.2 ⟨subd9_1_4385, List.forall_mem_cons.2 ⟨subd9_1_4386, List.forall_mem_cons.2 ⟨subd9_1_4387, List.forall_mem_cons.2 ⟨subd9_1_4388, List.forall_mem_cons.2 ⟨subd9_1_4389, List.forall_mem_cons.2 ⟨subd9_1_4390, List.forall_mem_cons.2 ⟨subd9_1_4391, List.forall_mem_cons.2 ⟨subd9_1_4392, List.forall_mem_cons.2 ⟨subd9_1_4393, List.forall_mem_cons.2 ⟨subd9_1_4394, List.forall_mem_cons.2 ⟨subd9_1_4395, List.forall_mem_cons.2 ⟨subd9_1_4396, List.forall_mem_cons.2 ⟨subd9_1_4397, List.forall_mem_cons.2 ⟨subd9_1_4398, List.forall_mem_cons.2 ⟨subd9_1_4399, List.forall_mem_cons.2 ⟨subd9_1_4400, List.forall_mem_cons.2 ⟨subd9_1_4401, List.forall_mem_cons.2 ⟨subd9_1_4402, List.forall_mem_cons.2 ⟨subd9_1_4403, List.forall_mem_cons.2 ⟨subd9_1_4404, List.forall_mem_cons.2 ⟨subd9_1_4405, List.forall_mem_cons.2 ⟨subd9_1_4406, List.forall_mem_cons.2 ⟨subd9_1_4407, List.forall_mem_cons.2 ⟨subd9_1_4408, List.forall_mem_cons.2 ⟨subd9_1_4409, List.forall_mem_cons.2 ⟨subd9_1_4410, List.forall_mem_cons.2 ⟨subd9_1_4411, List.forall_mem_cons.2 ⟨subd9_1_4412, List.forall_mem_cons.2 ⟨subd9_1_4413, List.forall_mem_cons.2 ⟨subd9_1_4414, List.forall_mem_cons.2 ⟨subd9_1_4415, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4416 : subd9_1 [5, 9, 9] = true := by decide +kernel
theorem subd9_1_4417 : subd9_1 [5, 9, 10] = true := by decide +kernel
theorem subd9_1_4418 : subd9_1 [5, 10] = true := by decide +kernel
theorem subd9_1_4419 : subd9_1 [5, 11] = true := by decide +kernel
theorem subd9_1_4420 : subd9_1 [5, 12] = true := by decide +kernel
theorem subd9_1_4421 : subd9_1 [6, -9] = true := by decide +kernel
theorem subd9_1_4422 : subd9_1 [6, -8] = true := by decide +kernel
theorem subd9_1_4423 : subd9_1 [6, -7] = true := by decide +kernel
theorem subd9_1_4424 : subd9_1 [6, -6] = true := by decide +kernel
theorem subd9_1_4425 : subd9_1 [6, -5, -10] = true := by decide +kernel
theorem subd9_1_4426 : subd9_1 [6, -5, -9] = true := by decide +kernel
theorem subd9_1_4427 : subd9_1 [6, -5, -8] = true := by decide +kernel
theorem subd9_1_4428 : subd9_1 [6, -5, -7] = true := by decide +kernel
theorem subd9_1_4429 : subd9_1 [6, -5, -6] = true := by decide +kernel
theorem subd9_1_4430 : subd9_1 [6, -5, -5] = true := by decide +kernel
theorem subd9_1_4431 : subd9_1 [6, -5, -4] = true := by decide +kernel
theorem subd9_1_4432 : subd9_1 [6, -5, -3] = true := by decide +kernel
theorem subd9_1_4433 : subd9_1 [6, -5, -2] = true := by decide +kernel
theorem subd9_1_4434 : subd9_1 [6, -5, -1] = true := by decide +kernel
theorem subd9_1_4435 : subd9_1 [6, -5, 0] = true := by decide +kernel
theorem subd9_1_4436 : subd9_1 [6, -5, 1] = true := by decide +kernel
theorem subd9_1_4437 : subd9_1 [6, -5, 2] = true := by decide +kernel
theorem subd9_1_4438 : subd9_1 [6, -5, 3] = true := by decide +kernel
theorem subd9_1_4439 : subd9_1 [6, -5, 4] = true := by decide +kernel
theorem subd9_1_4440 : subd9_1 [6, -4, -10] = true := by decide +kernel
theorem subd9_1_4441 : subd9_1 [6, -4, -9] = true := by decide +kernel
theorem subd9_1_4442 : subd9_1 [6, -4, -8] = true := by decide +kernel
theorem subd9_1_4443 : subd9_1 [6, -4, -7] = true := by decide +kernel
theorem subd9_1_4444 : subd9_1 [6, -4, -6] = true := by decide +kernel
theorem subd9_1_4445 : subd9_1 [6, -4, -5] = true := by decide +kernel
theorem subd9_1_4446 : subd9_1 [6, -4, -4] = true := by decide +kernel
theorem subd9_1_4447 : subd9_1 [6, -4, -3] = true := by decide +kernel
theorem sbd9_1_138 : ∀ q ∈ blkd9_1_138, subd9_1 q = true := by
  unfold blkd9_1_138
  exact List.forall_mem_cons.2 ⟨subd9_1_4416, List.forall_mem_cons.2 ⟨subd9_1_4417, List.forall_mem_cons.2 ⟨subd9_1_4418, List.forall_mem_cons.2 ⟨subd9_1_4419, List.forall_mem_cons.2 ⟨subd9_1_4420, List.forall_mem_cons.2 ⟨subd9_1_4421, List.forall_mem_cons.2 ⟨subd9_1_4422, List.forall_mem_cons.2 ⟨subd9_1_4423, List.forall_mem_cons.2 ⟨subd9_1_4424, List.forall_mem_cons.2 ⟨subd9_1_4425, List.forall_mem_cons.2 ⟨subd9_1_4426, List.forall_mem_cons.2 ⟨subd9_1_4427, List.forall_mem_cons.2 ⟨subd9_1_4428, List.forall_mem_cons.2 ⟨subd9_1_4429, List.forall_mem_cons.2 ⟨subd9_1_4430, List.forall_mem_cons.2 ⟨subd9_1_4431, List.forall_mem_cons.2 ⟨subd9_1_4432, List.forall_mem_cons.2 ⟨subd9_1_4433, List.forall_mem_cons.2 ⟨subd9_1_4434, List.forall_mem_cons.2 ⟨subd9_1_4435, List.forall_mem_cons.2 ⟨subd9_1_4436, List.forall_mem_cons.2 ⟨subd9_1_4437, List.forall_mem_cons.2 ⟨subd9_1_4438, List.forall_mem_cons.2 ⟨subd9_1_4439, List.forall_mem_cons.2 ⟨subd9_1_4440, List.forall_mem_cons.2 ⟨subd9_1_4441, List.forall_mem_cons.2 ⟨subd9_1_4442, List.forall_mem_cons.2 ⟨subd9_1_4443, List.forall_mem_cons.2 ⟨subd9_1_4444, List.forall_mem_cons.2 ⟨subd9_1_4445, List.forall_mem_cons.2 ⟨subd9_1_4446, List.forall_mem_cons.2 ⟨subd9_1_4447, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4448 : subd9_1 [6, -4, -2] = true := by decide +kernel
theorem subd9_1_4449 : subd9_1 [6, -4, -1] = true := by decide +kernel
theorem subd9_1_4450 : subd9_1 [6, -4, 0] = true := by decide +kernel
theorem subd9_1_4451 : subd9_1 [6, -4, 1] = true := by decide +kernel
theorem subd9_1_4452 : subd9_1 [6, -4, 2] = true := by decide +kernel
theorem subd9_1_4453 : subd9_1 [6, -4, 3] = true := by decide +kernel
theorem subd9_1_4454 : subd9_1 [6, -4, 4] = true := by decide +kernel
theorem subd9_1_4455 : subd9_1 [6, -4, 5] = true := by decide +kernel
theorem subd9_1_4456 : subd9_1 [6, -3, -10] = true := by decide +kernel
theorem subd9_1_4457 : subd9_1 [6, -3, -9] = true := by decide +kernel
theorem subd9_1_4458 : subd9_1 [6, -3, -8] = true := by decide +kernel
theorem subd9_1_4459 : subd9_1 [6, -3, -7] = true := by decide +kernel
theorem subd9_1_4460 : subd9_1 [6, -3, -6] = true := by decide +kernel
theorem subd9_1_4461 : subd9_1 [6, -3, -5] = true := by decide +kernel
theorem subd9_1_4462 : subd9_1 [6, -3, -4] = true := by decide +kernel
theorem subd9_1_4463 : subd9_1 [6, -3, -3] = true := by decide +kernel
theorem subd9_1_4464 : subd9_1 [6, -3, -2] = true := by decide +kernel
theorem subd9_1_4465 : subd9_1 [6, -3, -1] = true := by decide +kernel
theorem subd9_1_4466 : subd9_1 [6, -3, 0] = true := by decide +kernel
theorem subd9_1_4467 : subd9_1 [6, -3, 1] = true := by decide +kernel
theorem subd9_1_4468 : subd9_1 [6, -3, 2] = true := by decide +kernel
theorem subd9_1_4469 : subd9_1 [6, -3, 3] = true := by decide +kernel
theorem subd9_1_4470 : subd9_1 [6, -3, 4] = true := by decide +kernel
theorem subd9_1_4471 : subd9_1 [6, -3, 5] = true := by decide +kernel
theorem subd9_1_4472 : subd9_1 [6, -3, 6] = true := by decide +kernel
theorem subd9_1_4473 : subd9_1 [6, -2, -10] = true := by decide +kernel
theorem subd9_1_4474 : subd9_1 [6, -2, -9] = true := by decide +kernel
theorem subd9_1_4475 : subd9_1 [6, -2, -8] = true := by decide +kernel
theorem subd9_1_4476 : subd9_1 [6, -2, -7] = true := by decide +kernel
theorem subd9_1_4477 : subd9_1 [6, -2, -6] = true := by decide +kernel
theorem subd9_1_4478 : subd9_1 [6, -2, -5] = true := by decide +kernel
theorem subd9_1_4479 : subd9_1 [6, -2, -4] = true := by decide +kernel
theorem sbd9_1_139 : ∀ q ∈ blkd9_1_139, subd9_1 q = true := by
  unfold blkd9_1_139
  exact List.forall_mem_cons.2 ⟨subd9_1_4448, List.forall_mem_cons.2 ⟨subd9_1_4449, List.forall_mem_cons.2 ⟨subd9_1_4450, List.forall_mem_cons.2 ⟨subd9_1_4451, List.forall_mem_cons.2 ⟨subd9_1_4452, List.forall_mem_cons.2 ⟨subd9_1_4453, List.forall_mem_cons.2 ⟨subd9_1_4454, List.forall_mem_cons.2 ⟨subd9_1_4455, List.forall_mem_cons.2 ⟨subd9_1_4456, List.forall_mem_cons.2 ⟨subd9_1_4457, List.forall_mem_cons.2 ⟨subd9_1_4458, List.forall_mem_cons.2 ⟨subd9_1_4459, List.forall_mem_cons.2 ⟨subd9_1_4460, List.forall_mem_cons.2 ⟨subd9_1_4461, List.forall_mem_cons.2 ⟨subd9_1_4462, List.forall_mem_cons.2 ⟨subd9_1_4463, List.forall_mem_cons.2 ⟨subd9_1_4464, List.forall_mem_cons.2 ⟨subd9_1_4465, List.forall_mem_cons.2 ⟨subd9_1_4466, List.forall_mem_cons.2 ⟨subd9_1_4467, List.forall_mem_cons.2 ⟨subd9_1_4468, List.forall_mem_cons.2 ⟨subd9_1_4469, List.forall_mem_cons.2 ⟨subd9_1_4470, List.forall_mem_cons.2 ⟨subd9_1_4471, List.forall_mem_cons.2 ⟨subd9_1_4472, List.forall_mem_cons.2 ⟨subd9_1_4473, List.forall_mem_cons.2 ⟨subd9_1_4474, List.forall_mem_cons.2 ⟨subd9_1_4475, List.forall_mem_cons.2 ⟨subd9_1_4476, List.forall_mem_cons.2 ⟨subd9_1_4477, List.forall_mem_cons.2 ⟨subd9_1_4478, List.forall_mem_cons.2 ⟨subd9_1_4479, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4480 : subd9_1 [6, -2, -3] = true := by decide +kernel
theorem subd9_1_4481 : subd9_1 [6, -2, -2] = true := by decide +kernel
theorem subd9_1_4482 : subd9_1 [6, -2, -1] = true := by decide +kernel
theorem subd9_1_4483 : subd9_1 [6, -2, 0] = true := by decide +kernel
theorem subd9_1_4484 : subd9_1 [6, -2, 1] = true := by decide +kernel
theorem subd9_1_4485 : subd9_1 [6, -2, 2] = true := by decide +kernel
theorem subd9_1_4486 : subd9_1 [6, -2, 3] = true := by decide +kernel
theorem subd9_1_4487 : subd9_1 [6, -2, 4] = true := by decide +kernel
theorem subd9_1_4488 : subd9_1 [6, -2, 5] = true := by decide +kernel
theorem subd9_1_4489 : subd9_1 [6, -2, 6] = true := by decide +kernel
theorem subd9_1_4490 : subd9_1 [6, -2, 7] = true := by decide +kernel
theorem subd9_1_4491 : subd9_1 [6, -1, -9] = true := by decide +kernel
theorem subd9_1_4492 : subd9_1 [6, -1, -8] = true := by decide +kernel
theorem subd9_1_4493 : subd9_1 [6, -1, -7] = true := by decide +kernel
theorem subd9_1_4494 : subd9_1 [6, -1, -6] = true := by decide +kernel
theorem subd9_1_4495 : subd9_1 [6, -1, -5] = true := by decide +kernel
theorem subd9_1_4496 : subd9_1 [6, -1, -4] = true := by decide +kernel
theorem subd9_1_4497 : subd9_1 [6, -1, -3] = true := by decide +kernel
theorem subd9_1_4498 : subd9_1 [6, -1, -2] = true := by decide +kernel
theorem subd9_1_4499 : subd9_1 [6, -1, -1] = true := by decide +kernel
theorem subd9_1_4500 : subd9_1 [6, -1, 0] = true := by decide +kernel
theorem subd9_1_4501 : subd9_1 [6, -1, 1] = true := by decide +kernel
theorem subd9_1_4502 : subd9_1 [6, -1, 2] = true := by decide +kernel
theorem subd9_1_4503 : subd9_1 [6, -1, 3] = true := by decide +kernel
theorem subd9_1_4504 : subd9_1 [6, -1, 4] = true := by decide +kernel
theorem subd9_1_4505 : subd9_1 [6, -1, 5] = true := by decide +kernel
theorem subd9_1_4506 : subd9_1 [6, -1, 6] = true := by decide +kernel
theorem subd9_1_4507 : subd9_1 [6, -1, 7] = true := by decide +kernel
theorem subd9_1_4508 : subd9_1 [6, -1, 8] = true := by decide +kernel
theorem subd9_1_4509 : subd9_1 [6, 0, -9] = true := by decide +kernel
theorem subd9_1_4510 : subd9_1 [6, 0, -8] = true := by decide +kernel
theorem subd9_1_4511 : subd9_1 [6, 0, -7] = true := by decide +kernel
theorem sbd9_1_140 : ∀ q ∈ blkd9_1_140, subd9_1 q = true := by
  unfold blkd9_1_140
  exact List.forall_mem_cons.2 ⟨subd9_1_4480, List.forall_mem_cons.2 ⟨subd9_1_4481, List.forall_mem_cons.2 ⟨subd9_1_4482, List.forall_mem_cons.2 ⟨subd9_1_4483, List.forall_mem_cons.2 ⟨subd9_1_4484, List.forall_mem_cons.2 ⟨subd9_1_4485, List.forall_mem_cons.2 ⟨subd9_1_4486, List.forall_mem_cons.2 ⟨subd9_1_4487, List.forall_mem_cons.2 ⟨subd9_1_4488, List.forall_mem_cons.2 ⟨subd9_1_4489, List.forall_mem_cons.2 ⟨subd9_1_4490, List.forall_mem_cons.2 ⟨subd9_1_4491, List.forall_mem_cons.2 ⟨subd9_1_4492, List.forall_mem_cons.2 ⟨subd9_1_4493, List.forall_mem_cons.2 ⟨subd9_1_4494, List.forall_mem_cons.2 ⟨subd9_1_4495, List.forall_mem_cons.2 ⟨subd9_1_4496, List.forall_mem_cons.2 ⟨subd9_1_4497, List.forall_mem_cons.2 ⟨subd9_1_4498, List.forall_mem_cons.2 ⟨subd9_1_4499, List.forall_mem_cons.2 ⟨subd9_1_4500, List.forall_mem_cons.2 ⟨subd9_1_4501, List.forall_mem_cons.2 ⟨subd9_1_4502, List.forall_mem_cons.2 ⟨subd9_1_4503, List.forall_mem_cons.2 ⟨subd9_1_4504, List.forall_mem_cons.2 ⟨subd9_1_4505, List.forall_mem_cons.2 ⟨subd9_1_4506, List.forall_mem_cons.2 ⟨subd9_1_4507, List.forall_mem_cons.2 ⟨subd9_1_4508, List.forall_mem_cons.2 ⟨subd9_1_4509, List.forall_mem_cons.2 ⟨subd9_1_4510, List.forall_mem_cons.2 ⟨subd9_1_4511, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4512 : subd9_1 [6, 0, -6] = true := by decide +kernel
theorem subd9_1_4513 : subd9_1 [6, 0, -5] = true := by decide +kernel
theorem subd9_1_4514 : subd9_1 [6, 0, -4] = true := by decide +kernel
theorem subd9_1_4515 : subd9_1 [6, 0, -3] = true := by decide +kernel
theorem subd9_1_4516 : subd9_1 [6, 0, -2] = true := by decide +kernel
theorem subd9_1_4517 : subd9_1 [6, 0, -1] = true := by decide +kernel
theorem subd9_1_4518 : subd9_1 [6, 0, 0] = true := by decide +kernel
theorem subd9_1_4519 : subd9_1 [6, 0, 1] = true := by decide +kernel
theorem subd9_1_4520 : subd9_1 [6, 0, 2] = true := by decide +kernel
theorem subd9_1_4521 : subd9_1 [6, 0, 3] = true := by decide +kernel
theorem subd9_1_4522 : subd9_1 [6, 0, 4] = true := by decide +kernel
theorem subd9_1_4523 : subd9_1 [6, 0, 5] = true := by decide +kernel
theorem subd9_1_4524 : subd9_1 [6, 0, 6] = true := by decide +kernel
theorem subd9_1_4525 : subd9_1 [6, 0, 7] = true := by decide +kernel
theorem subd9_1_4526 : subd9_1 [6, 0, 8] = true := by decide +kernel
theorem subd9_1_4527 : subd9_1 [6, 1, -9] = true := by decide +kernel
theorem subd9_1_4528 : subd9_1 [6, 1, -8] = true := by decide +kernel
theorem subd9_1_4529 : subd9_1 [6, 1, -7] = true := by decide +kernel
theorem subd9_1_4530 : subd9_1 [6, 1, -6] = true := by decide +kernel
theorem subd9_1_4531 : subd9_1 [6, 1, -5] = true := by decide +kernel
theorem subd9_1_4532 : subd9_1 [6, 1, -4] = true := by decide +kernel
theorem subd9_1_4533 : subd9_1 [6, 1, -3] = true := by decide +kernel
theorem subd9_1_4534 : subd9_1 [6, 1, -2] = true := by decide +kernel
theorem subd9_1_4535 : subd9_1 [6, 1, -1] = true := by decide +kernel
theorem subd9_1_4536 : subd9_1 [6, 1, 0] = true := by decide +kernel
theorem subd9_1_4537 : subd9_1 [6, 1, 1] = true := by decide +kernel
theorem subd9_1_4538 : subd9_1 [6, 1, 2] = true := by decide +kernel
theorem subd9_1_4539 : subd9_1 [6, 1, 3] = true := by decide +kernel
theorem subd9_1_4540 : subd9_1 [6, 1, 4] = true := by decide +kernel
theorem subd9_1_4541 : subd9_1 [6, 1, 5] = true := by decide +kernel
theorem subd9_1_4542 : subd9_1 [6, 1, 6] = true := by decide +kernel
theorem subd9_1_4543 : subd9_1 [6, 1, 7] = true := by decide +kernel
theorem sbd9_1_141 : ∀ q ∈ blkd9_1_141, subd9_1 q = true := by
  unfold blkd9_1_141
  exact List.forall_mem_cons.2 ⟨subd9_1_4512, List.forall_mem_cons.2 ⟨subd9_1_4513, List.forall_mem_cons.2 ⟨subd9_1_4514, List.forall_mem_cons.2 ⟨subd9_1_4515, List.forall_mem_cons.2 ⟨subd9_1_4516, List.forall_mem_cons.2 ⟨subd9_1_4517, List.forall_mem_cons.2 ⟨subd9_1_4518, List.forall_mem_cons.2 ⟨subd9_1_4519, List.forall_mem_cons.2 ⟨subd9_1_4520, List.forall_mem_cons.2 ⟨subd9_1_4521, List.forall_mem_cons.2 ⟨subd9_1_4522, List.forall_mem_cons.2 ⟨subd9_1_4523, List.forall_mem_cons.2 ⟨subd9_1_4524, List.forall_mem_cons.2 ⟨subd9_1_4525, List.forall_mem_cons.2 ⟨subd9_1_4526, List.forall_mem_cons.2 ⟨subd9_1_4527, List.forall_mem_cons.2 ⟨subd9_1_4528, List.forall_mem_cons.2 ⟨subd9_1_4529, List.forall_mem_cons.2 ⟨subd9_1_4530, List.forall_mem_cons.2 ⟨subd9_1_4531, List.forall_mem_cons.2 ⟨subd9_1_4532, List.forall_mem_cons.2 ⟨subd9_1_4533, List.forall_mem_cons.2 ⟨subd9_1_4534, List.forall_mem_cons.2 ⟨subd9_1_4535, List.forall_mem_cons.2 ⟨subd9_1_4536, List.forall_mem_cons.2 ⟨subd9_1_4537, List.forall_mem_cons.2 ⟨subd9_1_4538, List.forall_mem_cons.2 ⟨subd9_1_4539, List.forall_mem_cons.2 ⟨subd9_1_4540, List.forall_mem_cons.2 ⟨subd9_1_4541, List.forall_mem_cons.2 ⟨subd9_1_4542, List.forall_mem_cons.2 ⟨subd9_1_4543, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4544 : subd9_1 [6, 1, 8] = true := by decide +kernel
theorem subd9_1_4545 : subd9_1 [6, 1, 9] = true := by decide +kernel
theorem subd9_1_4546 : subd9_1 [6, 2, -8] = true := by decide +kernel
theorem subd9_1_4547 : subd9_1 [6, 2, -7] = true := by decide +kernel
theorem subd9_1_4548 : subd9_1 [6, 2, -6] = true := by decide +kernel
theorem subd9_1_4549 : subd9_1 [6, 2, -5] = true := by decide +kernel
theorem subd9_1_4550 : subd9_1 [6, 2, -4] = true := by decide +kernel
theorem subd9_1_4551 : subd9_1 [6, 2, -3] = true := by decide +kernel
theorem subd9_1_4552 : subd9_1 [6, 2, -2] = true := by decide +kernel
theorem subd9_1_4553 : subd9_1 [6, 2, -1] = true := by decide +kernel
theorem subd9_1_4554 : subd9_1 [6, 2, 0] = true := by decide +kernel
theorem subd9_1_4555 : subd9_1 [6, 2, 1] = true := by decide +kernel
theorem subd9_1_4556 : subd9_1 [6, 2, 2] = true := by decide +kernel
theorem subd9_1_4557 : subd9_1 [6, 2, 3] = true := by decide +kernel
theorem subd9_1_4558 : subd9_1 [6, 2, 4] = true := by decide +kernel
theorem subd9_1_4559 : subd9_1 [6, 2, 5] = true := by decide +kernel
theorem subd9_1_4560 : subd9_1 [6, 2, 6] = true := by decide +kernel
theorem subd9_1_4561 : subd9_1 [6, 2, 7] = true := by decide +kernel
theorem subd9_1_4562 : subd9_1 [6, 2, 8] = true := by decide +kernel
theorem subd9_1_4563 : subd9_1 [6, 2, 9] = true := by decide +kernel
theorem subd9_1_4564 : subd9_1 [6, 3, -8] = true := by decide +kernel
theorem subd9_1_4565 : subd9_1 [6, 3, -7] = true := by decide +kernel
theorem subd9_1_4566 : subd9_1 [6, 3, -6] = true := by decide +kernel
theorem subd9_1_4567 : subd9_1 [6, 3, -5] = true := by decide +kernel
theorem subd9_1_4568 : subd9_1 [6, 3, -4] = true := by decide +kernel
theorem subd9_1_4569 : subd9_1 [6, 3, -3] = true := by decide +kernel
theorem subd9_1_4570 : subd9_1 [6, 3, -2] = true := by decide +kernel
theorem subd9_1_4571 : subd9_1 [6, 3, -1] = true := by decide +kernel
theorem subd9_1_4572 : subd9_1 [6, 3, 0] = true := by decide +kernel
theorem subd9_1_4573 : subd9_1 [6, 3, 1] = true := by decide +kernel
theorem subd9_1_4574 : subd9_1 [6, 3, 2] = true := by decide +kernel
theorem subd9_1_4575 : subd9_1 [6, 3, 3] = true := by decide +kernel
theorem sbd9_1_142 : ∀ q ∈ blkd9_1_142, subd9_1 q = true := by
  unfold blkd9_1_142
  exact List.forall_mem_cons.2 ⟨subd9_1_4544, List.forall_mem_cons.2 ⟨subd9_1_4545, List.forall_mem_cons.2 ⟨subd9_1_4546, List.forall_mem_cons.2 ⟨subd9_1_4547, List.forall_mem_cons.2 ⟨subd9_1_4548, List.forall_mem_cons.2 ⟨subd9_1_4549, List.forall_mem_cons.2 ⟨subd9_1_4550, List.forall_mem_cons.2 ⟨subd9_1_4551, List.forall_mem_cons.2 ⟨subd9_1_4552, List.forall_mem_cons.2 ⟨subd9_1_4553, List.forall_mem_cons.2 ⟨subd9_1_4554, List.forall_mem_cons.2 ⟨subd9_1_4555, List.forall_mem_cons.2 ⟨subd9_1_4556, List.forall_mem_cons.2 ⟨subd9_1_4557, List.forall_mem_cons.2 ⟨subd9_1_4558, List.forall_mem_cons.2 ⟨subd9_1_4559, List.forall_mem_cons.2 ⟨subd9_1_4560, List.forall_mem_cons.2 ⟨subd9_1_4561, List.forall_mem_cons.2 ⟨subd9_1_4562, List.forall_mem_cons.2 ⟨subd9_1_4563, List.forall_mem_cons.2 ⟨subd9_1_4564, List.forall_mem_cons.2 ⟨subd9_1_4565, List.forall_mem_cons.2 ⟨subd9_1_4566, List.forall_mem_cons.2 ⟨subd9_1_4567, List.forall_mem_cons.2 ⟨subd9_1_4568, List.forall_mem_cons.2 ⟨subd9_1_4569, List.forall_mem_cons.2 ⟨subd9_1_4570, List.forall_mem_cons.2 ⟨subd9_1_4571, List.forall_mem_cons.2 ⟨subd9_1_4572, List.forall_mem_cons.2 ⟨subd9_1_4573, List.forall_mem_cons.2 ⟨subd9_1_4574, List.forall_mem_cons.2 ⟨subd9_1_4575, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4576 : subd9_1 [6, 3, 4] = true := by decide +kernel
theorem subd9_1_4577 : subd9_1 [6, 3, 5] = true := by decide +kernel
theorem subd9_1_4578 : subd9_1 [6, 3, 6] = true := by decide +kernel
theorem subd9_1_4579 : subd9_1 [6, 3, 7] = true := by decide +kernel
theorem subd9_1_4580 : subd9_1 [6, 3, 8] = true := by decide +kernel
theorem subd9_1_4581 : subd9_1 [6, 3, 9] = true := by decide +kernel
theorem subd9_1_4582 : subd9_1 [6, 3, 10] = true := by decide +kernel
theorem subd9_1_4583 : subd9_1 [6, 4, -7] = true := by decide +kernel
theorem subd9_1_4584 : subd9_1 [6, 4, -6] = true := by decide +kernel
theorem subd9_1_4585 : subd9_1 [6, 4, -5] = true := by decide +kernel
theorem subd9_1_4586 : subd9_1 [6, 4, -4] = true := by decide +kernel
theorem subd9_1_4587 : subd9_1 [6, 4, -3] = true := by decide +kernel
theorem subd9_1_4588 : subd9_1 [6, 4, -2] = true := by decide +kernel
theorem subd9_1_4589 : subd9_1 [6, 4, -1] = true := by decide +kernel
theorem subd9_1_4590 : subd9_1 [6, 4, 0] = true := by decide +kernel
theorem subd9_1_4591 : subd9_1 [6, 4, 1] = true := by decide +kernel
theorem subd9_1_4592 : subd9_1 [6, 4, 2] = true := by decide +kernel
theorem subd9_1_4593 : subd9_1 [6, 4, 3] = true := by decide +kernel
theorem subd9_1_4594 : subd9_1 [6, 4, 4] = true := by decide +kernel
theorem subd9_1_4595 : subd9_1 [6, 4, 5] = true := by decide +kernel
theorem subd9_1_4596 : subd9_1 [6, 4, 6] = true := by decide +kernel
theorem subd9_1_4597 : subd9_1 [6, 4, 7] = true := by decide +kernel
theorem subd9_1_4598 : subd9_1 [6, 4, 8] = true := by decide +kernel
theorem subd9_1_4599 : subd9_1 [6, 4, 9] = true := by decide +kernel
theorem subd9_1_4600 : subd9_1 [6, 4, 10] = true := by decide +kernel
theorem subd9_1_4601 : subd9_1 [6, 5, -7] = true := by decide +kernel
theorem subd9_1_4602 : subd9_1 [6, 5, -6] = true := by decide +kernel
theorem subd9_1_4603 : subd9_1 [6, 5, -5] = true := by decide +kernel
theorem subd9_1_4604 : subd9_1 [6, 5, -4] = true := by decide +kernel
theorem subd9_1_4605 : subd9_1 [6, 5, -3] = true := by decide +kernel
theorem subd9_1_4606 : subd9_1 [6, 5, -2] = true := by decide +kernel
theorem subd9_1_4607 : subd9_1 [6, 5, -1] = true := by decide +kernel
theorem sbd9_1_143 : ∀ q ∈ blkd9_1_143, subd9_1 q = true := by
  unfold blkd9_1_143
  exact List.forall_mem_cons.2 ⟨subd9_1_4576, List.forall_mem_cons.2 ⟨subd9_1_4577, List.forall_mem_cons.2 ⟨subd9_1_4578, List.forall_mem_cons.2 ⟨subd9_1_4579, List.forall_mem_cons.2 ⟨subd9_1_4580, List.forall_mem_cons.2 ⟨subd9_1_4581, List.forall_mem_cons.2 ⟨subd9_1_4582, List.forall_mem_cons.2 ⟨subd9_1_4583, List.forall_mem_cons.2 ⟨subd9_1_4584, List.forall_mem_cons.2 ⟨subd9_1_4585, List.forall_mem_cons.2 ⟨subd9_1_4586, List.forall_mem_cons.2 ⟨subd9_1_4587, List.forall_mem_cons.2 ⟨subd9_1_4588, List.forall_mem_cons.2 ⟨subd9_1_4589, List.forall_mem_cons.2 ⟨subd9_1_4590, List.forall_mem_cons.2 ⟨subd9_1_4591, List.forall_mem_cons.2 ⟨subd9_1_4592, List.forall_mem_cons.2 ⟨subd9_1_4593, List.forall_mem_cons.2 ⟨subd9_1_4594, List.forall_mem_cons.2 ⟨subd9_1_4595, List.forall_mem_cons.2 ⟨subd9_1_4596, List.forall_mem_cons.2 ⟨subd9_1_4597, List.forall_mem_cons.2 ⟨subd9_1_4598, List.forall_mem_cons.2 ⟨subd9_1_4599, List.forall_mem_cons.2 ⟨subd9_1_4600, List.forall_mem_cons.2 ⟨subd9_1_4601, List.forall_mem_cons.2 ⟨subd9_1_4602, List.forall_mem_cons.2 ⟨subd9_1_4603, List.forall_mem_cons.2 ⟨subd9_1_4604, List.forall_mem_cons.2 ⟨subd9_1_4605, List.forall_mem_cons.2 ⟨subd9_1_4606, List.forall_mem_cons.2 ⟨subd9_1_4607, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4608 : subd9_1 [6, 5, 0] = true := by decide +kernel
theorem subd9_1_4609 : subd9_1 [6, 5, 1] = true := by decide +kernel
theorem subd9_1_4610 : subd9_1 [6, 5, 2] = true := by decide +kernel
theorem subd9_1_4611 : subd9_1 [6, 5, 3] = true := by decide +kernel
theorem subd9_1_4612 : subd9_1 [6, 5, 4] = true := by decide +kernel
theorem subd9_1_4613 : subd9_1 [6, 5, 5] = true := by decide +kernel
theorem subd9_1_4614 : subd9_1 [6, 5, 6] = true := by decide +kernel
theorem subd9_1_4615 : subd9_1 [6, 5, 7] = true := by decide +kernel
theorem subd9_1_4616 : subd9_1 [6, 5, 8] = true := by decide +kernel
theorem subd9_1_4617 : subd9_1 [6, 5, 9] = true := by decide +kernel
theorem subd9_1_4618 : subd9_1 [6, 5, 10] = true := by decide +kernel
theorem subd9_1_4619 : subd9_1 [6, 6, -6] = true := by decide +kernel
theorem subd9_1_4620 : subd9_1 [6, 6, -5] = true := by decide +kernel
theorem subd9_1_4621 : subd9_1 [6, 6, -4] = true := by decide +kernel
theorem subd9_1_4622 : subd9_1 [6, 6, -3] = true := by decide +kernel
theorem subd9_1_4623 : subd9_1 [6, 6, -2] = true := by decide +kernel
theorem subd9_1_4624 : subd9_1 [6, 6, -1] = true := by decide +kernel
theorem subd9_1_4625 : subd9_1 [6, 6, 0] = true := by decide +kernel
theorem subd9_1_4626 : subd9_1 [6, 6, 1] = true := by decide +kernel
theorem subd9_1_4627 : subd9_1 [6, 6, 2] = true := by decide +kernel
theorem subd9_1_4628 : subd9_1 [6, 6, 3] = true := by decide +kernel
theorem subd9_1_4629 : subd9_1 [6, 6, 4] = true := by decide +kernel
theorem subd9_1_4630 : subd9_1 [6, 6, 5] = true := by decide +kernel
theorem subd9_1_4631 : subd9_1 [6, 6, 6] = true := by decide +kernel
theorem subd9_1_4632 : subd9_1 [6, 6, 7] = true := by decide +kernel
theorem subd9_1_4633 : subd9_1 [6, 6, 8] = true := by decide +kernel
theorem subd9_1_4634 : subd9_1 [6, 6, 9] = true := by decide +kernel
theorem subd9_1_4635 : subd9_1 [6, 6, 10] = true := by decide +kernel
theorem subd9_1_4636 : subd9_1 [6, 7, -5] = true := by decide +kernel
theorem subd9_1_4637 : subd9_1 [6, 7, -4] = true := by decide +kernel
theorem subd9_1_4638 : subd9_1 [6, 7, -3] = true := by decide +kernel
theorem subd9_1_4639 : subd9_1 [6, 7, -2] = true := by decide +kernel
theorem sbd9_1_144 : ∀ q ∈ blkd9_1_144, subd9_1 q = true := by
  unfold blkd9_1_144
  exact List.forall_mem_cons.2 ⟨subd9_1_4608, List.forall_mem_cons.2 ⟨subd9_1_4609, List.forall_mem_cons.2 ⟨subd9_1_4610, List.forall_mem_cons.2 ⟨subd9_1_4611, List.forall_mem_cons.2 ⟨subd9_1_4612, List.forall_mem_cons.2 ⟨subd9_1_4613, List.forall_mem_cons.2 ⟨subd9_1_4614, List.forall_mem_cons.2 ⟨subd9_1_4615, List.forall_mem_cons.2 ⟨subd9_1_4616, List.forall_mem_cons.2 ⟨subd9_1_4617, List.forall_mem_cons.2 ⟨subd9_1_4618, List.forall_mem_cons.2 ⟨subd9_1_4619, List.forall_mem_cons.2 ⟨subd9_1_4620, List.forall_mem_cons.2 ⟨subd9_1_4621, List.forall_mem_cons.2 ⟨subd9_1_4622, List.forall_mem_cons.2 ⟨subd9_1_4623, List.forall_mem_cons.2 ⟨subd9_1_4624, List.forall_mem_cons.2 ⟨subd9_1_4625, List.forall_mem_cons.2 ⟨subd9_1_4626, List.forall_mem_cons.2 ⟨subd9_1_4627, List.forall_mem_cons.2 ⟨subd9_1_4628, List.forall_mem_cons.2 ⟨subd9_1_4629, List.forall_mem_cons.2 ⟨subd9_1_4630, List.forall_mem_cons.2 ⟨subd9_1_4631, List.forall_mem_cons.2 ⟨subd9_1_4632, List.forall_mem_cons.2 ⟨subd9_1_4633, List.forall_mem_cons.2 ⟨subd9_1_4634, List.forall_mem_cons.2 ⟨subd9_1_4635, List.forall_mem_cons.2 ⟨subd9_1_4636, List.forall_mem_cons.2 ⟨subd9_1_4637, List.forall_mem_cons.2 ⟨subd9_1_4638, List.forall_mem_cons.2 ⟨subd9_1_4639, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4640 : subd9_1 [6, 7, -1] = true := by decide +kernel
theorem subd9_1_4641 : subd9_1 [6, 7, 0] = true := by decide +kernel
theorem subd9_1_4642 : subd9_1 [6, 7, 1] = true := by decide +kernel
theorem subd9_1_4643 : subd9_1 [6, 7, 2] = true := by decide +kernel
theorem subd9_1_4644 : subd9_1 [6, 7, 3] = true := by decide +kernel
theorem subd9_1_4645 : subd9_1 [6, 7, 4] = true := by decide +kernel
theorem subd9_1_4646 : subd9_1 [6, 7, 5] = true := by decide +kernel
theorem subd9_1_4647 : subd9_1 [6, 7, 6] = true := by decide +kernel
theorem subd9_1_4648 : subd9_1 [6, 7, 7] = true := by decide +kernel
theorem subd9_1_4649 : subd9_1 [6, 7, 8] = true := by decide +kernel
theorem subd9_1_4650 : subd9_1 [6, 7, 9] = true := by decide +kernel
theorem subd9_1_4651 : subd9_1 [6, 7, 10] = true := by decide +kernel
theorem subd9_1_4652 : subd9_1 [6, 8, -4] = true := by decide +kernel
theorem subd9_1_4653 : subd9_1 [6, 8, -3] = true := by decide +kernel
theorem subd9_1_4654 : subd9_1 [6, 8, -2] = true := by decide +kernel
theorem subd9_1_4655 : subd9_1 [6, 8, -1] = true := by decide +kernel
theorem subd9_1_4656 : subd9_1 [6, 8, 0] = true := by decide +kernel
theorem subd9_1_4657 : subd9_1 [6, 8, 1] = true := by decide +kernel
theorem subd9_1_4658 : subd9_1 [6, 8, 2] = true := by decide +kernel
theorem subd9_1_4659 : subd9_1 [6, 8, 3] = true := by decide +kernel
theorem subd9_1_4660 : subd9_1 [6, 8, 4] = true := by decide +kernel
theorem subd9_1_4661 : subd9_1 [6, 8, 5] = true := by decide +kernel
theorem subd9_1_4662 : subd9_1 [6, 8, 6] = true := by decide +kernel
theorem subd9_1_4663 : subd9_1 [6, 8, 7] = true := by decide +kernel
theorem subd9_1_4664 : subd9_1 [6, 8, 8] = true := by decide +kernel
theorem subd9_1_4665 : subd9_1 [6, 8, 9] = true := by decide +kernel
theorem subd9_1_4666 : subd9_1 [6, 8, 10] = true := by decide +kernel
theorem subd9_1_4667 : subd9_1 [6, 9] = true := by decide +kernel
theorem subd9_1_4668 : subd9_1 [6, 10] = true := by decide +kernel
theorem subd9_1_4669 : subd9_1 [6, 11] = true := by decide +kernel
theorem subd9_1_4670 : subd9_1 [6, 12] = true := by decide +kernel
theorem subd9_1_4671 : subd9_1 [7, -9] = true := by decide +kernel
theorem sbd9_1_145 : ∀ q ∈ blkd9_1_145, subd9_1 q = true := by
  unfold blkd9_1_145
  exact List.forall_mem_cons.2 ⟨subd9_1_4640, List.forall_mem_cons.2 ⟨subd9_1_4641, List.forall_mem_cons.2 ⟨subd9_1_4642, List.forall_mem_cons.2 ⟨subd9_1_4643, List.forall_mem_cons.2 ⟨subd9_1_4644, List.forall_mem_cons.2 ⟨subd9_1_4645, List.forall_mem_cons.2 ⟨subd9_1_4646, List.forall_mem_cons.2 ⟨subd9_1_4647, List.forall_mem_cons.2 ⟨subd9_1_4648, List.forall_mem_cons.2 ⟨subd9_1_4649, List.forall_mem_cons.2 ⟨subd9_1_4650, List.forall_mem_cons.2 ⟨subd9_1_4651, List.forall_mem_cons.2 ⟨subd9_1_4652, List.forall_mem_cons.2 ⟨subd9_1_4653, List.forall_mem_cons.2 ⟨subd9_1_4654, List.forall_mem_cons.2 ⟨subd9_1_4655, List.forall_mem_cons.2 ⟨subd9_1_4656, List.forall_mem_cons.2 ⟨subd9_1_4657, List.forall_mem_cons.2 ⟨subd9_1_4658, List.forall_mem_cons.2 ⟨subd9_1_4659, List.forall_mem_cons.2 ⟨subd9_1_4660, List.forall_mem_cons.2 ⟨subd9_1_4661, List.forall_mem_cons.2 ⟨subd9_1_4662, List.forall_mem_cons.2 ⟨subd9_1_4663, List.forall_mem_cons.2 ⟨subd9_1_4664, List.forall_mem_cons.2 ⟨subd9_1_4665, List.forall_mem_cons.2 ⟨subd9_1_4666, List.forall_mem_cons.2 ⟨subd9_1_4667, List.forall_mem_cons.2 ⟨subd9_1_4668, List.forall_mem_cons.2 ⟨subd9_1_4669, List.forall_mem_cons.2 ⟨subd9_1_4670, List.forall_mem_cons.2 ⟨subd9_1_4671, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4672 : subd9_1 [7, -8] = true := by decide +kernel
theorem subd9_1_4673 : subd9_1 [7, -7] = true := by decide +kernel
theorem subd9_1_4674 : subd9_1 [7, -6] = true := by decide +kernel
theorem subd9_1_4675 : subd9_1 [7, -5] = true := by decide +kernel
theorem subd9_1_4676 : subd9_1 [7, -4, -9] = true := by decide +kernel
theorem subd9_1_4677 : subd9_1 [7, -4, -8] = true := by decide +kernel
theorem subd9_1_4678 : subd9_1 [7, -4, -7] = true := by decide +kernel
theorem subd9_1_4679 : subd9_1 [7, -4, -6] = true := by decide +kernel
theorem subd9_1_4680 : subd9_1 [7, -4, -5] = true := by decide +kernel
theorem subd9_1_4681 : subd9_1 [7, -4, -4] = true := by decide +kernel
theorem subd9_1_4682 : subd9_1 [7, -4, -3] = true := by decide +kernel
theorem subd9_1_4683 : subd9_1 [7, -4, -2] = true := by decide +kernel
theorem subd9_1_4684 : subd9_1 [7, -4, -1] = true := by decide +kernel
theorem subd9_1_4685 : subd9_1 [7, -4, 0] = true := by decide +kernel
theorem subd9_1_4686 : subd9_1 [7, -4, 1] = true := by decide +kernel
theorem subd9_1_4687 : subd9_1 [7, -4, 2] = true := by decide +kernel
theorem subd9_1_4688 : subd9_1 [7, -4, 3] = true := by decide +kernel
theorem subd9_1_4689 : subd9_1 [7, -4, 4] = true := by decide +kernel
theorem subd9_1_4690 : subd9_1 [7, -4, 5] = true := by decide +kernel
theorem subd9_1_4691 : subd9_1 [7, -3, -9] = true := by decide +kernel
theorem subd9_1_4692 : subd9_1 [7, -3, -8] = true := by decide +kernel
theorem subd9_1_4693 : subd9_1 [7, -3, -7] = true := by decide +kernel
theorem subd9_1_4694 : subd9_1 [7, -3, -6] = true := by decide +kernel
theorem subd9_1_4695 : subd9_1 [7, -3, -5] = true := by decide +kernel
theorem subd9_1_4696 : subd9_1 [7, -3, -4] = true := by decide +kernel
theorem subd9_1_4697 : subd9_1 [7, -3, -3] = true := by decide +kernel
theorem subd9_1_4698 : subd9_1 [7, -3, -2] = true := by decide +kernel
theorem subd9_1_4699 : subd9_1 [7, -3, -1] = true := by decide +kernel
theorem subd9_1_4700 : subd9_1 [7, -3, 0] = true := by decide +kernel
theorem subd9_1_4701 : subd9_1 [7, -3, 1] = true := by decide +kernel
theorem subd9_1_4702 : subd9_1 [7, -3, 2] = true := by decide +kernel
theorem subd9_1_4703 : subd9_1 [7, -3, 3] = true := by decide +kernel
theorem sbd9_1_146 : ∀ q ∈ blkd9_1_146, subd9_1 q = true := by
  unfold blkd9_1_146
  exact List.forall_mem_cons.2 ⟨subd9_1_4672, List.forall_mem_cons.2 ⟨subd9_1_4673, List.forall_mem_cons.2 ⟨subd9_1_4674, List.forall_mem_cons.2 ⟨subd9_1_4675, List.forall_mem_cons.2 ⟨subd9_1_4676, List.forall_mem_cons.2 ⟨subd9_1_4677, List.forall_mem_cons.2 ⟨subd9_1_4678, List.forall_mem_cons.2 ⟨subd9_1_4679, List.forall_mem_cons.2 ⟨subd9_1_4680, List.forall_mem_cons.2 ⟨subd9_1_4681, List.forall_mem_cons.2 ⟨subd9_1_4682, List.forall_mem_cons.2 ⟨subd9_1_4683, List.forall_mem_cons.2 ⟨subd9_1_4684, List.forall_mem_cons.2 ⟨subd9_1_4685, List.forall_mem_cons.2 ⟨subd9_1_4686, List.forall_mem_cons.2 ⟨subd9_1_4687, List.forall_mem_cons.2 ⟨subd9_1_4688, List.forall_mem_cons.2 ⟨subd9_1_4689, List.forall_mem_cons.2 ⟨subd9_1_4690, List.forall_mem_cons.2 ⟨subd9_1_4691, List.forall_mem_cons.2 ⟨subd9_1_4692, List.forall_mem_cons.2 ⟨subd9_1_4693, List.forall_mem_cons.2 ⟨subd9_1_4694, List.forall_mem_cons.2 ⟨subd9_1_4695, List.forall_mem_cons.2 ⟨subd9_1_4696, List.forall_mem_cons.2 ⟨subd9_1_4697, List.forall_mem_cons.2 ⟨subd9_1_4698, List.forall_mem_cons.2 ⟨subd9_1_4699, List.forall_mem_cons.2 ⟨subd9_1_4700, List.forall_mem_cons.2 ⟨subd9_1_4701, List.forall_mem_cons.2 ⟨subd9_1_4702, List.forall_mem_cons.2 ⟨subd9_1_4703, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4704 : subd9_1 [7, -3, 4] = true := by decide +kernel
theorem subd9_1_4705 : subd9_1 [7, -3, 5] = true := by decide +kernel
theorem subd9_1_4706 : subd9_1 [7, -3, 6] = true := by decide +kernel
theorem subd9_1_4707 : subd9_1 [7, -2, -9] = true := by decide +kernel
theorem subd9_1_4708 : subd9_1 [7, -2, -8] = true := by decide +kernel
theorem subd9_1_4709 : subd9_1 [7, -2, -7] = true := by decide +kernel
theorem subd9_1_4710 : subd9_1 [7, -2, -6] = true := by decide +kernel
theorem subd9_1_4711 : subd9_1 [7, -2, -5] = true := by decide +kernel
theorem subd9_1_4712 : subd9_1 [7, -2, -4] = true := by decide +kernel
theorem subd9_1_4713 : subd9_1 [7, -2, -3] = true := by decide +kernel
theorem subd9_1_4714 : subd9_1 [7, -2, -2] = true := by decide +kernel
theorem subd9_1_4715 : subd9_1 [7, -2, -1] = true := by decide +kernel
theorem subd9_1_4716 : subd9_1 [7, -2, 0] = true := by decide +kernel
theorem subd9_1_4717 : subd9_1 [7, -2, 1] = true := by decide +kernel
theorem subd9_1_4718 : subd9_1 [7, -2, 2] = true := by decide +kernel
theorem subd9_1_4719 : subd9_1 [7, -2, 3] = true := by decide +kernel
theorem subd9_1_4720 : subd9_1 [7, -2, 4] = true := by decide +kernel
theorem subd9_1_4721 : subd9_1 [7, -2, 5] = true := by decide +kernel
theorem subd9_1_4722 : subd9_1 [7, -2, 6] = true := by decide +kernel
theorem subd9_1_4723 : subd9_1 [7, -1, -9] = true := by decide +kernel
theorem subd9_1_4724 : subd9_1 [7, -1, -8] = true := by decide +kernel
theorem subd9_1_4725 : subd9_1 [7, -1, -7] = true := by decide +kernel
theorem subd9_1_4726 : subd9_1 [7, -1, -6] = true := by decide +kernel
theorem subd9_1_4727 : subd9_1 [7, -1, -5] = true := by decide +kernel
theorem subd9_1_4728 : subd9_1 [7, -1, -4] = true := by decide +kernel
theorem subd9_1_4729 : subd9_1 [7, -1, -3] = true := by decide +kernel
theorem subd9_1_4730 : subd9_1 [7, -1, -2] = true := by decide +kernel
theorem subd9_1_4731 : subd9_1 [7, -1, -1] = true := by decide +kernel
theorem subd9_1_4732 : subd9_1 [7, -1, 0] = true := by decide +kernel
theorem subd9_1_4733 : subd9_1 [7, -1, 1] = true := by decide +kernel
theorem subd9_1_4734 : subd9_1 [7, -1, 2] = true := by decide +kernel
theorem subd9_1_4735 : subd9_1 [7, -1, 3] = true := by decide +kernel
theorem sbd9_1_147 : ∀ q ∈ blkd9_1_147, subd9_1 q = true := by
  unfold blkd9_1_147
  exact List.forall_mem_cons.2 ⟨subd9_1_4704, List.forall_mem_cons.2 ⟨subd9_1_4705, List.forall_mem_cons.2 ⟨subd9_1_4706, List.forall_mem_cons.2 ⟨subd9_1_4707, List.forall_mem_cons.2 ⟨subd9_1_4708, List.forall_mem_cons.2 ⟨subd9_1_4709, List.forall_mem_cons.2 ⟨subd9_1_4710, List.forall_mem_cons.2 ⟨subd9_1_4711, List.forall_mem_cons.2 ⟨subd9_1_4712, List.forall_mem_cons.2 ⟨subd9_1_4713, List.forall_mem_cons.2 ⟨subd9_1_4714, List.forall_mem_cons.2 ⟨subd9_1_4715, List.forall_mem_cons.2 ⟨subd9_1_4716, List.forall_mem_cons.2 ⟨subd9_1_4717, List.forall_mem_cons.2 ⟨subd9_1_4718, List.forall_mem_cons.2 ⟨subd9_1_4719, List.forall_mem_cons.2 ⟨subd9_1_4720, List.forall_mem_cons.2 ⟨subd9_1_4721, List.forall_mem_cons.2 ⟨subd9_1_4722, List.forall_mem_cons.2 ⟨subd9_1_4723, List.forall_mem_cons.2 ⟨subd9_1_4724, List.forall_mem_cons.2 ⟨subd9_1_4725, List.forall_mem_cons.2 ⟨subd9_1_4726, List.forall_mem_cons.2 ⟨subd9_1_4727, List.forall_mem_cons.2 ⟨subd9_1_4728, List.forall_mem_cons.2 ⟨subd9_1_4729, List.forall_mem_cons.2 ⟨subd9_1_4730, List.forall_mem_cons.2 ⟨subd9_1_4731, List.forall_mem_cons.2 ⟨subd9_1_4732, List.forall_mem_cons.2 ⟨subd9_1_4733, List.forall_mem_cons.2 ⟨subd9_1_4734, List.forall_mem_cons.2 ⟨subd9_1_4735, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4736 : subd9_1 [7, -1, 4] = true := by decide +kernel
theorem subd9_1_4737 : subd9_1 [7, -1, 5] = true := by decide +kernel
theorem subd9_1_4738 : subd9_1 [7, -1, 6] = true := by decide +kernel
theorem subd9_1_4739 : subd9_1 [7, -1, 7] = true := by decide +kernel
theorem subd9_1_4740 : subd9_1 [7, 0, -9] = true := by decide +kernel
theorem subd9_1_4741 : subd9_1 [7, 0, -8] = true := by decide +kernel
theorem subd9_1_4742 : subd9_1 [7, 0, -7] = true := by decide +kernel
theorem subd9_1_4743 : subd9_1 [7, 0, -6] = true := by decide +kernel
theorem subd9_1_4744 : subd9_1 [7, 0, -5] = true := by decide +kernel
theorem subd9_1_4745 : subd9_1 [7, 0, -4] = true := by decide +kernel
theorem subd9_1_4746 : subd9_1 [7, 0, -3] = true := by decide +kernel
theorem subd9_1_4747 : subd9_1 [7, 0, -2] = true := by decide +kernel
theorem subd9_1_4748 : subd9_1 [7, 0, -1] = true := by decide +kernel
theorem subd9_1_4749 : subd9_1 [7, 0, 0] = true := by decide +kernel
theorem subd9_1_4750 : subd9_1 [7, 0, 1] = true := by decide +kernel
theorem subd9_1_4751 : subd9_1 [7, 0, 2] = true := by decide +kernel
theorem subd9_1_4752 : subd9_1 [7, 0, 3] = true := by decide +kernel
theorem subd9_1_4753 : subd9_1 [7, 0, 4] = true := by decide +kernel
theorem subd9_1_4754 : subd9_1 [7, 0, 5] = true := by decide +kernel
theorem subd9_1_4755 : subd9_1 [7, 0, 6] = true := by decide +kernel
theorem subd9_1_4756 : subd9_1 [7, 0, 7] = true := by decide +kernel
theorem subd9_1_4757 : subd9_1 [7, 0, 8] = true := by decide +kernel
theorem subd9_1_4758 : subd9_1 [7, 1, -8] = true := by decide +kernel
theorem subd9_1_4759 : subd9_1 [7, 1, -7] = true := by decide +kernel
theorem subd9_1_4760 : subd9_1 [7, 1, -6] = true := by decide +kernel
theorem subd9_1_4761 : subd9_1 [7, 1, -5] = true := by decide +kernel
theorem subd9_1_4762 : subd9_1 [7, 1, -4] = true := by decide +kernel
theorem subd9_1_4763 : subd9_1 [7, 1, -3] = true := by decide +kernel
theorem subd9_1_4764 : subd9_1 [7, 1, -2] = true := by decide +kernel
theorem subd9_1_4765 : subd9_1 [7, 1, -1] = true := by decide +kernel
theorem subd9_1_4766 : subd9_1 [7, 1, 0] = true := by decide +kernel
theorem subd9_1_4767 : subd9_1 [7, 1, 1] = true := by decide +kernel
theorem sbd9_1_148 : ∀ q ∈ blkd9_1_148, subd9_1 q = true := by
  unfold blkd9_1_148
  exact List.forall_mem_cons.2 ⟨subd9_1_4736, List.forall_mem_cons.2 ⟨subd9_1_4737, List.forall_mem_cons.2 ⟨subd9_1_4738, List.forall_mem_cons.2 ⟨subd9_1_4739, List.forall_mem_cons.2 ⟨subd9_1_4740, List.forall_mem_cons.2 ⟨subd9_1_4741, List.forall_mem_cons.2 ⟨subd9_1_4742, List.forall_mem_cons.2 ⟨subd9_1_4743, List.forall_mem_cons.2 ⟨subd9_1_4744, List.forall_mem_cons.2 ⟨subd9_1_4745, List.forall_mem_cons.2 ⟨subd9_1_4746, List.forall_mem_cons.2 ⟨subd9_1_4747, List.forall_mem_cons.2 ⟨subd9_1_4748, List.forall_mem_cons.2 ⟨subd9_1_4749, List.forall_mem_cons.2 ⟨subd9_1_4750, List.forall_mem_cons.2 ⟨subd9_1_4751, List.forall_mem_cons.2 ⟨subd9_1_4752, List.forall_mem_cons.2 ⟨subd9_1_4753, List.forall_mem_cons.2 ⟨subd9_1_4754, List.forall_mem_cons.2 ⟨subd9_1_4755, List.forall_mem_cons.2 ⟨subd9_1_4756, List.forall_mem_cons.2 ⟨subd9_1_4757, List.forall_mem_cons.2 ⟨subd9_1_4758, List.forall_mem_cons.2 ⟨subd9_1_4759, List.forall_mem_cons.2 ⟨subd9_1_4760, List.forall_mem_cons.2 ⟨subd9_1_4761, List.forall_mem_cons.2 ⟨subd9_1_4762, List.forall_mem_cons.2 ⟨subd9_1_4763, List.forall_mem_cons.2 ⟨subd9_1_4764, List.forall_mem_cons.2 ⟨subd9_1_4765, List.forall_mem_cons.2 ⟨subd9_1_4766, List.forall_mem_cons.2 ⟨subd9_1_4767, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4768 : subd9_1 [7, 1, 2] = true := by decide +kernel
theorem subd9_1_4769 : subd9_1 [7, 1, 3] = true := by decide +kernel
theorem subd9_1_4770 : subd9_1 [7, 1, 4] = true := by decide +kernel
theorem subd9_1_4771 : subd9_1 [7, 1, 5] = true := by decide +kernel
theorem subd9_1_4772 : subd9_1 [7, 1, 6] = true := by decide +kernel
theorem subd9_1_4773 : subd9_1 [7, 1, 7] = true := by decide +kernel
theorem subd9_1_4774 : subd9_1 [7, 1, 8] = true := by decide +kernel
theorem subd9_1_4775 : subd9_1 [7, 2, -8] = true := by decide +kernel
theorem subd9_1_4776 : subd9_1 [7, 2, -7] = true := by decide +kernel
theorem subd9_1_4777 : subd9_1 [7, 2, -6] = true := by decide +kernel
theorem subd9_1_4778 : subd9_1 [7, 2, -5] = true := by decide +kernel
theorem subd9_1_4779 : subd9_1 [7, 2, -4] = true := by decide +kernel
theorem subd9_1_4780 : subd9_1 [7, 2, -3] = true := by decide +kernel
theorem subd9_1_4781 : subd9_1 [7, 2, -2] = true := by decide +kernel
theorem subd9_1_4782 : subd9_1 [7, 2, -1] = true := by decide +kernel
theorem subd9_1_4783 : subd9_1 [7, 2, 0] = true := by decide +kernel
theorem subd9_1_4784 : subd9_1 [7, 2, 1] = true := by decide +kernel
theorem subd9_1_4785 : subd9_1 [7, 2, 2] = true := by decide +kernel
theorem subd9_1_4786 : subd9_1 [7, 2, 3] = true := by decide +kernel
theorem subd9_1_4787 : subd9_1 [7, 2, 4] = true := by decide +kernel
theorem subd9_1_4788 : subd9_1 [7, 2, 5] = true := by decide +kernel
theorem subd9_1_4789 : subd9_1 [7, 2, 6] = true := by decide +kernel
theorem subd9_1_4790 : subd9_1 [7, 2, 7] = true := by decide +kernel
theorem subd9_1_4791 : subd9_1 [7, 2, 8] = true := by decide +kernel
theorem subd9_1_4792 : subd9_1 [7, 2, 9] = true := by decide +kernel
theorem subd9_1_4793 : subd9_1 [7, 3, -7] = true := by decide +kernel
theorem subd9_1_4794 : subd9_1 [7, 3, -6] = true := by decide +kernel
theorem subd9_1_4795 : subd9_1 [7, 3, -5] = true := by decide +kernel
theorem subd9_1_4796 : subd9_1 [7, 3, -4] = true := by decide +kernel
theorem subd9_1_4797 : subd9_1 [7, 3, -3] = true := by decide +kernel
theorem subd9_1_4798 : subd9_1 [7, 3, -2] = true := by decide +kernel
theorem subd9_1_4799 : subd9_1 [7, 3, -1] = true := by decide +kernel
theorem sbd9_1_149 : ∀ q ∈ blkd9_1_149, subd9_1 q = true := by
  unfold blkd9_1_149
  exact List.forall_mem_cons.2 ⟨subd9_1_4768, List.forall_mem_cons.2 ⟨subd9_1_4769, List.forall_mem_cons.2 ⟨subd9_1_4770, List.forall_mem_cons.2 ⟨subd9_1_4771, List.forall_mem_cons.2 ⟨subd9_1_4772, List.forall_mem_cons.2 ⟨subd9_1_4773, List.forall_mem_cons.2 ⟨subd9_1_4774, List.forall_mem_cons.2 ⟨subd9_1_4775, List.forall_mem_cons.2 ⟨subd9_1_4776, List.forall_mem_cons.2 ⟨subd9_1_4777, List.forall_mem_cons.2 ⟨subd9_1_4778, List.forall_mem_cons.2 ⟨subd9_1_4779, List.forall_mem_cons.2 ⟨subd9_1_4780, List.forall_mem_cons.2 ⟨subd9_1_4781, List.forall_mem_cons.2 ⟨subd9_1_4782, List.forall_mem_cons.2 ⟨subd9_1_4783, List.forall_mem_cons.2 ⟨subd9_1_4784, List.forall_mem_cons.2 ⟨subd9_1_4785, List.forall_mem_cons.2 ⟨subd9_1_4786, List.forall_mem_cons.2 ⟨subd9_1_4787, List.forall_mem_cons.2 ⟨subd9_1_4788, List.forall_mem_cons.2 ⟨subd9_1_4789, List.forall_mem_cons.2 ⟨subd9_1_4790, List.forall_mem_cons.2 ⟨subd9_1_4791, List.forall_mem_cons.2 ⟨subd9_1_4792, List.forall_mem_cons.2 ⟨subd9_1_4793, List.forall_mem_cons.2 ⟨subd9_1_4794, List.forall_mem_cons.2 ⟨subd9_1_4795, List.forall_mem_cons.2 ⟨subd9_1_4796, List.forall_mem_cons.2 ⟨subd9_1_4797, List.forall_mem_cons.2 ⟨subd9_1_4798, List.forall_mem_cons.2 ⟨subd9_1_4799, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4800 : subd9_1 [7, 3, 0] = true := by decide +kernel
theorem subd9_1_4801 : subd9_1 [7, 3, 1] = true := by decide +kernel
theorem subd9_1_4802 : subd9_1 [7, 3, 2] = true := by decide +kernel
theorem subd9_1_4803 : subd9_1 [7, 3, 3] = true := by decide +kernel
theorem subd9_1_4804 : subd9_1 [7, 3, 4] = true := by decide +kernel
theorem subd9_1_4805 : subd9_1 [7, 3, 5] = true := by decide +kernel
theorem subd9_1_4806 : subd9_1 [7, 3, 6] = true := by decide +kernel
theorem subd9_1_4807 : subd9_1 [7, 3, 7] = true := by decide +kernel
theorem subd9_1_4808 : subd9_1 [7, 3, 8] = true := by decide +kernel
theorem subd9_1_4809 : subd9_1 [7, 3, 9] = true := by decide +kernel
theorem subd9_1_4810 : subd9_1 [7, 4, -7] = true := by decide +kernel
theorem subd9_1_4811 : subd9_1 [7, 4, -6] = true := by decide +kernel
theorem subd9_1_4812 : subd9_1 [7, 4, -5] = true := by decide +kernel
theorem subd9_1_4813 : subd9_1 [7, 4, -4] = true := by decide +kernel
theorem subd9_1_4814 : subd9_1 [7, 4, -3] = true := by decide +kernel
theorem subd9_1_4815 : subd9_1 [7, 4, -2] = true := by decide +kernel
theorem subd9_1_4816 : subd9_1 [7, 4, -1] = true := by decide +kernel
theorem subd9_1_4817 : subd9_1 [7, 4, 0] = true := by decide +kernel
theorem subd9_1_4818 : subd9_1 [7, 4, 1] = true := by decide +kernel
theorem subd9_1_4819 : subd9_1 [7, 4, 2] = true := by decide +kernel
theorem subd9_1_4820 : subd9_1 [7, 4, 3] = true := by decide +kernel
theorem subd9_1_4821 : subd9_1 [7, 4, 4] = true := by decide +kernel
theorem subd9_1_4822 : subd9_1 [7, 4, 5] = true := by decide +kernel
theorem subd9_1_4823 : subd9_1 [7, 4, 6] = true := by decide +kernel
theorem subd9_1_4824 : subd9_1 [7, 4, 7] = true := by decide +kernel
theorem subd9_1_4825 : subd9_1 [7, 4, 8] = true := by decide +kernel
theorem subd9_1_4826 : subd9_1 [7, 4, 9] = true := by decide +kernel
theorem subd9_1_4827 : subd9_1 [7, 4, 10] = true := by decide +kernel
theorem subd9_1_4828 : subd9_1 [7, 5, -6] = true := by decide +kernel
theorem subd9_1_4829 : subd9_1 [7, 5, -5] = true := by decide +kernel
theorem subd9_1_4830 : subd9_1 [7, 5, -4] = true := by decide +kernel
theorem subd9_1_4831 : subd9_1 [7, 5, -3] = true := by decide +kernel
theorem sbd9_1_150 : ∀ q ∈ blkd9_1_150, subd9_1 q = true := by
  unfold blkd9_1_150
  exact List.forall_mem_cons.2 ⟨subd9_1_4800, List.forall_mem_cons.2 ⟨subd9_1_4801, List.forall_mem_cons.2 ⟨subd9_1_4802, List.forall_mem_cons.2 ⟨subd9_1_4803, List.forall_mem_cons.2 ⟨subd9_1_4804, List.forall_mem_cons.2 ⟨subd9_1_4805, List.forall_mem_cons.2 ⟨subd9_1_4806, List.forall_mem_cons.2 ⟨subd9_1_4807, List.forall_mem_cons.2 ⟨subd9_1_4808, List.forall_mem_cons.2 ⟨subd9_1_4809, List.forall_mem_cons.2 ⟨subd9_1_4810, List.forall_mem_cons.2 ⟨subd9_1_4811, List.forall_mem_cons.2 ⟨subd9_1_4812, List.forall_mem_cons.2 ⟨subd9_1_4813, List.forall_mem_cons.2 ⟨subd9_1_4814, List.forall_mem_cons.2 ⟨subd9_1_4815, List.forall_mem_cons.2 ⟨subd9_1_4816, List.forall_mem_cons.2 ⟨subd9_1_4817, List.forall_mem_cons.2 ⟨subd9_1_4818, List.forall_mem_cons.2 ⟨subd9_1_4819, List.forall_mem_cons.2 ⟨subd9_1_4820, List.forall_mem_cons.2 ⟨subd9_1_4821, List.forall_mem_cons.2 ⟨subd9_1_4822, List.forall_mem_cons.2 ⟨subd9_1_4823, List.forall_mem_cons.2 ⟨subd9_1_4824, List.forall_mem_cons.2 ⟨subd9_1_4825, List.forall_mem_cons.2 ⟨subd9_1_4826, List.forall_mem_cons.2 ⟨subd9_1_4827, List.forall_mem_cons.2 ⟨subd9_1_4828, List.forall_mem_cons.2 ⟨subd9_1_4829, List.forall_mem_cons.2 ⟨subd9_1_4830, List.forall_mem_cons.2 ⟨subd9_1_4831, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
