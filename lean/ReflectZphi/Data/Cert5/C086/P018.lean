import ReflectZphi.Data.Cert5.C086.Base

namespace ReflectZphi.Data.Cert5.C086
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub6_1344 : sub6 [3, -5, -5] = true := by decide +kernel
theorem sub6_1345 : sub6 [3, -5, -4] = true := by decide +kernel
theorem sub6_1346 : sub6 [3, -5, -3] = true := by decide +kernel
theorem sub6_1347 : sub6 [3, -5, -2] = true := by decide +kernel
theorem sub6_1348 : sub6 [3, -5, -1] = true := by decide +kernel
theorem sub6_1349 : sub6 [3, -5, 0] = true := by decide +kernel
theorem sub6_1350 : sub6 [3, -5, 1] = true := by decide +kernel
theorem sub6_1351 : sub6 [3, -5, 2] = true := by decide +kernel
theorem sub6_1352 : sub6 [3, -5, 3] = true := by decide +kernel
theorem sub6_1353 : sub6 [3, -5, 4] = true := by decide +kernel
theorem sub6_1354 : sub6 [3, -5, 5] = true := by decide +kernel
theorem sub6_1355 : sub6 [3, -5, 6] = true := by decide +kernel
theorem sub6_1356 : sub6 [3, -5, 7] = true := by decide +kernel
theorem sub6_1357 : sub6 [3, -5, 8] = true := by decide +kernel
theorem sub6_1358 : sub6 [3, -4, -8] = true := by decide +kernel
theorem sub6_1359 : sub6 [3, -4, -7] = true := by decide +kernel
theorem sub6_1360 : sub6 [3, -4, -6] = true := by decide +kernel
theorem sub6_1361 : sub6 [3, -4, -5] = true := by decide +kernel
theorem sub6_1362 : sub6 [3, -4, -4] = true := by decide +kernel
theorem sub6_1363 : sub6 [3, -4, -3] = true := by decide +kernel
theorem sub6_1364 : sub6 [3, -4, -2] = true := by decide +kernel
theorem sub6_1365 : sub6 [3, -4, -1] = true := by decide +kernel
theorem sub6_1366 : sub6 [3, -4, 0] = true := by decide +kernel
theorem sub6_1367 : sub6 [3, -4, 1] = true := by decide +kernel
theorem sub6_1368 : sub6 [3, -4, 2] = true := by decide +kernel
theorem sub6_1369 : sub6 [3, -4, 3] = true := by decide +kernel
theorem sub6_1370 : sub6 [3, -4, 4] = true := by decide +kernel
theorem sub6_1371 : sub6 [3, -4, 5] = true := by decide +kernel
theorem sub6_1372 : sub6 [3, -4, 6] = true := by decide +kernel
theorem sub6_1373 : sub6 [3, -4, 7] = true := by decide +kernel
theorem sub6_1374 : sub6 [3, -4, 8] = true := by decide +kernel
theorem sub6_1375 : sub6 [3, -3, -8] = true := by decide +kernel
theorem sb6_42 : ∀ q ∈ blk6_42, sub6 q = true := by
  unfold blk6_42
  exact List.forall_mem_cons.2 ⟨sub6_1344, List.forall_mem_cons.2 ⟨sub6_1345, List.forall_mem_cons.2 ⟨sub6_1346, List.forall_mem_cons.2 ⟨sub6_1347, List.forall_mem_cons.2 ⟨sub6_1348, List.forall_mem_cons.2 ⟨sub6_1349, List.forall_mem_cons.2 ⟨sub6_1350, List.forall_mem_cons.2 ⟨sub6_1351, List.forall_mem_cons.2 ⟨sub6_1352, List.forall_mem_cons.2 ⟨sub6_1353, List.forall_mem_cons.2 ⟨sub6_1354, List.forall_mem_cons.2 ⟨sub6_1355, List.forall_mem_cons.2 ⟨sub6_1356, List.forall_mem_cons.2 ⟨sub6_1357, List.forall_mem_cons.2 ⟨sub6_1358, List.forall_mem_cons.2 ⟨sub6_1359, List.forall_mem_cons.2 ⟨sub6_1360, List.forall_mem_cons.2 ⟨sub6_1361, List.forall_mem_cons.2 ⟨sub6_1362, List.forall_mem_cons.2 ⟨sub6_1363, List.forall_mem_cons.2 ⟨sub6_1364, List.forall_mem_cons.2 ⟨sub6_1365, List.forall_mem_cons.2 ⟨sub6_1366, List.forall_mem_cons.2 ⟨sub6_1367, List.forall_mem_cons.2 ⟨sub6_1368, List.forall_mem_cons.2 ⟨sub6_1369, List.forall_mem_cons.2 ⟨sub6_1370, List.forall_mem_cons.2 ⟨sub6_1371, List.forall_mem_cons.2 ⟨sub6_1372, List.forall_mem_cons.2 ⟨sub6_1373, List.forall_mem_cons.2 ⟨sub6_1374, List.forall_mem_cons.2 ⟨sub6_1375, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1376 : sub6 [3, -3, -7] = true := by decide +kernel
theorem sub6_1377 : sub6 [3, -3, -6] = true := by decide +kernel
theorem sub6_1378 : sub6 [3, -3, -5] = true := by decide +kernel
theorem sub6_1379 : sub6 [3, -3, -4] = true := by decide +kernel
theorem sub6_1380 : sub6 [3, -3, -3] = true := by decide +kernel
theorem sub6_1381 : sub6 [3, -3, -2] = true := by decide +kernel
theorem sub6_1382 : sub6 [3, -3, -1] = true := by decide +kernel
theorem sub6_1383 : sub6 [3, -3, 0] = true := by decide +kernel
theorem sub6_1384 : sub6 [3, -3, 1] = true := by decide +kernel
theorem sub6_1385 : sub6 [3, -3, 2] = true := by decide +kernel
theorem sub6_1386 : sub6 [3, -3, 3] = true := by decide +kernel
theorem sub6_1387 : sub6 [3, -3, 4] = true := by decide +kernel
theorem sub6_1388 : sub6 [3, -3, 5] = true := by decide +kernel
theorem sub6_1389 : sub6 [3, -3, 6] = true := by decide +kernel
theorem sub6_1390 : sub6 [3, -3, 7] = true := by decide +kernel
theorem sub6_1391 : sub6 [3, -3, 8] = true := by decide +kernel
theorem sub6_1392 : sub6 [3, -2, -9] = true := by decide +kernel
theorem sub6_1393 : sub6 [3, -2, -8] = true := by decide +kernel
theorem sub6_1394 : sub6 [3, -2, -7] = true := by decide +kernel
theorem sub6_1395 : sub6 [3, -2, -6] = true := by decide +kernel
theorem sub6_1396 : sub6 [3, -2, -5] = true := by decide +kernel
theorem sub6_1397 : sub6 [3, -2, -4] = true := by decide +kernel
theorem sub6_1398 : sub6 [3, -2, -3] = true := by decide +kernel
theorem sub6_1399 : sub6 [3, -2, -2] = true := by decide +kernel
theorem sub6_1400 : sub6 [3, -2, -1] = true := by decide +kernel
theorem sub6_1401 : sub6 [3, -2, 0] = true := by decide +kernel
theorem sub6_1402 : sub6 [3, -2, 1] = true := by decide +kernel
theorem sub6_1403 : sub6 [3, -2, 2] = true := by decide +kernel
theorem sub6_1404 : sub6 [3, -2, 3] = true := by decide +kernel
theorem sub6_1405 : sub6 [3, -2, 4] = true := by decide +kernel
theorem sub6_1406 : sub6 [3, -2, 5] = true := by decide +kernel
theorem sub6_1407 : sub6 [3, -2, 6] = true := by decide +kernel
theorem sb6_43 : ∀ q ∈ blk6_43, sub6 q = true := by
  unfold blk6_43
  exact List.forall_mem_cons.2 ⟨sub6_1376, List.forall_mem_cons.2 ⟨sub6_1377, List.forall_mem_cons.2 ⟨sub6_1378, List.forall_mem_cons.2 ⟨sub6_1379, List.forall_mem_cons.2 ⟨sub6_1380, List.forall_mem_cons.2 ⟨sub6_1381, List.forall_mem_cons.2 ⟨sub6_1382, List.forall_mem_cons.2 ⟨sub6_1383, List.forall_mem_cons.2 ⟨sub6_1384, List.forall_mem_cons.2 ⟨sub6_1385, List.forall_mem_cons.2 ⟨sub6_1386, List.forall_mem_cons.2 ⟨sub6_1387, List.forall_mem_cons.2 ⟨sub6_1388, List.forall_mem_cons.2 ⟨sub6_1389, List.forall_mem_cons.2 ⟨sub6_1390, List.forall_mem_cons.2 ⟨sub6_1391, List.forall_mem_cons.2 ⟨sub6_1392, List.forall_mem_cons.2 ⟨sub6_1393, List.forall_mem_cons.2 ⟨sub6_1394, List.forall_mem_cons.2 ⟨sub6_1395, List.forall_mem_cons.2 ⟨sub6_1396, List.forall_mem_cons.2 ⟨sub6_1397, List.forall_mem_cons.2 ⟨sub6_1398, List.forall_mem_cons.2 ⟨sub6_1399, List.forall_mem_cons.2 ⟨sub6_1400, List.forall_mem_cons.2 ⟨sub6_1401, List.forall_mem_cons.2 ⟨sub6_1402, List.forall_mem_cons.2 ⟨sub6_1403, List.forall_mem_cons.2 ⟨sub6_1404, List.forall_mem_cons.2 ⟨sub6_1405, List.forall_mem_cons.2 ⟨sub6_1406, List.forall_mem_cons.2 ⟨sub6_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1408 : sub6 [3, -2, 7] = true := by decide +kernel
theorem sub6_1409 : sub6 [3, -2, 8] = true := by decide +kernel
theorem sub6_1410 : sub6 [3, -1, -10] = true := by decide +kernel
theorem sub6_1411 : sub6 [3, -1, -9] = true := by decide +kernel
theorem sub6_1412 : sub6 [3, -1, -8] = true := by decide +kernel
theorem sub6_1413 : sub6 [3, -1, -7] = true := by decide +kernel
theorem sub6_1414 : sub6 [3, -1, -6] = true := by decide +kernel
theorem sub6_1415 : sub6 [3, -1, -5] = true := by decide +kernel
theorem sub6_1416 : sub6 [3, -1, -4] = true := by decide +kernel
theorem sub6_1417 : sub6 [3, -1, -3] = true := by decide +kernel
theorem sub6_1418 : sub6 [3, -1, -2] = true := by decide +kernel
theorem sub6_1419 : sub6 [3, -1, -1] = true := by decide +kernel
theorem sub6_1420 : sub6 [3, -1, 0] = true := by decide +kernel
theorem sub6_1421 : sub6 [3, -1, 1] = true := by decide +kernel
theorem sub6_1422 : sub6 [3, -1, 2] = true := by decide +kernel
theorem sub6_1423 : sub6 [3, -1, 3] = true := by decide +kernel
theorem sub6_1424 : sub6 [3, -1, 4] = true := by decide +kernel
theorem sub6_1425 : sub6 [3, -1, 5] = true := by decide +kernel
theorem sub6_1426 : sub6 [3, -1, 6] = true := by decide +kernel
theorem sub6_1427 : sub6 [3, -1, 7] = true := by decide +kernel
theorem sub6_1428 : sub6 [3, 0, -10] = true := by decide +kernel
theorem sub6_1429 : sub6 [3, 0, -9] = true := by decide +kernel
theorem sub6_1430 : sub6 [3, 0, -8] = true := by decide +kernel
theorem sub6_1431 : sub6 [3, 0, -7] = true := by decide +kernel
theorem sub6_1432 : sub6 [3, 0, -6] = true := by decide +kernel
theorem sub6_1433 : sub6 [3, 0, -5] = true := by decide +kernel
theorem sub6_1434 : sub6 [3, 0, -4] = true := by decide +kernel
theorem sub6_1435 : sub6 [3, 0, -3] = true := by decide +kernel
theorem sub6_1436 : sub6 [3, 0, -2] = true := by decide +kernel
theorem sub6_1437 : sub6 [3, 0, -1] = true := by decide +kernel
theorem sub6_1438 : sub6 [3, 0, 0] = true := by decide +kernel
theorem sub6_1439 : sub6 [3, 0, 1] = true := by decide +kernel
theorem sb6_44 : ∀ q ∈ blk6_44, sub6 q = true := by
  unfold blk6_44
  exact List.forall_mem_cons.2 ⟨sub6_1408, List.forall_mem_cons.2 ⟨sub6_1409, List.forall_mem_cons.2 ⟨sub6_1410, List.forall_mem_cons.2 ⟨sub6_1411, List.forall_mem_cons.2 ⟨sub6_1412, List.forall_mem_cons.2 ⟨sub6_1413, List.forall_mem_cons.2 ⟨sub6_1414, List.forall_mem_cons.2 ⟨sub6_1415, List.forall_mem_cons.2 ⟨sub6_1416, List.forall_mem_cons.2 ⟨sub6_1417, List.forall_mem_cons.2 ⟨sub6_1418, List.forall_mem_cons.2 ⟨sub6_1419, List.forall_mem_cons.2 ⟨sub6_1420, List.forall_mem_cons.2 ⟨sub6_1421, List.forall_mem_cons.2 ⟨sub6_1422, List.forall_mem_cons.2 ⟨sub6_1423, List.forall_mem_cons.2 ⟨sub6_1424, List.forall_mem_cons.2 ⟨sub6_1425, List.forall_mem_cons.2 ⟨sub6_1426, List.forall_mem_cons.2 ⟨sub6_1427, List.forall_mem_cons.2 ⟨sub6_1428, List.forall_mem_cons.2 ⟨sub6_1429, List.forall_mem_cons.2 ⟨sub6_1430, List.forall_mem_cons.2 ⟨sub6_1431, List.forall_mem_cons.2 ⟨sub6_1432, List.forall_mem_cons.2 ⟨sub6_1433, List.forall_mem_cons.2 ⟨sub6_1434, List.forall_mem_cons.2 ⟨sub6_1435, List.forall_mem_cons.2 ⟨sub6_1436, List.forall_mem_cons.2 ⟨sub6_1437, List.forall_mem_cons.2 ⟨sub6_1438, List.forall_mem_cons.2 ⟨sub6_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1440 : sub6 [3, 0, 2] = true := by decide +kernel
theorem sub6_1441 : sub6 [3, 0, 3] = true := by decide +kernel
theorem sub6_1442 : sub6 [3, 0, 4] = true := by decide +kernel
theorem sub6_1443 : sub6 [3, 0, 5] = true := by decide +kernel
theorem sub6_1444 : sub6 [3, 0, 6] = true := by decide +kernel
theorem sub6_1445 : sub6 [3, 0, 7] = true := by decide +kernel
theorem sub6_1446 : sub6 [3, 1, -10] = true := by decide +kernel
theorem sub6_1447 : sub6 [3, 1, -9] = true := by decide +kernel
theorem sub6_1448 : sub6 [3, 1, -8] = true := by decide +kernel
theorem sub6_1449 : sub6 [3, 1, -7] = true := by decide +kernel
theorem sub6_1450 : sub6 [3, 1, -6] = true := by decide +kernel
theorem sub6_1451 : sub6 [3, 1, -5] = true := by decide +kernel
theorem sub6_1452 : sub6 [3, 1, -4] = true := by decide +kernel
theorem sub6_1453 : sub6 [3, 1, -3] = true := by decide +kernel
theorem sub6_1454 : sub6 [3, 1, -2] = true := by decide +kernel
theorem sub6_1455 : sub6 [3, 1, -1] = true := by decide +kernel
theorem sub6_1456 : sub6 [3, 1, 0] = true := by decide +kernel
theorem sub6_1457 : sub6 [3, 1, 1] = true := by decide +kernel
theorem sub6_1458 : sub6 [3, 1, 2] = true := by decide +kernel
theorem sub6_1459 : sub6 [3, 1, 3] = true := by decide +kernel
theorem sub6_1460 : sub6 [3, 1, 4] = true := by decide +kernel
theorem sub6_1461 : sub6 [3, 1, 5] = true := by decide +kernel
theorem sub6_1462 : sub6 [3, 1, 6] = true := by decide +kernel
theorem sub6_1463 : sub6 [3, 2, -10] = true := by decide +kernel
theorem sub6_1464 : sub6 [3, 2, -9] = true := by decide +kernel
theorem sub6_1465 : sub6 [3, 2, -8] = true := by decide +kernel
theorem sub6_1466 : sub6 [3, 2, -7] = true := by decide +kernel
theorem sub6_1467 : sub6 [3, 2, -6] = true := by decide +kernel
theorem sub6_1468 : sub6 [3, 2, -5] = true := by decide +kernel
theorem sub6_1469 : sub6 [3, 2, -4] = true := by decide +kernel
theorem sub6_1470 : sub6 [3, 2, -3] = true := by decide +kernel
theorem sub6_1471 : sub6 [3, 2, -2] = true := by decide +kernel
theorem sb6_45 : ∀ q ∈ blk6_45, sub6 q = true := by
  unfold blk6_45
  exact List.forall_mem_cons.2 ⟨sub6_1440, List.forall_mem_cons.2 ⟨sub6_1441, List.forall_mem_cons.2 ⟨sub6_1442, List.forall_mem_cons.2 ⟨sub6_1443, List.forall_mem_cons.2 ⟨sub6_1444, List.forall_mem_cons.2 ⟨sub6_1445, List.forall_mem_cons.2 ⟨sub6_1446, List.forall_mem_cons.2 ⟨sub6_1447, List.forall_mem_cons.2 ⟨sub6_1448, List.forall_mem_cons.2 ⟨sub6_1449, List.forall_mem_cons.2 ⟨sub6_1450, List.forall_mem_cons.2 ⟨sub6_1451, List.forall_mem_cons.2 ⟨sub6_1452, List.forall_mem_cons.2 ⟨sub6_1453, List.forall_mem_cons.2 ⟨sub6_1454, List.forall_mem_cons.2 ⟨sub6_1455, List.forall_mem_cons.2 ⟨sub6_1456, List.forall_mem_cons.2 ⟨sub6_1457, List.forall_mem_cons.2 ⟨sub6_1458, List.forall_mem_cons.2 ⟨sub6_1459, List.forall_mem_cons.2 ⟨sub6_1460, List.forall_mem_cons.2 ⟨sub6_1461, List.forall_mem_cons.2 ⟨sub6_1462, List.forall_mem_cons.2 ⟨sub6_1463, List.forall_mem_cons.2 ⟨sub6_1464, List.forall_mem_cons.2 ⟨sub6_1465, List.forall_mem_cons.2 ⟨sub6_1466, List.forall_mem_cons.2 ⟨sub6_1467, List.forall_mem_cons.2 ⟨sub6_1468, List.forall_mem_cons.2 ⟨sub6_1469, List.forall_mem_cons.2 ⟨sub6_1470, List.forall_mem_cons.2 ⟨sub6_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1472 : sub6 [3, 2, -1] = true := by decide +kernel
theorem sub6_1473 : sub6 [3, 2, 0] = true := by decide +kernel
theorem sub6_1474 : sub6 [3, 2, 1] = true := by decide +kernel
theorem sub6_1475 : sub6 [3, 2, 2] = true := by decide +kernel
theorem sub6_1476 : sub6 [3, 2, 3] = true := by decide +kernel
theorem sub6_1477 : sub6 [3, 2, 4] = true := by decide +kernel
theorem sub6_1478 : sub6 [3, 2, 5] = true := by decide +kernel
theorem sub6_1479 : sub6 [3, 3, -10] = true := by decide +kernel
theorem sub6_1480 : sub6 [3, 3, -9] = true := by decide +kernel
theorem sub6_1481 : sub6 [3, 3, -8] = true := by decide +kernel
theorem sub6_1482 : sub6 [3, 3, -7] = true := by decide +kernel
theorem sub6_1483 : sub6 [3, 3, -6] = true := by decide +kernel
theorem sub6_1484 : sub6 [3, 3, -5] = true := by decide +kernel
theorem sub6_1485 : sub6 [3, 3, -4] = true := by decide +kernel
theorem sub6_1486 : sub6 [3, 3, -3] = true := by decide +kernel
theorem sub6_1487 : sub6 [3, 3, -2] = true := by decide +kernel
theorem sub6_1488 : sub6 [3, 3, -1] = true := by decide +kernel
theorem sub6_1489 : sub6 [3, 3, 0] = true := by decide +kernel
theorem sub6_1490 : sub6 [3, 3, 1] = true := by decide +kernel
theorem sub6_1491 : sub6 [3, 3, 2] = true := by decide +kernel
theorem sub6_1492 : sub6 [3, 3, 3] = true := by decide +kernel
theorem sub6_1493 : sub6 [3, 3, 4] = true := by decide +kernel
theorem sub6_1494 : sub6 [3, 4] = true := by decide +kernel
theorem sub6_1495 : sub6 [3, 5] = true := by decide +kernel
theorem sub6_1496 : sub6 [4, -8] = true := by decide +kernel
theorem sub6_1497 : sub6 [4, -7] = true := by decide +kernel
theorem sub6_1498 : sub6 [4, -6] = true := by decide +kernel
theorem sub6_1499 : sub6 [4, -5] = true := by decide +kernel
theorem sub6_1500 : sub6 [4, -4, -7] = true := by decide +kernel
theorem sub6_1501 : sub6 [4, -4, -6] = true := by decide +kernel
theorem sub6_1502 : sub6 [4, -4, -5] = true := by decide +kernel
theorem sub6_1503 : sub6 [4, -4, -4] = true := by decide +kernel
theorem sb6_46 : ∀ q ∈ blk6_46, sub6 q = true := by
  unfold blk6_46
  exact List.forall_mem_cons.2 ⟨sub6_1472, List.forall_mem_cons.2 ⟨sub6_1473, List.forall_mem_cons.2 ⟨sub6_1474, List.forall_mem_cons.2 ⟨sub6_1475, List.forall_mem_cons.2 ⟨sub6_1476, List.forall_mem_cons.2 ⟨sub6_1477, List.forall_mem_cons.2 ⟨sub6_1478, List.forall_mem_cons.2 ⟨sub6_1479, List.forall_mem_cons.2 ⟨sub6_1480, List.forall_mem_cons.2 ⟨sub6_1481, List.forall_mem_cons.2 ⟨sub6_1482, List.forall_mem_cons.2 ⟨sub6_1483, List.forall_mem_cons.2 ⟨sub6_1484, List.forall_mem_cons.2 ⟨sub6_1485, List.forall_mem_cons.2 ⟨sub6_1486, List.forall_mem_cons.2 ⟨sub6_1487, List.forall_mem_cons.2 ⟨sub6_1488, List.forall_mem_cons.2 ⟨sub6_1489, List.forall_mem_cons.2 ⟨sub6_1490, List.forall_mem_cons.2 ⟨sub6_1491, List.forall_mem_cons.2 ⟨sub6_1492, List.forall_mem_cons.2 ⟨sub6_1493, List.forall_mem_cons.2 ⟨sub6_1494, List.forall_mem_cons.2 ⟨sub6_1495, List.forall_mem_cons.2 ⟨sub6_1496, List.forall_mem_cons.2 ⟨sub6_1497, List.forall_mem_cons.2 ⟨sub6_1498, List.forall_mem_cons.2 ⟨sub6_1499, List.forall_mem_cons.2 ⟨sub6_1500, List.forall_mem_cons.2 ⟨sub6_1501, List.forall_mem_cons.2 ⟨sub6_1502, List.forall_mem_cons.2 ⟨sub6_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1504 : sub6 [4, -4, -3] = true := by decide +kernel
theorem sub6_1505 : sub6 [4, -4, -2] = true := by decide +kernel
theorem sub6_1506 : sub6 [4, -4, -1] = true := by decide +kernel
theorem sub6_1507 : sub6 [4, -4, 0] = true := by decide +kernel
theorem sub6_1508 : sub6 [4, -4, 1] = true := by decide +kernel
theorem sub6_1509 : sub6 [4, -4, 2] = true := by decide +kernel
theorem sub6_1510 : sub6 [4, -4, 3] = true := by decide +kernel
theorem sub6_1511 : sub6 [4, -4, 4] = true := by decide +kernel
theorem sub6_1512 : sub6 [4, -4, 5] = true := by decide +kernel
theorem sub6_1513 : sub6 [4, -4, 6] = true := by decide +kernel
theorem sub6_1514 : sub6 [4, -4, 7] = true := by decide +kernel
theorem sub6_1515 : sub6 [4, -3, -8] = true := by decide +kernel
theorem sub6_1516 : sub6 [4, -3, -7] = true := by decide +kernel
theorem sub6_1517 : sub6 [4, -3, -6] = true := by decide +kernel
theorem sub6_1518 : sub6 [4, -3, -5] = true := by decide +kernel
theorem sub6_1519 : sub6 [4, -3, -4] = true := by decide +kernel
theorem sub6_1520 : sub6 [4, -3, -3] = true := by decide +kernel
theorem sub6_1521 : sub6 [4, -3, -2] = true := by decide +kernel
theorem sub6_1522 : sub6 [4, -3, -1] = true := by decide +kernel
theorem sub6_1523 : sub6 [4, -3, 0] = true := by decide +kernel
theorem sub6_1524 : sub6 [4, -3, 1] = true := by decide +kernel
theorem sub6_1525 : sub6 [4, -3, 2] = true := by decide +kernel
theorem sub6_1526 : sub6 [4, -3, 3] = true := by decide +kernel
theorem sub6_1527 : sub6 [4, -3, 4] = true := by decide +kernel
theorem sub6_1528 : sub6 [4, -3, 5] = true := by decide +kernel
theorem sub6_1529 : sub6 [4, -3, 6] = true := by decide +kernel
theorem sub6_1530 : sub6 [4, -3, 7] = true := by decide +kernel
theorem sub6_1531 : sub6 [4, -2, -9] = true := by decide +kernel
theorem sub6_1532 : sub6 [4, -2, -8] = true := by decide +kernel
theorem sub6_1533 : sub6 [4, -2, -7] = true := by decide +kernel
theorem sub6_1534 : sub6 [4, -2, -6] = true := by decide +kernel
theorem sub6_1535 : sub6 [4, -2, -5] = true := by decide +kernel
theorem sb6_47 : ∀ q ∈ blk6_47, sub6 q = true := by
  unfold blk6_47
  exact List.forall_mem_cons.2 ⟨sub6_1504, List.forall_mem_cons.2 ⟨sub6_1505, List.forall_mem_cons.2 ⟨sub6_1506, List.forall_mem_cons.2 ⟨sub6_1507, List.forall_mem_cons.2 ⟨sub6_1508, List.forall_mem_cons.2 ⟨sub6_1509, List.forall_mem_cons.2 ⟨sub6_1510, List.forall_mem_cons.2 ⟨sub6_1511, List.forall_mem_cons.2 ⟨sub6_1512, List.forall_mem_cons.2 ⟨sub6_1513, List.forall_mem_cons.2 ⟨sub6_1514, List.forall_mem_cons.2 ⟨sub6_1515, List.forall_mem_cons.2 ⟨sub6_1516, List.forall_mem_cons.2 ⟨sub6_1517, List.forall_mem_cons.2 ⟨sub6_1518, List.forall_mem_cons.2 ⟨sub6_1519, List.forall_mem_cons.2 ⟨sub6_1520, List.forall_mem_cons.2 ⟨sub6_1521, List.forall_mem_cons.2 ⟨sub6_1522, List.forall_mem_cons.2 ⟨sub6_1523, List.forall_mem_cons.2 ⟨sub6_1524, List.forall_mem_cons.2 ⟨sub6_1525, List.forall_mem_cons.2 ⟨sub6_1526, List.forall_mem_cons.2 ⟨sub6_1527, List.forall_mem_cons.2 ⟨sub6_1528, List.forall_mem_cons.2 ⟨sub6_1529, List.forall_mem_cons.2 ⟨sub6_1530, List.forall_mem_cons.2 ⟨sub6_1531, List.forall_mem_cons.2 ⟨sub6_1532, List.forall_mem_cons.2 ⟨sub6_1533, List.forall_mem_cons.2 ⟨sub6_1534, List.forall_mem_cons.2 ⟨sub6_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1536 : sub6 [4, -2, -4] = true := by decide +kernel
theorem sub6_1537 : sub6 [4, -2, -3] = true := by decide +kernel
theorem sub6_1538 : sub6 [4, -2, -2] = true := by decide +kernel
theorem sub6_1539 : sub6 [4, -2, -1] = true := by decide +kernel
theorem sub6_1540 : sub6 [4, -2, 0] = true := by decide +kernel
theorem sub6_1541 : sub6 [4, -2, 1] = true := by decide +kernel
theorem sub6_1542 : sub6 [4, -2, 2] = true := by decide +kernel
theorem sub6_1543 : sub6 [4, -2, 3] = true := by decide +kernel
theorem sub6_1544 : sub6 [4, -2, 4] = true := by decide +kernel
theorem sub6_1545 : sub6 [4, -2, 5] = true := by decide +kernel
theorem sub6_1546 : sub6 [4, -2, 6] = true := by decide +kernel
theorem sub6_1547 : sub6 [4, -2, 7] = true := by decide +kernel
theorem sub6_1548 : sub6 [4, -1, -9] = true := by decide +kernel
theorem sub6_1549 : sub6 [4, -1, -8] = true := by decide +kernel
theorem sub6_1550 : sub6 [4, -1, -7] = true := by decide +kernel
theorem sub6_1551 : sub6 [4, -1, -6] = true := by decide +kernel
theorem sub6_1552 : sub6 [4, -1, -5] = true := by decide +kernel
theorem sub6_1553 : sub6 [4, -1, -4] = true := by decide +kernel
theorem sub6_1554 : sub6 [4, -1, -3] = true := by decide +kernel
theorem sub6_1555 : sub6 [4, -1, -2] = true := by decide +kernel
theorem sub6_1556 : sub6 [4, -1, -1] = true := by decide +kernel
theorem sub6_1557 : sub6 [4, -1, 0] = true := by decide +kernel
theorem sub6_1558 : sub6 [4, -1, 1] = true := by decide +kernel
theorem sub6_1559 : sub6 [4, -1, 2] = true := by decide +kernel
theorem sub6_1560 : sub6 [4, -1, 3] = true := by decide +kernel
theorem sub6_1561 : sub6 [4, -1, 4] = true := by decide +kernel
theorem sub6_1562 : sub6 [4, -1, 5] = true := by decide +kernel
theorem sub6_1563 : sub6 [4, -1, 6] = true := by decide +kernel
theorem sub6_1564 : sub6 [4, 0, -10] = true := by decide +kernel
theorem sub6_1565 : sub6 [4, 0, -9] = true := by decide +kernel
theorem sub6_1566 : sub6 [4, 0, -8] = true := by decide +kernel
theorem sub6_1567 : sub6 [4, 0, -7] = true := by decide +kernel
theorem sb6_48 : ∀ q ∈ blk6_48, sub6 q = true := by
  unfold blk6_48
  exact List.forall_mem_cons.2 ⟨sub6_1536, List.forall_mem_cons.2 ⟨sub6_1537, List.forall_mem_cons.2 ⟨sub6_1538, List.forall_mem_cons.2 ⟨sub6_1539, List.forall_mem_cons.2 ⟨sub6_1540, List.forall_mem_cons.2 ⟨sub6_1541, List.forall_mem_cons.2 ⟨sub6_1542, List.forall_mem_cons.2 ⟨sub6_1543, List.forall_mem_cons.2 ⟨sub6_1544, List.forall_mem_cons.2 ⟨sub6_1545, List.forall_mem_cons.2 ⟨sub6_1546, List.forall_mem_cons.2 ⟨sub6_1547, List.forall_mem_cons.2 ⟨sub6_1548, List.forall_mem_cons.2 ⟨sub6_1549, List.forall_mem_cons.2 ⟨sub6_1550, List.forall_mem_cons.2 ⟨sub6_1551, List.forall_mem_cons.2 ⟨sub6_1552, List.forall_mem_cons.2 ⟨sub6_1553, List.forall_mem_cons.2 ⟨sub6_1554, List.forall_mem_cons.2 ⟨sub6_1555, List.forall_mem_cons.2 ⟨sub6_1556, List.forall_mem_cons.2 ⟨sub6_1557, List.forall_mem_cons.2 ⟨sub6_1558, List.forall_mem_cons.2 ⟨sub6_1559, List.forall_mem_cons.2 ⟨sub6_1560, List.forall_mem_cons.2 ⟨sub6_1561, List.forall_mem_cons.2 ⟨sub6_1562, List.forall_mem_cons.2 ⟨sub6_1563, List.forall_mem_cons.2 ⟨sub6_1564, List.forall_mem_cons.2 ⟨sub6_1565, List.forall_mem_cons.2 ⟨sub6_1566, List.forall_mem_cons.2 ⟨sub6_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1568 : sub6 [4, 0, -6] = true := by decide +kernel
theorem sub6_1569 : sub6 [4, 0, -5] = true := by decide +kernel
theorem sub6_1570 : sub6 [4, 0, -4] = true := by decide +kernel
theorem sub6_1571 : sub6 [4, 0, -3] = true := by decide +kernel
theorem sub6_1572 : sub6 [4, 0, -2] = true := by decide +kernel
theorem sub6_1573 : sub6 [4, 0, -1] = true := by decide +kernel
theorem sub6_1574 : sub6 [4, 0, 0] = true := by decide +kernel
theorem sub6_1575 : sub6 [4, 0, 1] = true := by decide +kernel
theorem sub6_1576 : sub6 [4, 0, 2] = true := by decide +kernel
theorem sub6_1577 : sub6 [4, 0, 3] = true := by decide +kernel
theorem sub6_1578 : sub6 [4, 0, 4] = true := by decide +kernel
theorem sub6_1579 : sub6 [4, 0, 5] = true := by decide +kernel
theorem sub6_1580 : sub6 [4, 1, -10] = true := by decide +kernel
theorem sub6_1581 : sub6 [4, 1, -9] = true := by decide +kernel
theorem sub6_1582 : sub6 [4, 1, -8] = true := by decide +kernel
theorem sub6_1583 : sub6 [4, 1, -7] = true := by decide +kernel
theorem sub6_1584 : sub6 [4, 1, -6] = true := by decide +kernel
theorem sub6_1585 : sub6 [4, 1, -5] = true := by decide +kernel
theorem sub6_1586 : sub6 [4, 1, -4] = true := by decide +kernel
theorem sub6_1587 : sub6 [4, 1, -3] = true := by decide +kernel
theorem sub6_1588 : sub6 [4, 1, -2] = true := by decide +kernel
theorem sub6_1589 : sub6 [4, 1, -1] = true := by decide +kernel
theorem sub6_1590 : sub6 [4, 1, 0] = true := by decide +kernel
theorem sub6_1591 : sub6 [4, 1, 1] = true := by decide +kernel
theorem sub6_1592 : sub6 [4, 1, 2] = true := by decide +kernel
theorem sub6_1593 : sub6 [4, 1, 3] = true := by decide +kernel
theorem sub6_1594 : sub6 [4, 1, 4] = true := by decide +kernel
theorem sub6_1595 : sub6 [4, 1, 5] = true := by decide +kernel
theorem sub6_1596 : sub6 [4, 2, -10] = true := by decide +kernel
theorem sub6_1597 : sub6 [4, 2, -9] = true := by decide +kernel
theorem sub6_1598 : sub6 [4, 2, -8] = true := by decide +kernel
theorem sub6_1599 : sub6 [4, 2, -7] = true := by decide +kernel
theorem sb6_49 : ∀ q ∈ blk6_49, sub6 q = true := by
  unfold blk6_49
  exact List.forall_mem_cons.2 ⟨sub6_1568, List.forall_mem_cons.2 ⟨sub6_1569, List.forall_mem_cons.2 ⟨sub6_1570, List.forall_mem_cons.2 ⟨sub6_1571, List.forall_mem_cons.2 ⟨sub6_1572, List.forall_mem_cons.2 ⟨sub6_1573, List.forall_mem_cons.2 ⟨sub6_1574, List.forall_mem_cons.2 ⟨sub6_1575, List.forall_mem_cons.2 ⟨sub6_1576, List.forall_mem_cons.2 ⟨sub6_1577, List.forall_mem_cons.2 ⟨sub6_1578, List.forall_mem_cons.2 ⟨sub6_1579, List.forall_mem_cons.2 ⟨sub6_1580, List.forall_mem_cons.2 ⟨sub6_1581, List.forall_mem_cons.2 ⟨sub6_1582, List.forall_mem_cons.2 ⟨sub6_1583, List.forall_mem_cons.2 ⟨sub6_1584, List.forall_mem_cons.2 ⟨sub6_1585, List.forall_mem_cons.2 ⟨sub6_1586, List.forall_mem_cons.2 ⟨sub6_1587, List.forall_mem_cons.2 ⟨sub6_1588, List.forall_mem_cons.2 ⟨sub6_1589, List.forall_mem_cons.2 ⟨sub6_1590, List.forall_mem_cons.2 ⟨sub6_1591, List.forall_mem_cons.2 ⟨sub6_1592, List.forall_mem_cons.2 ⟨sub6_1593, List.forall_mem_cons.2 ⟨sub6_1594, List.forall_mem_cons.2 ⟨sub6_1595, List.forall_mem_cons.2 ⟨sub6_1596, List.forall_mem_cons.2 ⟨sub6_1597, List.forall_mem_cons.2 ⟨sub6_1598, List.forall_mem_cons.2 ⟨sub6_1599, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1600 : sub6 [4, 2, -6] = true := by decide +kernel
theorem sub6_1601 : sub6 [4, 2, -5] = true := by decide +kernel
theorem sub6_1602 : sub6 [4, 2, -4] = true := by decide +kernel
theorem sub6_1603 : sub6 [4, 2, -3] = true := by decide +kernel
theorem sub6_1604 : sub6 [4, 2, -2] = true := by decide +kernel
theorem sub6_1605 : sub6 [4, 2, -1] = true := by decide +kernel
theorem sub6_1606 : sub6 [4, 2, 0] = true := by decide +kernel
theorem sub6_1607 : sub6 [4, 2, 1] = true := by decide +kernel
theorem sub6_1608 : sub6 [4, 2, 2] = true := by decide +kernel
theorem sub6_1609 : sub6 [4, 2, 3] = true := by decide +kernel
theorem sub6_1610 : sub6 [4, 2, 4] = true := by decide +kernel
theorem sub6_1611 : sub6 [4, 3] = true := by decide +kernel
theorem sub6_1612 : sub6 [4, 4] = true := by decide +kernel
theorem sub6_1613 : sub6 [5, -7] = true := by decide +kernel
theorem sub6_1614 : sub6 [5, -6] = true := by decide +kernel
theorem sub6_1615 : sub6 [5, -5] = true := by decide +kernel
theorem sub6_1616 : sub6 [5, -4] = true := by decide +kernel
theorem sub6_1617 : sub6 [5, -3, -7] = true := by decide +kernel
theorem sub6_1618 : sub6 [5, -3, -6] = true := by decide +kernel
theorem sub6_1619 : sub6 [5, -3, -5] = true := by decide +kernel
theorem sub6_1620 : sub6 [5, -3, -4] = true := by decide +kernel
theorem sub6_1621 : sub6 [5, -3, -3] = true := by decide +kernel
theorem sub6_1622 : sub6 [5, -3, -2] = true := by decide +kernel
theorem sub6_1623 : sub6 [5, -3, -1] = true := by decide +kernel
theorem sub6_1624 : sub6 [5, -3, 0] = true := by decide +kernel
theorem sub6_1625 : sub6 [5, -3, 1] = true := by decide +kernel
theorem sub6_1626 : sub6 [5, -3, 2] = true := by decide +kernel
theorem sub6_1627 : sub6 [5, -3, 3] = true := by decide +kernel
theorem sub6_1628 : sub6 [5, -3, 4] = true := by decide +kernel
theorem sub6_1629 : sub6 [5, -3, 5] = true := by decide +kernel
theorem sub6_1630 : sub6 [5, -2, -8] = true := by decide +kernel
theorem sub6_1631 : sub6 [5, -2, -7] = true := by decide +kernel
theorem sb6_50 : ∀ q ∈ blk6_50, sub6 q = true := by
  unfold blk6_50
  exact List.forall_mem_cons.2 ⟨sub6_1600, List.forall_mem_cons.2 ⟨sub6_1601, List.forall_mem_cons.2 ⟨sub6_1602, List.forall_mem_cons.2 ⟨sub6_1603, List.forall_mem_cons.2 ⟨sub6_1604, List.forall_mem_cons.2 ⟨sub6_1605, List.forall_mem_cons.2 ⟨sub6_1606, List.forall_mem_cons.2 ⟨sub6_1607, List.forall_mem_cons.2 ⟨sub6_1608, List.forall_mem_cons.2 ⟨sub6_1609, List.forall_mem_cons.2 ⟨sub6_1610, List.forall_mem_cons.2 ⟨sub6_1611, List.forall_mem_cons.2 ⟨sub6_1612, List.forall_mem_cons.2 ⟨sub6_1613, List.forall_mem_cons.2 ⟨sub6_1614, List.forall_mem_cons.2 ⟨sub6_1615, List.forall_mem_cons.2 ⟨sub6_1616, List.forall_mem_cons.2 ⟨sub6_1617, List.forall_mem_cons.2 ⟨sub6_1618, List.forall_mem_cons.2 ⟨sub6_1619, List.forall_mem_cons.2 ⟨sub6_1620, List.forall_mem_cons.2 ⟨sub6_1621, List.forall_mem_cons.2 ⟨sub6_1622, List.forall_mem_cons.2 ⟨sub6_1623, List.forall_mem_cons.2 ⟨sub6_1624, List.forall_mem_cons.2 ⟨sub6_1625, List.forall_mem_cons.2 ⟨sub6_1626, List.forall_mem_cons.2 ⟨sub6_1627, List.forall_mem_cons.2 ⟨sub6_1628, List.forall_mem_cons.2 ⟨sub6_1629, List.forall_mem_cons.2 ⟨sub6_1630, List.forall_mem_cons.2 ⟨sub6_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1632 : sub6 [5, -2, -6] = true := by decide +kernel
theorem sub6_1633 : sub6 [5, -2, -5] = true := by decide +kernel
theorem sub6_1634 : sub6 [5, -2, -4] = true := by decide +kernel
theorem sub6_1635 : sub6 [5, -2, -3] = true := by decide +kernel
theorem sub6_1636 : sub6 [5, -2, -2] = true := by decide +kernel
theorem sub6_1637 : sub6 [5, -2, -1] = true := by decide +kernel
theorem sub6_1638 : sub6 [5, -2, 0] = true := by decide +kernel
theorem sub6_1639 : sub6 [5, -2, 1] = true := by decide +kernel
theorem sub6_1640 : sub6 [5, -2, 2] = true := by decide +kernel
theorem sub6_1641 : sub6 [5, -2, 3] = true := by decide +kernel
theorem sub6_1642 : sub6 [5, -2, 4] = true := by decide +kernel
theorem sub6_1643 : sub6 [5, -2, 5] = true := by decide +kernel
theorem sub6_1644 : sub6 [5, -1, -9] = true := by decide +kernel
theorem sub6_1645 : sub6 [5, -1, -8] = true := by decide +kernel
theorem sub6_1646 : sub6 [5, -1, -7] = true := by decide +kernel
theorem sub6_1647 : sub6 [5, -1, -6] = true := by decide +kernel
theorem sub6_1648 : sub6 [5, -1, -5] = true := by decide +kernel
theorem sub6_1649 : sub6 [5, -1, -4] = true := by decide +kernel
theorem sub6_1650 : sub6 [5, -1, -3] = true := by decide +kernel
theorem sub6_1651 : sub6 [5, -1, -2] = true := by decide +kernel
theorem sub6_1652 : sub6 [5, -1, -1] = true := by decide +kernel
theorem sub6_1653 : sub6 [5, -1, 0] = true := by decide +kernel
theorem sub6_1654 : sub6 [5, -1, 1] = true := by decide +kernel
theorem sub6_1655 : sub6 [5, -1, 2] = true := by decide +kernel
theorem sub6_1656 : sub6 [5, -1, 3] = true := by decide +kernel
theorem sub6_1657 : sub6 [5, -1, 4] = true := by decide +kernel
theorem sub6_1658 : sub6 [5, 0, -9] = true := by decide +kernel
theorem sub6_1659 : sub6 [5, 0, -8] = true := by decide +kernel
theorem sub6_1660 : sub6 [5, 0, -7] = true := by decide +kernel
theorem sub6_1661 : sub6 [5, 0, -6] = true := by decide +kernel
theorem sub6_1662 : sub6 [5, 0, -5] = true := by decide +kernel
theorem sub6_1663 : sub6 [5, 0, -4] = true := by decide +kernel
theorem sb6_51 : ∀ q ∈ blk6_51, sub6 q = true := by
  unfold blk6_51
  exact List.forall_mem_cons.2 ⟨sub6_1632, List.forall_mem_cons.2 ⟨sub6_1633, List.forall_mem_cons.2 ⟨sub6_1634, List.forall_mem_cons.2 ⟨sub6_1635, List.forall_mem_cons.2 ⟨sub6_1636, List.forall_mem_cons.2 ⟨sub6_1637, List.forall_mem_cons.2 ⟨sub6_1638, List.forall_mem_cons.2 ⟨sub6_1639, List.forall_mem_cons.2 ⟨sub6_1640, List.forall_mem_cons.2 ⟨sub6_1641, List.forall_mem_cons.2 ⟨sub6_1642, List.forall_mem_cons.2 ⟨sub6_1643, List.forall_mem_cons.2 ⟨sub6_1644, List.forall_mem_cons.2 ⟨sub6_1645, List.forall_mem_cons.2 ⟨sub6_1646, List.forall_mem_cons.2 ⟨sub6_1647, List.forall_mem_cons.2 ⟨sub6_1648, List.forall_mem_cons.2 ⟨sub6_1649, List.forall_mem_cons.2 ⟨sub6_1650, List.forall_mem_cons.2 ⟨sub6_1651, List.forall_mem_cons.2 ⟨sub6_1652, List.forall_mem_cons.2 ⟨sub6_1653, List.forall_mem_cons.2 ⟨sub6_1654, List.forall_mem_cons.2 ⟨sub6_1655, List.forall_mem_cons.2 ⟨sub6_1656, List.forall_mem_cons.2 ⟨sub6_1657, List.forall_mem_cons.2 ⟨sub6_1658, List.forall_mem_cons.2 ⟨sub6_1659, List.forall_mem_cons.2 ⟨sub6_1660, List.forall_mem_cons.2 ⟨sub6_1661, List.forall_mem_cons.2 ⟨sub6_1662, List.forall_mem_cons.2 ⟨sub6_1663, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub6_1664 : sub6 [5, 0, -3] = true := by decide +kernel
theorem sub6_1665 : sub6 [5, 0, -2] = true := by decide +kernel
theorem sub6_1666 : sub6 [5, 0, -1] = true := by decide +kernel
theorem sub6_1667 : sub6 [5, 0, 0] = true := by decide +kernel
theorem sub6_1668 : sub6 [5, 0, 1] = true := by decide +kernel
theorem sub6_1669 : sub6 [5, 0, 2] = true := by decide +kernel
theorem sub6_1670 : sub6 [5, 0, 3] = true := by decide +kernel
theorem sub6_1671 : sub6 [5, 0, 4] = true := by decide +kernel
theorem sub6_1672 : sub6 [5, 1] = true := by decide +kernel
theorem sub6_1673 : sub6 [5, 2] = true := by decide +kernel
theorem sub6_1674 : sub6 [5, 3] = true := by decide +kernel
theorem sub6_1675 : sub6 [6, -6] = true := by decide +kernel
theorem sub6_1676 : sub6 [6, -5] = true := by decide +kernel
theorem sub6_1677 : sub6 [6, -4] = true := by decide +kernel
theorem sub6_1678 : sub6 [6, -3] = true := by decide +kernel
theorem sub6_1679 : sub6 [6, -2] = true := by decide +kernel
theorem sub6_1680 : sub6 [6, -1] = true := by decide +kernel
theorem sub6_1681 : sub6 [6, 0] = true := by decide +kernel
theorem sub6_1682 : sub6 [6, 1] = true := by decide +kernel
theorem sb6_52 : ∀ q ∈ blk6_52, sub6 q = true := by
  unfold blk6_52
  exact List.forall_mem_cons.2 ⟨sub6_1664, List.forall_mem_cons.2 ⟨sub6_1665, List.forall_mem_cons.2 ⟨sub6_1666, List.forall_mem_cons.2 ⟨sub6_1667, List.forall_mem_cons.2 ⟨sub6_1668, List.forall_mem_cons.2 ⟨sub6_1669, List.forall_mem_cons.2 ⟨sub6_1670, List.forall_mem_cons.2 ⟨sub6_1671, List.forall_mem_cons.2 ⟨sub6_1672, List.forall_mem_cons.2 ⟨sub6_1673, List.forall_mem_cons.2 ⟨sub6_1674, List.forall_mem_cons.2 ⟨sub6_1675, List.forall_mem_cons.2 ⟨sub6_1676, List.forall_mem_cons.2 ⟨sub6_1677, List.forall_mem_cons.2 ⟨sub6_1678, List.forall_mem_cons.2 ⟨sub6_1679, List.forall_mem_cons.2 ⟨sub6_1680, List.forall_mem_cons.2 ⟨sub6_1681, List.forall_mem_cons.2 ⟨sub6_1682, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub7_0 : sub7 [-6, -4] = true := by decide +kernel
theorem sub7_1 : sub7 [-6, -3] = true := by decide +kernel
theorem sub7_2 : sub7 [-6, -2] = true := by decide +kernel
theorem sub7_3 : sub7 [-6, -1] = true := by decide +kernel
theorem sub7_4 : sub7 [-6, 0] = true := by decide +kernel
theorem sub7_5 : sub7 [-6, 1] = true := by decide +kernel
theorem sub7_6 : sub7 [-6, 2] = true := by decide +kernel
theorem sub7_7 : sub7 [-5, -5] = true := by decide +kernel
theorem sub7_8 : sub7 [-5, -4] = true := by decide +kernel
theorem sub7_9 : sub7 [-5, -3] = true := by decide +kernel
theorem sub7_10 : sub7 [-5, -2] = true := by decide +kernel
theorem sub7_11 : sub7 [-5, -1] = true := by decide +kernel
theorem sub7_12 : sub7 [-5, 0] = true := by decide +kernel
theorem sub7_13 : sub7 [-5, 1] = true := by decide +kernel
theorem sub7_14 : sub7 [-5, 2] = true := by decide +kernel
theorem sub7_15 : sub7 [-5, 3] = true := by decide +kernel
theorem sub7_16 : sub7 [-5, 4] = true := by decide +kernel
theorem sub7_17 : sub7 [-4, -6] = true := by decide +kernel
theorem sub7_18 : sub7 [-4, -5] = true := by decide +kernel
theorem sub7_19 : sub7 [-4, -4] = true := by decide +kernel
theorem sub7_20 : sub7 [-4, -3] = true := by decide +kernel
theorem sub7_21 : sub7 [-4, -2] = true := by decide +kernel
theorem sub7_22 : sub7 [-4, -1, -7] = true := by decide +kernel
theorem sub7_23 : sub7 [-4, -1, -6] = true := by decide +kernel
theorem sub7_24 : sub7 [-4, -1, -5] = true := by decide +kernel
theorem sub7_25 : sub7 [-4, -1, -4] = true := by decide +kernel
theorem sub7_26 : sub7 [-4, -1, -3] = true := by decide +kernel
theorem sub7_27 : sub7 [-4, -1, -2] = true := by decide +kernel
theorem sub7_28 : sub7 [-4, -1, -1] = true := by decide +kernel
theorem sub7_29 : sub7 [-4, -1, 0] = true := by decide +kernel
theorem sub7_30 : sub7 [-4, -1, 1] = true := by decide +kernel
theorem sub7_31 : sub7 [-4, -1, 2] = true := by decide +kernel
theorem sb7_0 : ∀ q ∈ blk7_0, sub7 q = true := by
  unfold blk7_0
  exact List.forall_mem_cons.2 ⟨sub7_0, List.forall_mem_cons.2 ⟨sub7_1, List.forall_mem_cons.2 ⟨sub7_2, List.forall_mem_cons.2 ⟨sub7_3, List.forall_mem_cons.2 ⟨sub7_4, List.forall_mem_cons.2 ⟨sub7_5, List.forall_mem_cons.2 ⟨sub7_6, List.forall_mem_cons.2 ⟨sub7_7, List.forall_mem_cons.2 ⟨sub7_8, List.forall_mem_cons.2 ⟨sub7_9, List.forall_mem_cons.2 ⟨sub7_10, List.forall_mem_cons.2 ⟨sub7_11, List.forall_mem_cons.2 ⟨sub7_12, List.forall_mem_cons.2 ⟨sub7_13, List.forall_mem_cons.2 ⟨sub7_14, List.forall_mem_cons.2 ⟨sub7_15, List.forall_mem_cons.2 ⟨sub7_16, List.forall_mem_cons.2 ⟨sub7_17, List.forall_mem_cons.2 ⟨sub7_18, List.forall_mem_cons.2 ⟨sub7_19, List.forall_mem_cons.2 ⟨sub7_20, List.forall_mem_cons.2 ⟨sub7_21, List.forall_mem_cons.2 ⟨sub7_22, List.forall_mem_cons.2 ⟨sub7_23, List.forall_mem_cons.2 ⟨sub7_24, List.forall_mem_cons.2 ⟨sub7_25, List.forall_mem_cons.2 ⟨sub7_26, List.forall_mem_cons.2 ⟨sub7_27, List.forall_mem_cons.2 ⟨sub7_28, List.forall_mem_cons.2 ⟨sub7_29, List.forall_mem_cons.2 ⟨sub7_30, List.forall_mem_cons.2 ⟨sub7_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C086
