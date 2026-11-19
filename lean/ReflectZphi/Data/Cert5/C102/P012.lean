import ReflectZphi.Data.Cert5.C102.Base

namespace ReflectZphi.Data.Cert5.C102
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub8_1376 : sub8 [3, 1, -4] = true := by decide +kernel
theorem sub8_1377 : sub8 [3, 1, -3] = true := by decide +kernel
theorem sub8_1378 : sub8 [3, 1, -2] = true := by decide +kernel
theorem sub8_1379 : sub8 [3, 1, -1] = true := by decide +kernel
theorem sub8_1380 : sub8 [3, 1, 0] = true := by decide +kernel
theorem sub8_1381 : sub8 [3, 1, 1] = true := by decide +kernel
theorem sub8_1382 : sub8 [3, 1, 2] = true := by decide +kernel
theorem sub8_1383 : sub8 [3, 1, 3] = true := by decide +kernel
theorem sub8_1384 : sub8 [3, 1, 4] = true := by decide +kernel
theorem sub8_1385 : sub8 [3, 1, 5] = true := by decide +kernel
theorem sub8_1386 : sub8 [3, 1, 6] = true := by decide +kernel
theorem sub8_1387 : sub8 [3, 1, 7] = true := by decide +kernel
theorem sub8_1388 : sub8 [3, 2, -8] = true := by decide +kernel
theorem sub8_1389 : sub8 [3, 2, -7] = true := by decide +kernel
theorem sub8_1390 : sub8 [3, 2, -6] = true := by decide +kernel
theorem sub8_1391 : sub8 [3, 2, -5] = true := by decide +kernel
theorem sub8_1392 : sub8 [3, 2, -4] = true := by decide +kernel
theorem sub8_1393 : sub8 [3, 2, -3] = true := by decide +kernel
theorem sub8_1394 : sub8 [3, 2, -2] = true := by decide +kernel
theorem sub8_1395 : sub8 [3, 2, -1] = true := by decide +kernel
theorem sub8_1396 : sub8 [3, 2, 0] = true := by decide +kernel
theorem sub8_1397 : sub8 [3, 2, 1] = true := by decide +kernel
theorem sub8_1398 : sub8 [3, 2, 2] = true := by decide +kernel
theorem sub8_1399 : sub8 [3, 2, 3] = true := by decide +kernel
theorem sub8_1400 : sub8 [3, 2, 4] = true := by decide +kernel
theorem sub8_1401 : sub8 [3, 2, 5] = true := by decide +kernel
theorem sub8_1402 : sub8 [3, 2, 6] = true := by decide +kernel
theorem sub8_1403 : sub8 [3, 3, -7] = true := by decide +kernel
theorem sub8_1404 : sub8 [3, 3, -6] = true := by decide +kernel
theorem sub8_1405 : sub8 [3, 3, -5] = true := by decide +kernel
theorem sub8_1406 : sub8 [3, 3, -4] = true := by decide +kernel
theorem sub8_1407 : sub8 [3, 3, -3] = true := by decide +kernel
theorem sb8_43 : ∀ q ∈ blk8_43, sub8 q = true := by
  unfold blk8_43
  exact List.forall_mem_cons.2 ⟨sub8_1376, List.forall_mem_cons.2 ⟨sub8_1377, List.forall_mem_cons.2 ⟨sub8_1378, List.forall_mem_cons.2 ⟨sub8_1379, List.forall_mem_cons.2 ⟨sub8_1380, List.forall_mem_cons.2 ⟨sub8_1381, List.forall_mem_cons.2 ⟨sub8_1382, List.forall_mem_cons.2 ⟨sub8_1383, List.forall_mem_cons.2 ⟨sub8_1384, List.forall_mem_cons.2 ⟨sub8_1385, List.forall_mem_cons.2 ⟨sub8_1386, List.forall_mem_cons.2 ⟨sub8_1387, List.forall_mem_cons.2 ⟨sub8_1388, List.forall_mem_cons.2 ⟨sub8_1389, List.forall_mem_cons.2 ⟨sub8_1390, List.forall_mem_cons.2 ⟨sub8_1391, List.forall_mem_cons.2 ⟨sub8_1392, List.forall_mem_cons.2 ⟨sub8_1393, List.forall_mem_cons.2 ⟨sub8_1394, List.forall_mem_cons.2 ⟨sub8_1395, List.forall_mem_cons.2 ⟨sub8_1396, List.forall_mem_cons.2 ⟨sub8_1397, List.forall_mem_cons.2 ⟨sub8_1398, List.forall_mem_cons.2 ⟨sub8_1399, List.forall_mem_cons.2 ⟨sub8_1400, List.forall_mem_cons.2 ⟨sub8_1401, List.forall_mem_cons.2 ⟨sub8_1402, List.forall_mem_cons.2 ⟨sub8_1403, List.forall_mem_cons.2 ⟨sub8_1404, List.forall_mem_cons.2 ⟨sub8_1405, List.forall_mem_cons.2 ⟨sub8_1406, List.forall_mem_cons.2 ⟨sub8_1407, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1408 : sub8 [3, 3, -2] = true := by decide +kernel
theorem sub8_1409 : sub8 [3, 3, -1] = true := by decide +kernel
theorem sub8_1410 : sub8 [3, 3, 0] = true := by decide +kernel
theorem sub8_1411 : sub8 [3, 3, 1] = true := by decide +kernel
theorem sub8_1412 : sub8 [3, 3, 2] = true := by decide +kernel
theorem sub8_1413 : sub8 [3, 3, 3] = true := by decide +kernel
theorem sub8_1414 : sub8 [3, 3, 4] = true := by decide +kernel
theorem sub8_1415 : sub8 [3, 3, 5] = true := by decide +kernel
theorem sub8_1416 : sub8 [3, 3, 6] = true := by decide +kernel
theorem sub8_1417 : sub8 [3, 4] = true := by decide +kernel
theorem sub8_1418 : sub8 [3, 5] = true := by decide +kernel
theorem sub8_1419 : sub8 [4, -9] = true := by decide +kernel
theorem sub8_1420 : sub8 [4, -8] = true := by decide +kernel
theorem sub8_1421 : sub8 [4, -7] = true := by decide +kernel
theorem sub8_1422 : sub8 [4, -6] = true := by decide +kernel
theorem sub8_1423 : sub8 [4, -5, -9] = true := by decide +kernel
theorem sub8_1424 : sub8 [4, -5, -8] = true := by decide +kernel
theorem sub8_1425 : sub8 [4, -5, -7] = true := by decide +kernel
theorem sub8_1426 : sub8 [4, -5, -6] = true := by decide +kernel
theorem sub8_1427 : sub8 [4, -5, -5] = true := by decide +kernel
theorem sub8_1428 : sub8 [4, -5, -4] = true := by decide +kernel
theorem sub8_1429 : sub8 [4, -5, -3] = true := by decide +kernel
theorem sub8_1430 : sub8 [4, -5, -2] = true := by decide +kernel
theorem sub8_1431 : sub8 [4, -5, -1] = true := by decide +kernel
theorem sub8_1432 : sub8 [4, -5, 0] = true := by decide +kernel
theorem sub8_1433 : sub8 [4, -5, 1] = true := by decide +kernel
theorem sub8_1434 : sub8 [4, -5, 2] = true := by decide +kernel
theorem sub8_1435 : sub8 [4, -5, 3] = true := by decide +kernel
theorem sub8_1436 : sub8 [4, -5, 4] = true := by decide +kernel
theorem sub8_1437 : sub8 [4, -5, 5] = true := by decide +kernel
theorem sub8_1438 : sub8 [4, -4, -9] = true := by decide +kernel
theorem sub8_1439 : sub8 [4, -4, -8] = true := by decide +kernel
theorem sb8_44 : ∀ q ∈ blk8_44, sub8 q = true := by
  unfold blk8_44
  exact List.forall_mem_cons.2 ⟨sub8_1408, List.forall_mem_cons.2 ⟨sub8_1409, List.forall_mem_cons.2 ⟨sub8_1410, List.forall_mem_cons.2 ⟨sub8_1411, List.forall_mem_cons.2 ⟨sub8_1412, List.forall_mem_cons.2 ⟨sub8_1413, List.forall_mem_cons.2 ⟨sub8_1414, List.forall_mem_cons.2 ⟨sub8_1415, List.forall_mem_cons.2 ⟨sub8_1416, List.forall_mem_cons.2 ⟨sub8_1417, List.forall_mem_cons.2 ⟨sub8_1418, List.forall_mem_cons.2 ⟨sub8_1419, List.forall_mem_cons.2 ⟨sub8_1420, List.forall_mem_cons.2 ⟨sub8_1421, List.forall_mem_cons.2 ⟨sub8_1422, List.forall_mem_cons.2 ⟨sub8_1423, List.forall_mem_cons.2 ⟨sub8_1424, List.forall_mem_cons.2 ⟨sub8_1425, List.forall_mem_cons.2 ⟨sub8_1426, List.forall_mem_cons.2 ⟨sub8_1427, List.forall_mem_cons.2 ⟨sub8_1428, List.forall_mem_cons.2 ⟨sub8_1429, List.forall_mem_cons.2 ⟨sub8_1430, List.forall_mem_cons.2 ⟨sub8_1431, List.forall_mem_cons.2 ⟨sub8_1432, List.forall_mem_cons.2 ⟨sub8_1433, List.forall_mem_cons.2 ⟨sub8_1434, List.forall_mem_cons.2 ⟨sub8_1435, List.forall_mem_cons.2 ⟨sub8_1436, List.forall_mem_cons.2 ⟨sub8_1437, List.forall_mem_cons.2 ⟨sub8_1438, List.forall_mem_cons.2 ⟨sub8_1439, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1440 : sub8 [4, -4, -7] = true := by decide +kernel
theorem sub8_1441 : sub8 [4, -4, -6] = true := by decide +kernel
theorem sub8_1442 : sub8 [4, -4, -5] = true := by decide +kernel
theorem sub8_1443 : sub8 [4, -4, -4] = true := by decide +kernel
theorem sub8_1444 : sub8 [4, -4, -3] = true := by decide +kernel
theorem sub8_1445 : sub8 [4, -4, -2] = true := by decide +kernel
theorem sub8_1446 : sub8 [4, -4, -1] = true := by decide +kernel
theorem sub8_1447 : sub8 [4, -4, 0] = true := by decide +kernel
theorem sub8_1448 : sub8 [4, -4, 1] = true := by decide +kernel
theorem sub8_1449 : sub8 [4, -4, 2] = true := by decide +kernel
theorem sub8_1450 : sub8 [4, -4, 3] = true := by decide +kernel
theorem sub8_1451 : sub8 [4, -4, 4] = true := by decide +kernel
theorem sub8_1452 : sub8 [4, -4, 5] = true := by decide +kernel
theorem sub8_1453 : sub8 [4, -4, 6] = true := by decide +kernel
theorem sub8_1454 : sub8 [4, -3, -9] = true := by decide +kernel
theorem sub8_1455 : sub8 [4, -3, -8] = true := by decide +kernel
theorem sub8_1456 : sub8 [4, -3, -7] = true := by decide +kernel
theorem sub8_1457 : sub8 [4, -3, -6] = true := by decide +kernel
theorem sub8_1458 : sub8 [4, -3, -5] = true := by decide +kernel
theorem sub8_1459 : sub8 [4, -3, -4] = true := by decide +kernel
theorem sub8_1460 : sub8 [4, -3, -3] = true := by decide +kernel
theorem sub8_1461 : sub8 [4, -3, -2] = true := by decide +kernel
theorem sub8_1462 : sub8 [4, -3, -1] = true := by decide +kernel
theorem sub8_1463 : sub8 [4, -3, 0] = true := by decide +kernel
theorem sub8_1464 : sub8 [4, -3, 1] = true := by decide +kernel
theorem sub8_1465 : sub8 [4, -3, 2] = true := by decide +kernel
theorem sub8_1466 : sub8 [4, -3, 3] = true := by decide +kernel
theorem sub8_1467 : sub8 [4, -3, 4] = true := by decide +kernel
theorem sub8_1468 : sub8 [4, -3, 5] = true := by decide +kernel
theorem sub8_1469 : sub8 [4, -3, 6] = true := by decide +kernel
theorem sub8_1470 : sub8 [4, -2, -9] = true := by decide +kernel
theorem sub8_1471 : sub8 [4, -2, -8] = true := by decide +kernel
theorem sb8_45 : ∀ q ∈ blk8_45, sub8 q = true := by
  unfold blk8_45
  exact List.forall_mem_cons.2 ⟨sub8_1440, List.forall_mem_cons.2 ⟨sub8_1441, List.forall_mem_cons.2 ⟨sub8_1442, List.forall_mem_cons.2 ⟨sub8_1443, List.forall_mem_cons.2 ⟨sub8_1444, List.forall_mem_cons.2 ⟨sub8_1445, List.forall_mem_cons.2 ⟨sub8_1446, List.forall_mem_cons.2 ⟨sub8_1447, List.forall_mem_cons.2 ⟨sub8_1448, List.forall_mem_cons.2 ⟨sub8_1449, List.forall_mem_cons.2 ⟨sub8_1450, List.forall_mem_cons.2 ⟨sub8_1451, List.forall_mem_cons.2 ⟨sub8_1452, List.forall_mem_cons.2 ⟨sub8_1453, List.forall_mem_cons.2 ⟨sub8_1454, List.forall_mem_cons.2 ⟨sub8_1455, List.forall_mem_cons.2 ⟨sub8_1456, List.forall_mem_cons.2 ⟨sub8_1457, List.forall_mem_cons.2 ⟨sub8_1458, List.forall_mem_cons.2 ⟨sub8_1459, List.forall_mem_cons.2 ⟨sub8_1460, List.forall_mem_cons.2 ⟨sub8_1461, List.forall_mem_cons.2 ⟨sub8_1462, List.forall_mem_cons.2 ⟨sub8_1463, List.forall_mem_cons.2 ⟨sub8_1464, List.forall_mem_cons.2 ⟨sub8_1465, List.forall_mem_cons.2 ⟨sub8_1466, List.forall_mem_cons.2 ⟨sub8_1467, List.forall_mem_cons.2 ⟨sub8_1468, List.forall_mem_cons.2 ⟨sub8_1469, List.forall_mem_cons.2 ⟨sub8_1470, List.forall_mem_cons.2 ⟨sub8_1471, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1472 : sub8 [4, -2, -7] = true := by decide +kernel
theorem sub8_1473 : sub8 [4, -2, -6] = true := by decide +kernel
theorem sub8_1474 : sub8 [4, -2, -5] = true := by decide +kernel
theorem sub8_1475 : sub8 [4, -2, -4] = true := by decide +kernel
theorem sub8_1476 : sub8 [4, -2, -3] = true := by decide +kernel
theorem sub8_1477 : sub8 [4, -2, -2] = true := by decide +kernel
theorem sub8_1478 : sub8 [4, -2, -1] = true := by decide +kernel
theorem sub8_1479 : sub8 [4, -2, 0] = true := by decide +kernel
theorem sub8_1480 : sub8 [4, -2, 1] = true := by decide +kernel
theorem sub8_1481 : sub8 [4, -2, 2] = true := by decide +kernel
theorem sub8_1482 : sub8 [4, -2, 3] = true := by decide +kernel
theorem sub8_1483 : sub8 [4, -2, 4] = true := by decide +kernel
theorem sub8_1484 : sub8 [4, -2, 5] = true := by decide +kernel
theorem sub8_1485 : sub8 [4, -2, 6] = true := by decide +kernel
theorem sub8_1486 : sub8 [4, -2, 7] = true := by decide +kernel
theorem sub8_1487 : sub8 [4, -1, -9] = true := by decide +kernel
theorem sub8_1488 : sub8 [4, -1, -8] = true := by decide +kernel
theorem sub8_1489 : sub8 [4, -1, -7] = true := by decide +kernel
theorem sub8_1490 : sub8 [4, -1, -6] = true := by decide +kernel
theorem sub8_1491 : sub8 [4, -1, -5] = true := by decide +kernel
theorem sub8_1492 : sub8 [4, -1, -4] = true := by decide +kernel
theorem sub8_1493 : sub8 [4, -1, -3] = true := by decide +kernel
theorem sub8_1494 : sub8 [4, -1, -2] = true := by decide +kernel
theorem sub8_1495 : sub8 [4, -1, -1] = true := by decide +kernel
theorem sub8_1496 : sub8 [4, -1, 0] = true := by decide +kernel
theorem sub8_1497 : sub8 [4, -1, 1] = true := by decide +kernel
theorem sub8_1498 : sub8 [4, -1, 2] = true := by decide +kernel
theorem sub8_1499 : sub8 [4, -1, 3] = true := by decide +kernel
theorem sub8_1500 : sub8 [4, -1, 4] = true := by decide +kernel
theorem sub8_1501 : sub8 [4, -1, 5] = true := by decide +kernel
theorem sub8_1502 : sub8 [4, -1, 6] = true := by decide +kernel
theorem sub8_1503 : sub8 [4, -1, 7] = true := by decide +kernel
theorem sb8_46 : ∀ q ∈ blk8_46, sub8 q = true := by
  unfold blk8_46
  exact List.forall_mem_cons.2 ⟨sub8_1472, List.forall_mem_cons.2 ⟨sub8_1473, List.forall_mem_cons.2 ⟨sub8_1474, List.forall_mem_cons.2 ⟨sub8_1475, List.forall_mem_cons.2 ⟨sub8_1476, List.forall_mem_cons.2 ⟨sub8_1477, List.forall_mem_cons.2 ⟨sub8_1478, List.forall_mem_cons.2 ⟨sub8_1479, List.forall_mem_cons.2 ⟨sub8_1480, List.forall_mem_cons.2 ⟨sub8_1481, List.forall_mem_cons.2 ⟨sub8_1482, List.forall_mem_cons.2 ⟨sub8_1483, List.forall_mem_cons.2 ⟨sub8_1484, List.forall_mem_cons.2 ⟨sub8_1485, List.forall_mem_cons.2 ⟨sub8_1486, List.forall_mem_cons.2 ⟨sub8_1487, List.forall_mem_cons.2 ⟨sub8_1488, List.forall_mem_cons.2 ⟨sub8_1489, List.forall_mem_cons.2 ⟨sub8_1490, List.forall_mem_cons.2 ⟨sub8_1491, List.forall_mem_cons.2 ⟨sub8_1492, List.forall_mem_cons.2 ⟨sub8_1493, List.forall_mem_cons.2 ⟨sub8_1494, List.forall_mem_cons.2 ⟨sub8_1495, List.forall_mem_cons.2 ⟨sub8_1496, List.forall_mem_cons.2 ⟨sub8_1497, List.forall_mem_cons.2 ⟨sub8_1498, List.forall_mem_cons.2 ⟨sub8_1499, List.forall_mem_cons.2 ⟨sub8_1500, List.forall_mem_cons.2 ⟨sub8_1501, List.forall_mem_cons.2 ⟨sub8_1502, List.forall_mem_cons.2 ⟨sub8_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1504 : sub8 [4, 0, -9] = true := by decide +kernel
theorem sub8_1505 : sub8 [4, 0, -8] = true := by decide +kernel
theorem sub8_1506 : sub8 [4, 0, -7] = true := by decide +kernel
theorem sub8_1507 : sub8 [4, 0, -6] = true := by decide +kernel
theorem sub8_1508 : sub8 [4, 0, -5] = true := by decide +kernel
theorem sub8_1509 : sub8 [4, 0, -4] = true := by decide +kernel
theorem sub8_1510 : sub8 [4, 0, -3] = true := by decide +kernel
theorem sub8_1511 : sub8 [4, 0, -2] = true := by decide +kernel
theorem sub8_1512 : sub8 [4, 0, -1] = true := by decide +kernel
theorem sub8_1513 : sub8 [4, 0, 0] = true := by decide +kernel
theorem sub8_1514 : sub8 [4, 0, 1] = true := by decide +kernel
theorem sub8_1515 : sub8 [4, 0, 2] = true := by decide +kernel
theorem sub8_1516 : sub8 [4, 0, 3] = true := by decide +kernel
theorem sub8_1517 : sub8 [4, 0, 4] = true := by decide +kernel
theorem sub8_1518 : sub8 [4, 0, 5] = true := by decide +kernel
theorem sub8_1519 : sub8 [4, 0, 6] = true := by decide +kernel
theorem sub8_1520 : sub8 [4, 1, -8] = true := by decide +kernel
theorem sub8_1521 : sub8 [4, 1, -7] = true := by decide +kernel
theorem sub8_1522 : sub8 [4, 1, -6] = true := by decide +kernel
theorem sub8_1523 : sub8 [4, 1, -5] = true := by decide +kernel
theorem sub8_1524 : sub8 [4, 1, -4] = true := by decide +kernel
theorem sub8_1525 : sub8 [4, 1, -3] = true := by decide +kernel
theorem sub8_1526 : sub8 [4, 1, -2] = true := by decide +kernel
theorem sub8_1527 : sub8 [4, 1, -1] = true := by decide +kernel
theorem sub8_1528 : sub8 [4, 1, 0] = true := by decide +kernel
theorem sub8_1529 : sub8 [4, 1, 1] = true := by decide +kernel
theorem sub8_1530 : sub8 [4, 1, 2] = true := by decide +kernel
theorem sub8_1531 : sub8 [4, 1, 3] = true := by decide +kernel
theorem sub8_1532 : sub8 [4, 1, 4] = true := by decide +kernel
theorem sub8_1533 : sub8 [4, 1, 5] = true := by decide +kernel
theorem sub8_1534 : sub8 [4, 1, 6] = true := by decide +kernel
theorem sub8_1535 : sub8 [4, 2] = true := by decide +kernel
theorem sb8_47 : ∀ q ∈ blk8_47, sub8 q = true := by
  unfold blk8_47
  exact List.forall_mem_cons.2 ⟨sub8_1504, List.forall_mem_cons.2 ⟨sub8_1505, List.forall_mem_cons.2 ⟨sub8_1506, List.forall_mem_cons.2 ⟨sub8_1507, List.forall_mem_cons.2 ⟨sub8_1508, List.forall_mem_cons.2 ⟨sub8_1509, List.forall_mem_cons.2 ⟨sub8_1510, List.forall_mem_cons.2 ⟨sub8_1511, List.forall_mem_cons.2 ⟨sub8_1512, List.forall_mem_cons.2 ⟨sub8_1513, List.forall_mem_cons.2 ⟨sub8_1514, List.forall_mem_cons.2 ⟨sub8_1515, List.forall_mem_cons.2 ⟨sub8_1516, List.forall_mem_cons.2 ⟨sub8_1517, List.forall_mem_cons.2 ⟨sub8_1518, List.forall_mem_cons.2 ⟨sub8_1519, List.forall_mem_cons.2 ⟨sub8_1520, List.forall_mem_cons.2 ⟨sub8_1521, List.forall_mem_cons.2 ⟨sub8_1522, List.forall_mem_cons.2 ⟨sub8_1523, List.forall_mem_cons.2 ⟨sub8_1524, List.forall_mem_cons.2 ⟨sub8_1525, List.forall_mem_cons.2 ⟨sub8_1526, List.forall_mem_cons.2 ⟨sub8_1527, List.forall_mem_cons.2 ⟨sub8_1528, List.forall_mem_cons.2 ⟨sub8_1529, List.forall_mem_cons.2 ⟨sub8_1530, List.forall_mem_cons.2 ⟨sub8_1531, List.forall_mem_cons.2 ⟨sub8_1532, List.forall_mem_cons.2 ⟨sub8_1533, List.forall_mem_cons.2 ⟨sub8_1534, List.forall_mem_cons.2 ⟨sub8_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1536 : sub8 [4, 3] = true := by decide +kernel
theorem sub8_1537 : sub8 [4, 4] = true := by decide +kernel
theorem sub8_1538 : sub8 [5, -9] = true := by decide +kernel
theorem sub8_1539 : sub8 [5, -8] = true := by decide +kernel
theorem sub8_1540 : sub8 [5, -7] = true := by decide +kernel
theorem sub8_1541 : sub8 [5, -6] = true := by decide +kernel
theorem sub8_1542 : sub8 [5, -5, -8] = true := by decide +kernel
theorem sub8_1543 : sub8 [5, -5, -7] = true := by decide +kernel
theorem sub8_1544 : sub8 [5, -5, -6] = true := by decide +kernel
theorem sub8_1545 : sub8 [5, -5, -5] = true := by decide +kernel
theorem sub8_1546 : sub8 [5, -5, -4] = true := by decide +kernel
theorem sub8_1547 : sub8 [5, -5, -3] = true := by decide +kernel
theorem sub8_1548 : sub8 [5, -5, -2] = true := by decide +kernel
theorem sub8_1549 : sub8 [5, -5, -1] = true := by decide +kernel
theorem sub8_1550 : sub8 [5, -5, 0] = true := by decide +kernel
theorem sub8_1551 : sub8 [5, -5, 1] = true := by decide +kernel
theorem sub8_1552 : sub8 [5, -5, 2] = true := by decide +kernel
theorem sub8_1553 : sub8 [5, -5, 3] = true := by decide +kernel
theorem sub8_1554 : sub8 [5, -5, 4] = true := by decide +kernel
theorem sub8_1555 : sub8 [5, -5, 5] = true := by decide +kernel
theorem sub8_1556 : sub8 [5, -4, -9] = true := by decide +kernel
theorem sub8_1557 : sub8 [5, -4, -8] = true := by decide +kernel
theorem sub8_1558 : sub8 [5, -4, -7] = true := by decide +kernel
theorem sub8_1559 : sub8 [5, -4, -6] = true := by decide +kernel
theorem sub8_1560 : sub8 [5, -4, -5] = true := by decide +kernel
theorem sub8_1561 : sub8 [5, -4, -4] = true := by decide +kernel
theorem sub8_1562 : sub8 [5, -4, -3] = true := by decide +kernel
theorem sub8_1563 : sub8 [5, -4, -2] = true := by decide +kernel
theorem sub8_1564 : sub8 [5, -4, -1] = true := by decide +kernel
theorem sub8_1565 : sub8 [5, -4, 0] = true := by decide +kernel
theorem sub8_1566 : sub8 [5, -4, 1] = true := by decide +kernel
theorem sub8_1567 : sub8 [5, -4, 2] = true := by decide +kernel
theorem sb8_48 : ∀ q ∈ blk8_48, sub8 q = true := by
  unfold blk8_48
  exact List.forall_mem_cons.2 ⟨sub8_1536, List.forall_mem_cons.2 ⟨sub8_1537, List.forall_mem_cons.2 ⟨sub8_1538, List.forall_mem_cons.2 ⟨sub8_1539, List.forall_mem_cons.2 ⟨sub8_1540, List.forall_mem_cons.2 ⟨sub8_1541, List.forall_mem_cons.2 ⟨sub8_1542, List.forall_mem_cons.2 ⟨sub8_1543, List.forall_mem_cons.2 ⟨sub8_1544, List.forall_mem_cons.2 ⟨sub8_1545, List.forall_mem_cons.2 ⟨sub8_1546, List.forall_mem_cons.2 ⟨sub8_1547, List.forall_mem_cons.2 ⟨sub8_1548, List.forall_mem_cons.2 ⟨sub8_1549, List.forall_mem_cons.2 ⟨sub8_1550, List.forall_mem_cons.2 ⟨sub8_1551, List.forall_mem_cons.2 ⟨sub8_1552, List.forall_mem_cons.2 ⟨sub8_1553, List.forall_mem_cons.2 ⟨sub8_1554, List.forall_mem_cons.2 ⟨sub8_1555, List.forall_mem_cons.2 ⟨sub8_1556, List.forall_mem_cons.2 ⟨sub8_1557, List.forall_mem_cons.2 ⟨sub8_1558, List.forall_mem_cons.2 ⟨sub8_1559, List.forall_mem_cons.2 ⟨sub8_1560, List.forall_mem_cons.2 ⟨sub8_1561, List.forall_mem_cons.2 ⟨sub8_1562, List.forall_mem_cons.2 ⟨sub8_1563, List.forall_mem_cons.2 ⟨sub8_1564, List.forall_mem_cons.2 ⟨sub8_1565, List.forall_mem_cons.2 ⟨sub8_1566, List.forall_mem_cons.2 ⟨sub8_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1568 : sub8 [5, -4, 3] = true := by decide +kernel
theorem sub8_1569 : sub8 [5, -4, 4] = true := by decide +kernel
theorem sub8_1570 : sub8 [5, -4, 5] = true := by decide +kernel
theorem sub8_1571 : sub8 [5, -3, -9] = true := by decide +kernel
theorem sub8_1572 : sub8 [5, -3, -8] = true := by decide +kernel
theorem sub8_1573 : sub8 [5, -3, -7] = true := by decide +kernel
theorem sub8_1574 : sub8 [5, -3, -6] = true := by decide +kernel
theorem sub8_1575 : sub8 [5, -3, -5] = true := by decide +kernel
theorem sub8_1576 : sub8 [5, -3, -4] = true := by decide +kernel
theorem sub8_1577 : sub8 [5, -3, -3] = true := by decide +kernel
theorem sub8_1578 : sub8 [5, -3, -2] = true := by decide +kernel
theorem sub8_1579 : sub8 [5, -3, -1] = true := by decide +kernel
theorem sub8_1580 : sub8 [5, -3, 0] = true := by decide +kernel
theorem sub8_1581 : sub8 [5, -3, 1] = true := by decide +kernel
theorem sub8_1582 : sub8 [5, -3, 2] = true := by decide +kernel
theorem sub8_1583 : sub8 [5, -3, 3] = true := by decide +kernel
theorem sub8_1584 : sub8 [5, -3, 4] = true := by decide +kernel
theorem sub8_1585 : sub8 [5, -3, 5] = true := by decide +kernel
theorem sub8_1586 : sub8 [5, -3, 6] = true := by decide +kernel
theorem sub8_1587 : sub8 [5, -2, -9] = true := by decide +kernel
theorem sub8_1588 : sub8 [5, -2, -8] = true := by decide +kernel
theorem sub8_1589 : sub8 [5, -2, -7] = true := by decide +kernel
theorem sub8_1590 : sub8 [5, -2, -6] = true := by decide +kernel
theorem sub8_1591 : sub8 [5, -2, -5] = true := by decide +kernel
theorem sub8_1592 : sub8 [5, -2, -4] = true := by decide +kernel
theorem sub8_1593 : sub8 [5, -2, -3] = true := by decide +kernel
theorem sub8_1594 : sub8 [5, -2, -2] = true := by decide +kernel
theorem sub8_1595 : sub8 [5, -2, -1] = true := by decide +kernel
theorem sub8_1596 : sub8 [5, -2, 0] = true := by decide +kernel
theorem sub8_1597 : sub8 [5, -2, 1] = true := by decide +kernel
theorem sub8_1598 : sub8 [5, -2, 2] = true := by decide +kernel
theorem sub8_1599 : sub8 [5, -2, 3] = true := by decide +kernel
theorem sb8_49 : ∀ q ∈ blk8_49, sub8 q = true := by
  unfold blk8_49
  exact List.forall_mem_cons.2 ⟨sub8_1568, List.forall_mem_cons.2 ⟨sub8_1569, List.forall_mem_cons.2 ⟨sub8_1570, List.forall_mem_cons.2 ⟨sub8_1571, List.forall_mem_cons.2 ⟨sub8_1572, List.forall_mem_cons.2 ⟨sub8_1573, List.forall_mem_cons.2 ⟨sub8_1574, List.forall_mem_cons.2 ⟨sub8_1575, List.forall_mem_cons.2 ⟨sub8_1576, List.forall_mem_cons.2 ⟨sub8_1577, List.forall_mem_cons.2 ⟨sub8_1578, List.forall_mem_cons.2 ⟨sub8_1579, List.forall_mem_cons.2 ⟨sub8_1580, List.forall_mem_cons.2 ⟨sub8_1581, List.forall_mem_cons.2 ⟨sub8_1582, List.forall_mem_cons.2 ⟨sub8_1583, List.forall_mem_cons.2 ⟨sub8_1584, List.forall_mem_cons.2 ⟨sub8_1585, List.forall_mem_cons.2 ⟨sub8_1586, List.forall_mem_cons.2 ⟨sub8_1587, List.forall_mem_cons.2 ⟨sub8_1588, List.forall_mem_cons.2 ⟨sub8_1589, List.forall_mem_cons.2 ⟨sub8_1590, List.forall_mem_cons.2 ⟨sub8_1591, List.forall_mem_cons.2 ⟨sub8_1592, List.forall_mem_cons.2 ⟨sub8_1593, List.forall_mem_cons.2 ⟨sub8_1594, List.forall_mem_cons.2 ⟨sub8_1595, List.forall_mem_cons.2 ⟨sub8_1596, List.forall_mem_cons.2 ⟨sub8_1597, List.forall_mem_cons.2 ⟨sub8_1598, List.forall_mem_cons.2 ⟨sub8_1599, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1600 : sub8 [5, -2, 4] = true := by decide +kernel
theorem sub8_1601 : sub8 [5, -2, 5] = true := by decide +kernel
theorem sub8_1602 : sub8 [5, -2, 6] = true := by decide +kernel
theorem sub8_1603 : sub8 [5, -1, -9] = true := by decide +kernel
theorem sub8_1604 : sub8 [5, -1, -8] = true := by decide +kernel
theorem sub8_1605 : sub8 [5, -1, -7] = true := by decide +kernel
theorem sub8_1606 : sub8 [5, -1, -6] = true := by decide +kernel
theorem sub8_1607 : sub8 [5, -1, -5] = true := by decide +kernel
theorem sub8_1608 : sub8 [5, -1, -4] = true := by decide +kernel
theorem sub8_1609 : sub8 [5, -1, -3] = true := by decide +kernel
theorem sub8_1610 : sub8 [5, -1, -2] = true := by decide +kernel
theorem sub8_1611 : sub8 [5, -1, -1] = true := by decide +kernel
theorem sub8_1612 : sub8 [5, -1, 0] = true := by decide +kernel
theorem sub8_1613 : sub8 [5, -1, 1] = true := by decide +kernel
theorem sub8_1614 : sub8 [5, -1, 2] = true := by decide +kernel
theorem sub8_1615 : sub8 [5, -1, 3] = true := by decide +kernel
theorem sub8_1616 : sub8 [5, -1, 4] = true := by decide +kernel
theorem sub8_1617 : sub8 [5, -1, 5] = true := by decide +kernel
theorem sub8_1618 : sub8 [5, -1, 6] = true := by decide +kernel
theorem sub8_1619 : sub8 [5, 0, -8] = true := by decide +kernel
theorem sub8_1620 : sub8 [5, 0, -7] = true := by decide +kernel
theorem sub8_1621 : sub8 [5, 0, -6] = true := by decide +kernel
theorem sub8_1622 : sub8 [5, 0, -5] = true := by decide +kernel
theorem sub8_1623 : sub8 [5, 0, -4] = true := by decide +kernel
theorem sub8_1624 : sub8 [5, 0, -3] = true := by decide +kernel
theorem sub8_1625 : sub8 [5, 0, -2] = true := by decide +kernel
theorem sub8_1626 : sub8 [5, 0, -1] = true := by decide +kernel
theorem sub8_1627 : sub8 [5, 0, 0] = true := by decide +kernel
theorem sub8_1628 : sub8 [5, 0, 1] = true := by decide +kernel
theorem sub8_1629 : sub8 [5, 0, 2] = true := by decide +kernel
theorem sub8_1630 : sub8 [5, 0, 3] = true := by decide +kernel
theorem sub8_1631 : sub8 [5, 0, 4] = true := by decide +kernel
theorem sb8_50 : ∀ q ∈ blk8_50, sub8 q = true := by
  unfold blk8_50
  exact List.forall_mem_cons.2 ⟨sub8_1600, List.forall_mem_cons.2 ⟨sub8_1601, List.forall_mem_cons.2 ⟨sub8_1602, List.forall_mem_cons.2 ⟨sub8_1603, List.forall_mem_cons.2 ⟨sub8_1604, List.forall_mem_cons.2 ⟨sub8_1605, List.forall_mem_cons.2 ⟨sub8_1606, List.forall_mem_cons.2 ⟨sub8_1607, List.forall_mem_cons.2 ⟨sub8_1608, List.forall_mem_cons.2 ⟨sub8_1609, List.forall_mem_cons.2 ⟨sub8_1610, List.forall_mem_cons.2 ⟨sub8_1611, List.forall_mem_cons.2 ⟨sub8_1612, List.forall_mem_cons.2 ⟨sub8_1613, List.forall_mem_cons.2 ⟨sub8_1614, List.forall_mem_cons.2 ⟨sub8_1615, List.forall_mem_cons.2 ⟨sub8_1616, List.forall_mem_cons.2 ⟨sub8_1617, List.forall_mem_cons.2 ⟨sub8_1618, List.forall_mem_cons.2 ⟨sub8_1619, List.forall_mem_cons.2 ⟨sub8_1620, List.forall_mem_cons.2 ⟨sub8_1621, List.forall_mem_cons.2 ⟨sub8_1622, List.forall_mem_cons.2 ⟨sub8_1623, List.forall_mem_cons.2 ⟨sub8_1624, List.forall_mem_cons.2 ⟨sub8_1625, List.forall_mem_cons.2 ⟨sub8_1626, List.forall_mem_cons.2 ⟨sub8_1627, List.forall_mem_cons.2 ⟨sub8_1628, List.forall_mem_cons.2 ⟨sub8_1629, List.forall_mem_cons.2 ⟨sub8_1630, List.forall_mem_cons.2 ⟨sub8_1631, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1632 : sub8 [5, 0, 5] = true := by decide +kernel
theorem sub8_1633 : sub8 [5, 0, 6] = true := by decide +kernel
theorem sub8_1634 : sub8 [5, 1] = true := by decide +kernel
theorem sub8_1635 : sub8 [5, 2] = true := by decide +kernel
theorem sub8_1636 : sub8 [5, 3] = true := by decide +kernel
theorem sub8_1637 : sub8 [6, -9] = true := by decide +kernel
theorem sub8_1638 : sub8 [6, -8] = true := by decide +kernel
theorem sub8_1639 : sub8 [6, -7] = true := by decide +kernel
theorem sub8_1640 : sub8 [6, -6] = true := by decide +kernel
theorem sub8_1641 : sub8 [6, -5] = true := by decide +kernel
theorem sub8_1642 : sub8 [6, -4, -8] = true := by decide +kernel
theorem sub8_1643 : sub8 [6, -4, -7] = true := by decide +kernel
theorem sub8_1644 : sub8 [6, -4, -6] = true := by decide +kernel
theorem sub8_1645 : sub8 [6, -4, -5] = true := by decide +kernel
theorem sub8_1646 : sub8 [6, -4, -4] = true := by decide +kernel
theorem sub8_1647 : sub8 [6, -4, -3] = true := by decide +kernel
theorem sub8_1648 : sub8 [6, -4, -2] = true := by decide +kernel
theorem sub8_1649 : sub8 [6, -4, -1] = true := by decide +kernel
theorem sub8_1650 : sub8 [6, -4, 0] = true := by decide +kernel
theorem sub8_1651 : sub8 [6, -4, 1] = true := by decide +kernel
theorem sub8_1652 : sub8 [6, -4, 2] = true := by decide +kernel
theorem sub8_1653 : sub8 [6, -4, 3] = true := by decide +kernel
theorem sub8_1654 : sub8 [6, -4, 4] = true := by decide +kernel
theorem sub8_1655 : sub8 [6, -4, 5] = true := by decide +kernel
theorem sub8_1656 : sub8 [6, -3, -8] = true := by decide +kernel
theorem sub8_1657 : sub8 [6, -3, -7] = true := by decide +kernel
theorem sub8_1658 : sub8 [6, -3, -6] = true := by decide +kernel
theorem sub8_1659 : sub8 [6, -3, -5] = true := by decide +kernel
theorem sub8_1660 : sub8 [6, -3, -4] = true := by decide +kernel
theorem sub8_1661 : sub8 [6, -3, -3] = true := by decide +kernel
theorem sub8_1662 : sub8 [6, -3, -2] = true := by decide +kernel
theorem sub8_1663 : sub8 [6, -3, -1] = true := by decide +kernel
theorem sb8_51 : ∀ q ∈ blk8_51, sub8 q = true := by
  unfold blk8_51
  exact List.forall_mem_cons.2 ⟨sub8_1632, List.forall_mem_cons.2 ⟨sub8_1633, List.forall_mem_cons.2 ⟨sub8_1634, List.forall_mem_cons.2 ⟨sub8_1635, List.forall_mem_cons.2 ⟨sub8_1636, List.forall_mem_cons.2 ⟨sub8_1637, List.forall_mem_cons.2 ⟨sub8_1638, List.forall_mem_cons.2 ⟨sub8_1639, List.forall_mem_cons.2 ⟨sub8_1640, List.forall_mem_cons.2 ⟨sub8_1641, List.forall_mem_cons.2 ⟨sub8_1642, List.forall_mem_cons.2 ⟨sub8_1643, List.forall_mem_cons.2 ⟨sub8_1644, List.forall_mem_cons.2 ⟨sub8_1645, List.forall_mem_cons.2 ⟨sub8_1646, List.forall_mem_cons.2 ⟨sub8_1647, List.forall_mem_cons.2 ⟨sub8_1648, List.forall_mem_cons.2 ⟨sub8_1649, List.forall_mem_cons.2 ⟨sub8_1650, List.forall_mem_cons.2 ⟨sub8_1651, List.forall_mem_cons.2 ⟨sub8_1652, List.forall_mem_cons.2 ⟨sub8_1653, List.forall_mem_cons.2 ⟨sub8_1654, List.forall_mem_cons.2 ⟨sub8_1655, List.forall_mem_cons.2 ⟨sub8_1656, List.forall_mem_cons.2 ⟨sub8_1657, List.forall_mem_cons.2 ⟨sub8_1658, List.forall_mem_cons.2 ⟨sub8_1659, List.forall_mem_cons.2 ⟨sub8_1660, List.forall_mem_cons.2 ⟨sub8_1661, List.forall_mem_cons.2 ⟨sub8_1662, List.forall_mem_cons.2 ⟨sub8_1663, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1664 : sub8 [6, -3, 0] = true := by decide +kernel
theorem sub8_1665 : sub8 [6, -3, 1] = true := by decide +kernel
theorem sub8_1666 : sub8 [6, -3, 2] = true := by decide +kernel
theorem sub8_1667 : sub8 [6, -3, 3] = true := by decide +kernel
theorem sub8_1668 : sub8 [6, -3, 4] = true := by decide +kernel
theorem sub8_1669 : sub8 [6, -3, 5] = true := by decide +kernel
theorem sub8_1670 : sub8 [6, -2, -8] = true := by decide +kernel
theorem sub8_1671 : sub8 [6, -2, -7] = true := by decide +kernel
theorem sub8_1672 : sub8 [6, -2, -6] = true := by decide +kernel
theorem sub8_1673 : sub8 [6, -2, -5] = true := by decide +kernel
theorem sub8_1674 : sub8 [6, -2, -4] = true := by decide +kernel
theorem sub8_1675 : sub8 [6, -2, -3] = true := by decide +kernel
theorem sub8_1676 : sub8 [6, -2, -2] = true := by decide +kernel
theorem sub8_1677 : sub8 [6, -2, -1] = true := by decide +kernel
theorem sub8_1678 : sub8 [6, -2, 0] = true := by decide +kernel
theorem sub8_1679 : sub8 [6, -2, 1] = true := by decide +kernel
theorem sub8_1680 : sub8 [6, -2, 2] = true := by decide +kernel
theorem sub8_1681 : sub8 [6, -2, 3] = true := by decide +kernel
theorem sub8_1682 : sub8 [6, -2, 4] = true := by decide +kernel
theorem sub8_1683 : sub8 [6, -2, 5] = true := by decide +kernel
theorem sub8_1684 : sub8 [6, -1, -8] = true := by decide +kernel
theorem sub8_1685 : sub8 [6, -1, -7] = true := by decide +kernel
theorem sub8_1686 : sub8 [6, -1, -6] = true := by decide +kernel
theorem sub8_1687 : sub8 [6, -1, -5] = true := by decide +kernel
theorem sub8_1688 : sub8 [6, -1, -4] = true := by decide +kernel
theorem sub8_1689 : sub8 [6, -1, -3] = true := by decide +kernel
theorem sub8_1690 : sub8 [6, -1, -2] = true := by decide +kernel
theorem sub8_1691 : sub8 [6, -1, -1] = true := by decide +kernel
theorem sub8_1692 : sub8 [6, -1, 0] = true := by decide +kernel
theorem sub8_1693 : sub8 [6, -1, 1] = true := by decide +kernel
theorem sub8_1694 : sub8 [6, -1, 2] = true := by decide +kernel
theorem sub8_1695 : sub8 [6, -1, 3] = true := by decide +kernel
theorem sb8_52 : ∀ q ∈ blk8_52, sub8 q = true := by
  unfold blk8_52
  exact List.forall_mem_cons.2 ⟨sub8_1664, List.forall_mem_cons.2 ⟨sub8_1665, List.forall_mem_cons.2 ⟨sub8_1666, List.forall_mem_cons.2 ⟨sub8_1667, List.forall_mem_cons.2 ⟨sub8_1668, List.forall_mem_cons.2 ⟨sub8_1669, List.forall_mem_cons.2 ⟨sub8_1670, List.forall_mem_cons.2 ⟨sub8_1671, List.forall_mem_cons.2 ⟨sub8_1672, List.forall_mem_cons.2 ⟨sub8_1673, List.forall_mem_cons.2 ⟨sub8_1674, List.forall_mem_cons.2 ⟨sub8_1675, List.forall_mem_cons.2 ⟨sub8_1676, List.forall_mem_cons.2 ⟨sub8_1677, List.forall_mem_cons.2 ⟨sub8_1678, List.forall_mem_cons.2 ⟨sub8_1679, List.forall_mem_cons.2 ⟨sub8_1680, List.forall_mem_cons.2 ⟨sub8_1681, List.forall_mem_cons.2 ⟨sub8_1682, List.forall_mem_cons.2 ⟨sub8_1683, List.forall_mem_cons.2 ⟨sub8_1684, List.forall_mem_cons.2 ⟨sub8_1685, List.forall_mem_cons.2 ⟨sub8_1686, List.forall_mem_cons.2 ⟨sub8_1687, List.forall_mem_cons.2 ⟨sub8_1688, List.forall_mem_cons.2 ⟨sub8_1689, List.forall_mem_cons.2 ⟨sub8_1690, List.forall_mem_cons.2 ⟨sub8_1691, List.forall_mem_cons.2 ⟨sub8_1692, List.forall_mem_cons.2 ⟨sub8_1693, List.forall_mem_cons.2 ⟨sub8_1694, List.forall_mem_cons.2 ⟨sub8_1695, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub8_1696 : sub8 [6, -1, 4] = true := by decide +kernel
theorem sub8_1697 : sub8 [6, -1, 5] = true := by decide +kernel
theorem sub8_1698 : sub8 [6, 0] = true := by decide +kernel
theorem sub8_1699 : sub8 [6, 1] = true := by decide +kernel
theorem sub8_1700 : sub8 [6, 2] = true := by decide +kernel
theorem sub8_1701 : sub8 [7, -8] = true := by decide +kernel
theorem sub8_1702 : sub8 [7, -7] = true := by decide +kernel
theorem sub8_1703 : sub8 [7, -6] = true := by decide +kernel
theorem sub8_1704 : sub8 [7, -5] = true := by decide +kernel
theorem sub8_1705 : sub8 [7, -4] = true := by decide +kernel
theorem sub8_1706 : sub8 [7, -3] = true := by decide +kernel
theorem sub8_1707 : sub8 [7, -2] = true := by decide +kernel
theorem sub8_1708 : sub8 [7, -1] = true := by decide +kernel
theorem sub8_1709 : sub8 [7, 0] = true := by decide +kernel
theorem sub8_1710 : sub8 [7, 1] = true := by decide +kernel
theorem sub8_1711 : sub8 [8, -8] = true := by decide +kernel
theorem sub8_1712 : sub8 [8, -7] = true := by decide +kernel
theorem sub8_1713 : sub8 [8, -6] = true := by decide +kernel
theorem sub8_1714 : sub8 [8, -5] = true := by decide +kernel
theorem sub8_1715 : sub8 [8, -4] = true := by decide +kernel
theorem sub8_1716 : sub8 [8, -3] = true := by decide +kernel
theorem sub8_1717 : sub8 [8, -2] = true := by decide +kernel
theorem sub8_1718 : sub8 [8, -1] = true := by decide +kernel
theorem sub8_1719 : sub8 [8, 0] = true := by decide +kernel
theorem sub8_1720 : sub8 [9] = true := by decide +kernel
theorem sb8_53 : ∀ q ∈ blk8_53, sub8 q = true := by
  unfold blk8_53
  exact List.forall_mem_cons.2 ⟨sub8_1696, List.forall_mem_cons.2 ⟨sub8_1697, List.forall_mem_cons.2 ⟨sub8_1698, List.forall_mem_cons.2 ⟨sub8_1699, List.forall_mem_cons.2 ⟨sub8_1700, List.forall_mem_cons.2 ⟨sub8_1701, List.forall_mem_cons.2 ⟨sub8_1702, List.forall_mem_cons.2 ⟨sub8_1703, List.forall_mem_cons.2 ⟨sub8_1704, List.forall_mem_cons.2 ⟨sub8_1705, List.forall_mem_cons.2 ⟨sub8_1706, List.forall_mem_cons.2 ⟨sub8_1707, List.forall_mem_cons.2 ⟨sub8_1708, List.forall_mem_cons.2 ⟨sub8_1709, List.forall_mem_cons.2 ⟨sub8_1710, List.forall_mem_cons.2 ⟨sub8_1711, List.forall_mem_cons.2 ⟨sub8_1712, List.forall_mem_cons.2 ⟨sub8_1713, List.forall_mem_cons.2 ⟨sub8_1714, List.forall_mem_cons.2 ⟨sub8_1715, List.forall_mem_cons.2 ⟨sub8_1716, List.forall_mem_cons.2 ⟨sub8_1717, List.forall_mem_cons.2 ⟨sub8_1718, List.forall_mem_cons.2 ⟨sub8_1719, List.forall_mem_cons.2 ⟨sub8_1720, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_0 : sub9 [-4, -2] = true := by decide +kernel
theorem sub9_1 : sub9 [-4, -1] = true := by decide +kernel
theorem sub9_2 : sub9 [-4, 0] = true := by decide +kernel
theorem sub9_3 : sub9 [-4, 1] = true := by decide +kernel
theorem sub9_4 : sub9 [-4, 2] = true := by decide +kernel
theorem sub9_5 : sub9 [-4, 3] = true := by decide +kernel
theorem sub9_6 : sub9 [-4, 4] = true := by decide +kernel
theorem sub9_7 : sub9 [-3, -4] = true := by decide +kernel
theorem sub9_8 : sub9 [-3, -3] = true := by decide +kernel
theorem sub9_9 : sub9 [-3, -2] = true := by decide +kernel
theorem sub9_10 : sub9 [-3, -1] = true := by decide +kernel
theorem sub9_11 : sub9 [-3, 0, -7] = true := by decide +kernel
theorem sub9_12 : sub9 [-3, 0, -6] = true := by decide +kernel
theorem sub9_13 : sub9 [-3, 0, -5] = true := by decide +kernel
theorem sub9_14 : sub9 [-3, 0, -4] = true := by decide +kernel
theorem sub9_15 : sub9 [-3, 0, -3] = true := by decide +kernel
theorem sub9_16 : sub9 [-3, 0, -2] = true := by decide +kernel
theorem sub9_17 : sub9 [-3, 0, -1] = true := by decide +kernel
theorem sub9_18 : sub9 [-3, 0, 0] = true := by decide +kernel
theorem sub9_19 : sub9 [-3, 0, 1] = true := by decide +kernel
theorem sub9_20 : sub9 [-3, 0, 2] = true := by decide +kernel
theorem sub9_21 : sub9 [-3, 0, 3] = true := by decide +kernel
theorem sub9_22 : sub9 [-3, 0, 4] = true := by decide +kernel
theorem sub9_23 : sub9 [-3, 0, 5] = true := by decide +kernel
theorem sub9_24 : sub9 [-3, 1, -7] = true := by decide +kernel
theorem sub9_25 : sub9 [-3, 1, -6] = true := by decide +kernel
theorem sub9_26 : sub9 [-3, 1, -5] = true := by decide +kernel
theorem sub9_27 : sub9 [-3, 1, -4] = true := by decide +kernel
theorem sub9_28 : sub9 [-3, 1, -3] = true := by decide +kernel
theorem sub9_29 : sub9 [-3, 1, -2] = true := by decide +kernel
theorem sub9_30 : sub9 [-3, 1, -1] = true := by decide +kernel
theorem sub9_31 : sub9 [-3, 1, 0] = true := by decide +kernel
theorem sb9_0 : ∀ q ∈ blk9_0, sub9 q = true := by
  unfold blk9_0
  exact List.forall_mem_cons.2 ⟨sub9_0, List.forall_mem_cons.2 ⟨sub9_1, List.forall_mem_cons.2 ⟨sub9_2, List.forall_mem_cons.2 ⟨sub9_3, List.forall_mem_cons.2 ⟨sub9_4, List.forall_mem_cons.2 ⟨sub9_5, List.forall_mem_cons.2 ⟨sub9_6, List.forall_mem_cons.2 ⟨sub9_7, List.forall_mem_cons.2 ⟨sub9_8, List.forall_mem_cons.2 ⟨sub9_9, List.forall_mem_cons.2 ⟨sub9_10, List.forall_mem_cons.2 ⟨sub9_11, List.forall_mem_cons.2 ⟨sub9_12, List.forall_mem_cons.2 ⟨sub9_13, List.forall_mem_cons.2 ⟨sub9_14, List.forall_mem_cons.2 ⟨sub9_15, List.forall_mem_cons.2 ⟨sub9_16, List.forall_mem_cons.2 ⟨sub9_17, List.forall_mem_cons.2 ⟨sub9_18, List.forall_mem_cons.2 ⟨sub9_19, List.forall_mem_cons.2 ⟨sub9_20, List.forall_mem_cons.2 ⟨sub9_21, List.forall_mem_cons.2 ⟨sub9_22, List.forall_mem_cons.2 ⟨sub9_23, List.forall_mem_cons.2 ⟨sub9_24, List.forall_mem_cons.2 ⟨sub9_25, List.forall_mem_cons.2 ⟨sub9_26, List.forall_mem_cons.2 ⟨sub9_27, List.forall_mem_cons.2 ⟨sub9_28, List.forall_mem_cons.2 ⟨sub9_29, List.forall_mem_cons.2 ⟨sub9_30, List.forall_mem_cons.2 ⟨sub9_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C102
