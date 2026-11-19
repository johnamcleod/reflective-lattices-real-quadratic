import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_0_1472 : subd6_0 [4, 1, -6] = true := by decide +kernel
theorem subd6_0_1473 : subd6_0 [4, 1, -5] = true := by decide +kernel
theorem subd6_0_1474 : subd6_0 [4, 1, -4] = true := by decide +kernel
theorem subd6_0_1475 : subd6_0 [4, 1, -3] = true := by decide +kernel
theorem subd6_0_1476 : subd6_0 [4, 1, -2] = true := by decide +kernel
theorem subd6_0_1477 : subd6_0 [4, 1, -1] = true := by decide +kernel
theorem subd6_0_1478 : subd6_0 [4, 1, 0] = true := by decide +kernel
theorem subd6_0_1479 : subd6_0 [4, 1, 1] = true := by decide +kernel
theorem subd6_0_1480 : subd6_0 [4, 1, 2] = true := by decide +kernel
theorem subd6_0_1481 : subd6_0 [4, 1, 3] = true := by decide +kernel
theorem subd6_0_1482 : subd6_0 [4, 1, 4] = true := by decide +kernel
theorem subd6_0_1483 : subd6_0 [4, 1, 5] = true := by decide +kernel
theorem subd6_0_1484 : subd6_0 [4, 1, 6] = true := by decide +kernel
theorem subd6_0_1485 : subd6_0 [4, 2, -8] = true := by decide +kernel
theorem subd6_0_1486 : subd6_0 [4, 2, -7] = true := by decide +kernel
theorem subd6_0_1487 : subd6_0 [4, 2, -6] = true := by decide +kernel
theorem subd6_0_1488 : subd6_0 [4, 2, -5] = true := by decide +kernel
theorem subd6_0_1489 : subd6_0 [4, 2, -4] = true := by decide +kernel
theorem subd6_0_1490 : subd6_0 [4, 2, -3] = true := by decide +kernel
theorem subd6_0_1491 : subd6_0 [4, 2, -2] = true := by decide +kernel
theorem subd6_0_1492 : subd6_0 [4, 2, -1] = true := by decide +kernel
theorem subd6_0_1493 : subd6_0 [4, 2, 0] = true := by decide +kernel
theorem subd6_0_1494 : subd6_0 [4, 2, 1] = true := by decide +kernel
theorem subd6_0_1495 : subd6_0 [4, 2, 2] = true := by decide +kernel
theorem subd6_0_1496 : subd6_0 [4, 2, 3] = true := by decide +kernel
theorem subd6_0_1497 : subd6_0 [4, 2, 4] = true := by decide +kernel
theorem subd6_0_1498 : subd6_0 [4, 2, 5] = true := by decide +kernel
theorem subd6_0_1499 : subd6_0 [4, 2, 6] = true := by decide +kernel
theorem subd6_0_1500 : subd6_0 [4, 3, -8] = true := by decide +kernel
theorem subd6_0_1501 : subd6_0 [4, 3, -7] = true := by decide +kernel
theorem subd6_0_1502 : subd6_0 [4, 3, -6] = true := by decide +kernel
theorem subd6_0_1503 : subd6_0 [4, 3, -5] = true := by decide +kernel
theorem sbd6_0_46 : ∀ q ∈ blkd6_0_46, subd6_0 q = true := by
  unfold blkd6_0_46
  exact List.forall_mem_cons.2 ⟨subd6_0_1472, List.forall_mem_cons.2 ⟨subd6_0_1473, List.forall_mem_cons.2 ⟨subd6_0_1474, List.forall_mem_cons.2 ⟨subd6_0_1475, List.forall_mem_cons.2 ⟨subd6_0_1476, List.forall_mem_cons.2 ⟨subd6_0_1477, List.forall_mem_cons.2 ⟨subd6_0_1478, List.forall_mem_cons.2 ⟨subd6_0_1479, List.forall_mem_cons.2 ⟨subd6_0_1480, List.forall_mem_cons.2 ⟨subd6_0_1481, List.forall_mem_cons.2 ⟨subd6_0_1482, List.forall_mem_cons.2 ⟨subd6_0_1483, List.forall_mem_cons.2 ⟨subd6_0_1484, List.forall_mem_cons.2 ⟨subd6_0_1485, List.forall_mem_cons.2 ⟨subd6_0_1486, List.forall_mem_cons.2 ⟨subd6_0_1487, List.forall_mem_cons.2 ⟨subd6_0_1488, List.forall_mem_cons.2 ⟨subd6_0_1489, List.forall_mem_cons.2 ⟨subd6_0_1490, List.forall_mem_cons.2 ⟨subd6_0_1491, List.forall_mem_cons.2 ⟨subd6_0_1492, List.forall_mem_cons.2 ⟨subd6_0_1493, List.forall_mem_cons.2 ⟨subd6_0_1494, List.forall_mem_cons.2 ⟨subd6_0_1495, List.forall_mem_cons.2 ⟨subd6_0_1496, List.forall_mem_cons.2 ⟨subd6_0_1497, List.forall_mem_cons.2 ⟨subd6_0_1498, List.forall_mem_cons.2 ⟨subd6_0_1499, List.forall_mem_cons.2 ⟨subd6_0_1500, List.forall_mem_cons.2 ⟨subd6_0_1501, List.forall_mem_cons.2 ⟨subd6_0_1502, List.forall_mem_cons.2 ⟨subd6_0_1503, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1504 : subd6_0 [4, 3, -4] = true := by decide +kernel
theorem subd6_0_1505 : subd6_0 [4, 3, -3] = true := by decide +kernel
theorem subd6_0_1506 : subd6_0 [4, 3, -2] = true := by decide +kernel
theorem subd6_0_1507 : subd6_0 [4, 3, -1] = true := by decide +kernel
theorem subd6_0_1508 : subd6_0 [4, 3, 0] = true := by decide +kernel
theorem subd6_0_1509 : subd6_0 [4, 3, 1] = true := by decide +kernel
theorem subd6_0_1510 : subd6_0 [4, 3, 2] = true := by decide +kernel
theorem subd6_0_1511 : subd6_0 [4, 3, 3] = true := by decide +kernel
theorem subd6_0_1512 : subd6_0 [4, 3, 4] = true := by decide +kernel
theorem subd6_0_1513 : subd6_0 [4, 3, 5] = true := by decide +kernel
theorem subd6_0_1514 : subd6_0 [4, 4] = true := by decide +kernel
theorem subd6_0_1515 : subd6_0 [4, 5] = true := by decide +kernel
theorem subd6_0_1516 : subd6_0 [4, 6] = true := by decide +kernel
theorem subd6_0_1517 : subd6_0 [5, -7] = true := by decide +kernel
theorem subd6_0_1518 : subd6_0 [5, -6] = true := by decide +kernel
theorem subd6_0_1519 : subd6_0 [5, -5] = true := by decide +kernel
theorem subd6_0_1520 : subd6_0 [5, -4] = true := by decide +kernel
theorem subd6_0_1521 : subd6_0 [5, -3] = true := by decide +kernel
theorem subd6_0_1522 : subd6_0 [5, -2] = true := by decide +kernel
theorem subd6_0_1523 : subd6_0 [5, -1, -7] = true := by decide +kernel
theorem subd6_0_1524 : subd6_0 [5, -1, -6] = true := by decide +kernel
theorem subd6_0_1525 : subd6_0 [5, -1, -5] = true := by decide +kernel
theorem subd6_0_1526 : subd6_0 [5, -1, -4] = true := by decide +kernel
theorem subd6_0_1527 : subd6_0 [5, -1, -3] = true := by decide +kernel
theorem subd6_0_1528 : subd6_0 [5, -1, -2] = true := by decide +kernel
theorem subd6_0_1529 : subd6_0 [5, -1, -1] = true := by decide +kernel
theorem subd6_0_1530 : subd6_0 [5, -1, 0] = true := by decide +kernel
theorem subd6_0_1531 : subd6_0 [5, -1, 1] = true := by decide +kernel
theorem subd6_0_1532 : subd6_0 [5, -1, 2] = true := by decide +kernel
theorem subd6_0_1533 : subd6_0 [5, -1, 3] = true := by decide +kernel
theorem subd6_0_1534 : subd6_0 [5, -1, 4] = true := by decide +kernel
theorem subd6_0_1535 : subd6_0 [5, -1, 5] = true := by decide +kernel
theorem sbd6_0_47 : ∀ q ∈ blkd6_0_47, subd6_0 q = true := by
  unfold blkd6_0_47
  exact List.forall_mem_cons.2 ⟨subd6_0_1504, List.forall_mem_cons.2 ⟨subd6_0_1505, List.forall_mem_cons.2 ⟨subd6_0_1506, List.forall_mem_cons.2 ⟨subd6_0_1507, List.forall_mem_cons.2 ⟨subd6_0_1508, List.forall_mem_cons.2 ⟨subd6_0_1509, List.forall_mem_cons.2 ⟨subd6_0_1510, List.forall_mem_cons.2 ⟨subd6_0_1511, List.forall_mem_cons.2 ⟨subd6_0_1512, List.forall_mem_cons.2 ⟨subd6_0_1513, List.forall_mem_cons.2 ⟨subd6_0_1514, List.forall_mem_cons.2 ⟨subd6_0_1515, List.forall_mem_cons.2 ⟨subd6_0_1516, List.forall_mem_cons.2 ⟨subd6_0_1517, List.forall_mem_cons.2 ⟨subd6_0_1518, List.forall_mem_cons.2 ⟨subd6_0_1519, List.forall_mem_cons.2 ⟨subd6_0_1520, List.forall_mem_cons.2 ⟨subd6_0_1521, List.forall_mem_cons.2 ⟨subd6_0_1522, List.forall_mem_cons.2 ⟨subd6_0_1523, List.forall_mem_cons.2 ⟨subd6_0_1524, List.forall_mem_cons.2 ⟨subd6_0_1525, List.forall_mem_cons.2 ⟨subd6_0_1526, List.forall_mem_cons.2 ⟨subd6_0_1527, List.forall_mem_cons.2 ⟨subd6_0_1528, List.forall_mem_cons.2 ⟨subd6_0_1529, List.forall_mem_cons.2 ⟨subd6_0_1530, List.forall_mem_cons.2 ⟨subd6_0_1531, List.forall_mem_cons.2 ⟨subd6_0_1532, List.forall_mem_cons.2 ⟨subd6_0_1533, List.forall_mem_cons.2 ⟨subd6_0_1534, List.forall_mem_cons.2 ⟨subd6_0_1535, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1536 : subd6_0 [5, -1, 6] = true := by decide +kernel
theorem subd6_0_1537 : subd6_0 [5, 0, -7] = true := by decide +kernel
theorem subd6_0_1538 : subd6_0 [5, 0, -6] = true := by decide +kernel
theorem subd6_0_1539 : subd6_0 [5, 0, -5] = true := by decide +kernel
theorem subd6_0_1540 : subd6_0 [5, 0, -4] = true := by decide +kernel
theorem subd6_0_1541 : subd6_0 [5, 0, -3] = true := by decide +kernel
theorem subd6_0_1542 : subd6_0 [5, 0, -2] = true := by decide +kernel
theorem subd6_0_1543 : subd6_0 [5, 0, -1] = true := by decide +kernel
theorem subd6_0_1544 : subd6_0 [5, 0, 0] = true := by decide +kernel
theorem subd6_0_1545 : subd6_0 [5, 0, 1] = true := by decide +kernel
theorem subd6_0_1546 : subd6_0 [5, 0, 2] = true := by decide +kernel
theorem subd6_0_1547 : subd6_0 [5, 0, 3] = true := by decide +kernel
theorem subd6_0_1548 : subd6_0 [5, 0, 4] = true := by decide +kernel
theorem subd6_0_1549 : subd6_0 [5, 0, 5] = true := by decide +kernel
theorem subd6_0_1550 : subd6_0 [5, 0, 6] = true := by decide +kernel
theorem subd6_0_1551 : subd6_0 [5, 1] = true := by decide +kernel
theorem subd6_0_1552 : subd6_0 [5, 2] = true := by decide +kernel
theorem subd6_0_1553 : subd6_0 [5, 3] = true := by decide +kernel
theorem subd6_0_1554 : subd6_0 [5, 4] = true := by decide +kernel
theorem subd6_0_1555 : subd6_0 [5, 5] = true := by decide +kernel
theorem subd6_0_1556 : subd6_0 [6, -6] = true := by decide +kernel
theorem subd6_0_1557 : subd6_0 [6, -5] = true := by decide +kernel
theorem subd6_0_1558 : subd6_0 [6, -4] = true := by decide +kernel
theorem subd6_0_1559 : subd6_0 [6, -3] = true := by decide +kernel
theorem subd6_0_1560 : subd6_0 [6, -2] = true := by decide +kernel
theorem subd6_0_1561 : subd6_0 [6, -1] = true := by decide +kernel
theorem subd6_0_1562 : subd6_0 [6, 0] = true := by decide +kernel
theorem subd6_0_1563 : subd6_0 [6, 1] = true := by decide +kernel
theorem subd6_0_1564 : subd6_0 [6, 2] = true := by decide +kernel
theorem subd6_0_1565 : subd6_0 [6, 3] = true := by decide +kernel
theorem subd6_0_1566 : subd6_0 [6, 4] = true := by decide +kernel
theorem subd6_0_1567 : subd6_0 [7, -5] = true := by decide +kernel
theorem sbd6_0_48 : ∀ q ∈ blkd6_0_48, subd6_0 q = true := by
  unfold blkd6_0_48
  exact List.forall_mem_cons.2 ⟨subd6_0_1536, List.forall_mem_cons.2 ⟨subd6_0_1537, List.forall_mem_cons.2 ⟨subd6_0_1538, List.forall_mem_cons.2 ⟨subd6_0_1539, List.forall_mem_cons.2 ⟨subd6_0_1540, List.forall_mem_cons.2 ⟨subd6_0_1541, List.forall_mem_cons.2 ⟨subd6_0_1542, List.forall_mem_cons.2 ⟨subd6_0_1543, List.forall_mem_cons.2 ⟨subd6_0_1544, List.forall_mem_cons.2 ⟨subd6_0_1545, List.forall_mem_cons.2 ⟨subd6_0_1546, List.forall_mem_cons.2 ⟨subd6_0_1547, List.forall_mem_cons.2 ⟨subd6_0_1548, List.forall_mem_cons.2 ⟨subd6_0_1549, List.forall_mem_cons.2 ⟨subd6_0_1550, List.forall_mem_cons.2 ⟨subd6_0_1551, List.forall_mem_cons.2 ⟨subd6_0_1552, List.forall_mem_cons.2 ⟨subd6_0_1553, List.forall_mem_cons.2 ⟨subd6_0_1554, List.forall_mem_cons.2 ⟨subd6_0_1555, List.forall_mem_cons.2 ⟨subd6_0_1556, List.forall_mem_cons.2 ⟨subd6_0_1557, List.forall_mem_cons.2 ⟨subd6_0_1558, List.forall_mem_cons.2 ⟨subd6_0_1559, List.forall_mem_cons.2 ⟨subd6_0_1560, List.forall_mem_cons.2 ⟨subd6_0_1561, List.forall_mem_cons.2 ⟨subd6_0_1562, List.forall_mem_cons.2 ⟨subd6_0_1563, List.forall_mem_cons.2 ⟨subd6_0_1564, List.forall_mem_cons.2 ⟨subd6_0_1565, List.forall_mem_cons.2 ⟨subd6_0_1566, List.forall_mem_cons.2 ⟨subd6_0_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_0_1568 : subd6_0 [7, -4] = true := by decide +kernel
theorem subd6_0_1569 : subd6_0 [7, -3] = true := by decide +kernel
theorem subd6_0_1570 : subd6_0 [7, -2] = true := by decide +kernel
theorem subd6_0_1571 : subd6_0 [7, -1] = true := by decide +kernel
theorem subd6_0_1572 : subd6_0 [7, 0] = true := by decide +kernel
theorem subd6_0_1573 : subd6_0 [7, 1] = true := by decide +kernel
theorem subd6_0_1574 : subd6_0 [7, 2] = true := by decide +kernel
theorem sbd6_0_49 : ∀ q ∈ blkd6_0_49, subd6_0 q = true := by
  unfold blkd6_0_49
  exact List.forall_mem_cons.2 ⟨subd6_0_1568, List.forall_mem_cons.2 ⟨subd6_0_1569, List.forall_mem_cons.2 ⟨subd6_0_1570, List.forall_mem_cons.2 ⟨subd6_0_1571, List.forall_mem_cons.2 ⟨subd6_0_1572, List.forall_mem_cons.2 ⟨subd6_0_1573, List.forall_mem_cons.2 ⟨subd6_0_1574, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd6_1 : ldCheck G d6_1.U d6_1.ms ldd6_1 = true := by decide +kernel
theorem pre_okd6_1 : subPre G cell6 d6_1 = true := by decide +kernel
theorem subd6_1_0 : subd6_1 [-1] = true := by decide +kernel
theorem subd6_1_1 : subd6_1 [0] = true := by decide +kernel
theorem subd6_1_2 : subd6_1 [1] = true := by decide +kernel
theorem sbd6_1_0 : ∀ q ∈ blkd6_1_0, subd6_1 q = true := by
  unfold blkd6_1_0
  exact List.forall_mem_cons.2 ⟨subd6_1_0, List.forall_mem_cons.2 ⟨subd6_1_1, List.forall_mem_cons.2 ⟨subd6_1_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd6_2 : ldCheck G d6_2.U d6_2.ms ldd6_2 = true := by decide +kernel
theorem pre_okd6_2 : subPre G cell6 d6_2 = true := by decide +kernel
theorem subd6_2_0 : subd6_2 [] = true := by decide +kernel
theorem sbd6_2_0 : ∀ q ∈ blkd6_2_0, subd6_2 q = true := by
  unfold blkd6_2_0
  exact List.forall_mem_cons.2 ⟨subd6_2_0, List.forall_mem_nil _⟩
theorem ld_okd6_3 : ldCheck G d6_3.U d6_3.ms ldd6_3 = true := by decide +kernel
theorem pre_okd6_3 : subPre G cell6 d6_3 = true := by decide +kernel
theorem subd6_3_0 : subd6_3 [] = true := by decide +kernel
theorem sbd6_3_0 : ∀ q ∈ blkd6_3_0, subd6_3 q = true := by
  unfold blkd6_3_0
  exact List.forall_mem_cons.2 ⟨subd6_3_0, List.forall_mem_nil _⟩
theorem ld_okd6_4 : ldCheck G d6_4.U d6_4.ms ldd6_4 = true := by decide +kernel
theorem pre_okd6_4 : subPre G cell6 d6_4 = true := by decide +kernel
theorem subd6_4_0 : subd6_4 [-1] = true := by decide +kernel
theorem subd6_4_1 : subd6_4 [0, -2] = true := by decide +kernel
theorem subd6_4_2 : subd6_4 [0, -1] = true := by decide +kernel
theorem subd6_4_3 : subd6_4 [0, 0] = true := by decide +kernel
theorem subd6_4_4 : subd6_4 [0, 1] = true := by decide +kernel
theorem subd6_4_5 : subd6_4 [1] = true := by decide +kernel
theorem sbd6_4_0 : ∀ q ∈ blkd6_4_0, subd6_4 q = true := by
  unfold blkd6_4_0
  exact List.forall_mem_cons.2 ⟨subd6_4_0, List.forall_mem_cons.2 ⟨subd6_4_1, List.forall_mem_cons.2 ⟨subd6_4_2, List.forall_mem_cons.2 ⟨subd6_4_3, List.forall_mem_cons.2 ⟨subd6_4_4, List.forall_mem_cons.2 ⟨subd6_4_5, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C093
