import ReflectZphi.Data.Cert5.C080.Base

namespace ReflectZphi.Data.Cert5.C080
open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split ReflectZphi.FastLeaf

theorem sub9_1536 : sub9 [4, 3, -7] = true := by decide +kernel
theorem sub9_1537 : sub9 [4, 3, -6] = true := by decide +kernel
theorem sub9_1538 : sub9 [4, 3, -5] = true := by decide +kernel
theorem sub9_1539 : sub9 [4, 3, -4] = true := by decide +kernel
theorem sub9_1540 : sub9 [4, 3, -3] = true := by decide +kernel
theorem sub9_1541 : sub9 [4, 3, -2] = true := by decide +kernel
theorem sub9_1542 : sub9 [4, 3, -1] = true := by decide +kernel
theorem sub9_1543 : sub9 [4, 3, 0] = true := by decide +kernel
theorem sub9_1544 : sub9 [4, 3, 1] = true := by decide +kernel
theorem sub9_1545 : sub9 [4, 3, 2] = true := by decide +kernel
theorem sub9_1546 : sub9 [4, 3, 3] = true := by decide +kernel
theorem sub9_1547 : sub9 [4, 3, 4] = true := by decide +kernel
theorem sub9_1548 : sub9 [4, 3, 5] = true := by decide +kernel
theorem sub9_1549 : sub9 [4, 3, 6] = true := by decide +kernel
theorem sub9_1550 : sub9 [4, 4, -9] = true := by decide +kernel
theorem sub9_1551 : sub9 [4, 4, -8] = true := by decide +kernel
theorem sub9_1552 : sub9 [4, 4, -7] = true := by decide +kernel
theorem sub9_1553 : sub9 [4, 4, -6] = true := by decide +kernel
theorem sub9_1554 : sub9 [4, 4, -5] = true := by decide +kernel
theorem sub9_1555 : sub9 [4, 4, -4] = true := by decide +kernel
theorem sub9_1556 : sub9 [4, 4, -3] = true := by decide +kernel
theorem sub9_1557 : sub9 [4, 4, -2] = true := by decide +kernel
theorem sub9_1558 : sub9 [4, 4, -1] = true := by decide +kernel
theorem sub9_1559 : sub9 [4, 4, 0] = true := by decide +kernel
theorem sub9_1560 : sub9 [4, 4, 1] = true := by decide +kernel
theorem sub9_1561 : sub9 [4, 4, 2] = true := by decide +kernel
theorem sub9_1562 : sub9 [4, 4, 3] = true := by decide +kernel
theorem sub9_1563 : sub9 [4, 4, 4] = true := by decide +kernel
theorem sub9_1564 : sub9 [4, 4, 5] = true := by decide +kernel
theorem sub9_1565 : sub9 [4, 5] = true := by decide +kernel
theorem sub9_1566 : sub9 [4, 6] = true := by decide +kernel
theorem sub9_1567 : sub9 [5, -3] = true := by decide +kernel
theorem sb9_48 : ∀ q ∈ blk9_48, sub9 q = true := by
  unfold blk9_48
  exact List.forall_mem_cons.2 ⟨sub9_1536, List.forall_mem_cons.2 ⟨sub9_1537, List.forall_mem_cons.2 ⟨sub9_1538, List.forall_mem_cons.2 ⟨sub9_1539, List.forall_mem_cons.2 ⟨sub9_1540, List.forall_mem_cons.2 ⟨sub9_1541, List.forall_mem_cons.2 ⟨sub9_1542, List.forall_mem_cons.2 ⟨sub9_1543, List.forall_mem_cons.2 ⟨sub9_1544, List.forall_mem_cons.2 ⟨sub9_1545, List.forall_mem_cons.2 ⟨sub9_1546, List.forall_mem_cons.2 ⟨sub9_1547, List.forall_mem_cons.2 ⟨sub9_1548, List.forall_mem_cons.2 ⟨sub9_1549, List.forall_mem_cons.2 ⟨sub9_1550, List.forall_mem_cons.2 ⟨sub9_1551, List.forall_mem_cons.2 ⟨sub9_1552, List.forall_mem_cons.2 ⟨sub9_1553, List.forall_mem_cons.2 ⟨sub9_1554, List.forall_mem_cons.2 ⟨sub9_1555, List.forall_mem_cons.2 ⟨sub9_1556, List.forall_mem_cons.2 ⟨sub9_1557, List.forall_mem_cons.2 ⟨sub9_1558, List.forall_mem_cons.2 ⟨sub9_1559, List.forall_mem_cons.2 ⟨sub9_1560, List.forall_mem_cons.2 ⟨sub9_1561, List.forall_mem_cons.2 ⟨sub9_1562, List.forall_mem_cons.2 ⟨sub9_1563, List.forall_mem_cons.2 ⟨sub9_1564, List.forall_mem_cons.2 ⟨sub9_1565, List.forall_mem_cons.2 ⟨sub9_1566, List.forall_mem_cons.2 ⟨sub9_1567, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub9_1568 : sub9 [5, -2] = true := by decide +kernel
theorem sub9_1569 : sub9 [5, -1] = true := by decide +kernel
theorem sub9_1570 : sub9 [5, 0] = true := by decide +kernel
theorem sub9_1571 : sub9 [5, 1] = true := by decide +kernel
theorem sub9_1572 : sub9 [5, 2, -7] = true := by decide +kernel
theorem sub9_1573 : sub9 [5, 2, -6] = true := by decide +kernel
theorem sub9_1574 : sub9 [5, 2, -5] = true := by decide +kernel
theorem sub9_1575 : sub9 [5, 2, -4] = true := by decide +kernel
theorem sub9_1576 : sub9 [5, 2, -3] = true := by decide +kernel
theorem sub9_1577 : sub9 [5, 2, -2] = true := by decide +kernel
theorem sub9_1578 : sub9 [5, 2, -1] = true := by decide +kernel
theorem sub9_1579 : sub9 [5, 2, 0] = true := by decide +kernel
theorem sub9_1580 : sub9 [5, 2, 1] = true := by decide +kernel
theorem sub9_1581 : sub9 [5, 2, 2] = true := by decide +kernel
theorem sub9_1582 : sub9 [5, 2, 3] = true := by decide +kernel
theorem sub9_1583 : sub9 [5, 2, 4] = true := by decide +kernel
theorem sub9_1584 : sub9 [5, 2, 5] = true := by decide +kernel
theorem sub9_1585 : sub9 [5, 3] = true := by decide +kernel
theorem sub9_1586 : sub9 [5, 4] = true := by decide +kernel
theorem sub9_1587 : sub9 [5, 5] = true := by decide +kernel
theorem sub9_1588 : sub9 [5, 6] = true := by decide +kernel
theorem sub9_1589 : sub9 [6, -1] = true := by decide +kernel
theorem sub9_1590 : sub9 [6, 0] = true := by decide +kernel
theorem sub9_1591 : sub9 [6, 1] = true := by decide +kernel
theorem sub9_1592 : sub9 [6, 2] = true := by decide +kernel
theorem sub9_1593 : sub9 [6, 3] = true := by decide +kernel
theorem sub9_1594 : sub9 [6, 4] = true := by decide +kernel
theorem sb9_49 : ∀ q ∈ blk9_49, sub9 q = true := by
  unfold blk9_49
  exact List.forall_mem_cons.2 ⟨sub9_1568, List.forall_mem_cons.2 ⟨sub9_1569, List.forall_mem_cons.2 ⟨sub9_1570, List.forall_mem_cons.2 ⟨sub9_1571, List.forall_mem_cons.2 ⟨sub9_1572, List.forall_mem_cons.2 ⟨sub9_1573, List.forall_mem_cons.2 ⟨sub9_1574, List.forall_mem_cons.2 ⟨sub9_1575, List.forall_mem_cons.2 ⟨sub9_1576, List.forall_mem_cons.2 ⟨sub9_1577, List.forall_mem_cons.2 ⟨sub9_1578, List.forall_mem_cons.2 ⟨sub9_1579, List.forall_mem_cons.2 ⟨sub9_1580, List.forall_mem_cons.2 ⟨sub9_1581, List.forall_mem_cons.2 ⟨sub9_1582, List.forall_mem_cons.2 ⟨sub9_1583, List.forall_mem_cons.2 ⟨sub9_1584, List.forall_mem_cons.2 ⟨sub9_1585, List.forall_mem_cons.2 ⟨sub9_1586, List.forall_mem_cons.2 ⟨sub9_1587, List.forall_mem_cons.2 ⟨sub9_1588, List.forall_mem_cons.2 ⟨sub9_1589, List.forall_mem_cons.2 ⟨sub9_1590, List.forall_mem_cons.2 ⟨sub9_1591, List.forall_mem_cons.2 ⟨sub9_1592, List.forall_mem_cons.2 ⟨sub9_1593, List.forall_mem_cons.2 ⟨sub9_1594, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_0 : sub10 [-5] = true := by decide +kernel
theorem sub10_1 : sub10 [-4, -5] = true := by decide +kernel
theorem sub10_2 : sub10 [-4, -4] = true := by decide +kernel
theorem sub10_3 : sub10 [-4, -3, -7] = true := by decide +kernel
theorem sub10_4 : sub10 [-4, -3, -6] = true := by decide +kernel
theorem sub10_5 : sub10 [-4, -3, -5] = true := by decide +kernel
theorem sub10_6 : sub10 [-4, -3, -4] = true := by decide +kernel
theorem sub10_7 : sub10 [-4, -3, -3] = true := by decide +kernel
theorem sub10_8 : sub10 [-4, -3, -2] = true := by decide +kernel
theorem sub10_9 : sub10 [-4, -3, -1] = true := by decide +kernel
theorem sub10_10 : sub10 [-4, -3, 0] = true := by decide +kernel
theorem sub10_11 : sub10 [-4, -3, 1] = true := by decide +kernel
theorem sub10_12 : sub10 [-4, -3, 2] = true := by decide +kernel
theorem sub10_13 : sub10 [-4, -3, 3] = true := by decide +kernel
theorem sub10_14 : sub10 [-4, -3, 4] = true := by decide +kernel
theorem sub10_15 : sub10 [-4, -3, 5] = true := by decide +kernel
theorem sub10_16 : sub10 [-4, -3, 6] = true := by decide +kernel
theorem sub10_17 : sub10 [-4, -2, -8] = true := by decide +kernel
theorem sub10_18 : sub10 [-4, -2, -7] = true := by decide +kernel
theorem sub10_19 : sub10 [-4, -2, -6] = true := by decide +kernel
theorem sub10_20 : sub10 [-4, -2, -5] = true := by decide +kernel
theorem sub10_21 : sub10 [-4, -2, -4] = true := by decide +kernel
theorem sub10_22 : sub10 [-4, -2, -3] = true := by decide +kernel
theorem sub10_23 : sub10 [-4, -2, -2] = true := by decide +kernel
theorem sub10_24 : sub10 [-4, -2, -1] = true := by decide +kernel
theorem sub10_25 : sub10 [-4, -2, 0] = true := by decide +kernel
theorem sub10_26 : sub10 [-4, -2, 1] = true := by decide +kernel
theorem sub10_27 : sub10 [-4, -2, 2] = true := by decide +kernel
theorem sub10_28 : sub10 [-4, -2, 3] = true := by decide +kernel
theorem sub10_29 : sub10 [-4, -2, 4] = true := by decide +kernel
theorem sub10_30 : sub10 [-4, -2, 5] = true := by decide +kernel
theorem sub10_31 : sub10 [-4, -2, 6] = true := by decide +kernel
theorem sb10_0 : ∀ q ∈ blk10_0, sub10 q = true := by
  unfold blk10_0
  exact List.forall_mem_cons.2 ⟨sub10_0, List.forall_mem_cons.2 ⟨sub10_1, List.forall_mem_cons.2 ⟨sub10_2, List.forall_mem_cons.2 ⟨sub10_3, List.forall_mem_cons.2 ⟨sub10_4, List.forall_mem_cons.2 ⟨sub10_5, List.forall_mem_cons.2 ⟨sub10_6, List.forall_mem_cons.2 ⟨sub10_7, List.forall_mem_cons.2 ⟨sub10_8, List.forall_mem_cons.2 ⟨sub10_9, List.forall_mem_cons.2 ⟨sub10_10, List.forall_mem_cons.2 ⟨sub10_11, List.forall_mem_cons.2 ⟨sub10_12, List.forall_mem_cons.2 ⟨sub10_13, List.forall_mem_cons.2 ⟨sub10_14, List.forall_mem_cons.2 ⟨sub10_15, List.forall_mem_cons.2 ⟨sub10_16, List.forall_mem_cons.2 ⟨sub10_17, List.forall_mem_cons.2 ⟨sub10_18, List.forall_mem_cons.2 ⟨sub10_19, List.forall_mem_cons.2 ⟨sub10_20, List.forall_mem_cons.2 ⟨sub10_21, List.forall_mem_cons.2 ⟨sub10_22, List.forall_mem_cons.2 ⟨sub10_23, List.forall_mem_cons.2 ⟨sub10_24, List.forall_mem_cons.2 ⟨sub10_25, List.forall_mem_cons.2 ⟨sub10_26, List.forall_mem_cons.2 ⟨sub10_27, List.forall_mem_cons.2 ⟨sub10_28, List.forall_mem_cons.2 ⟨sub10_29, List.forall_mem_cons.2 ⟨sub10_30, List.forall_mem_cons.2 ⟨sub10_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_32 : sub10 [-4, -2, 7] = true := by decide +kernel
theorem sub10_33 : sub10 [-4, -1, -9] = true := by decide +kernel
theorem sub10_34 : sub10 [-4, -1, -8] = true := by decide +kernel
theorem sub10_35 : sub10 [-4, -1, -7] = true := by decide +kernel
theorem sub10_36 : sub10 [-4, -1, -6] = true := by decide +kernel
theorem sub10_37 : sub10 [-4, -1, -5] = true := by decide +kernel
theorem sub10_38 : sub10 [-4, -1, -4] = true := by decide +kernel
theorem sub10_39 : sub10 [-4, -1, -3] = true := by decide +kernel
theorem sub10_40 : sub10 [-4, -1, -2] = true := by decide +kernel
theorem sub10_41 : sub10 [-4, -1, -1] = true := by decide +kernel
theorem sub10_42 : sub10 [-4, -1, 0] = true := by decide +kernel
theorem sub10_43 : sub10 [-4, -1, 1] = true := by decide +kernel
theorem sub10_44 : sub10 [-4, -1, 2] = true := by decide +kernel
theorem sub10_45 : sub10 [-4, -1, 3] = true := by decide +kernel
theorem sub10_46 : sub10 [-4, -1, 4] = true := by decide +kernel
theorem sub10_47 : sub10 [-4, -1, 5] = true := by decide +kernel
theorem sub10_48 : sub10 [-4, -1, 6] = true := by decide +kernel
theorem sub10_49 : sub10 [-4, -1, 7] = true := by decide +kernel
theorem sub10_50 : sub10 [-4, 0, -9] = true := by decide +kernel
theorem sub10_51 : sub10 [-4, 0, -8] = true := by decide +kernel
theorem sub10_52 : sub10 [-4, 0, -7] = true := by decide +kernel
theorem sub10_53 : sub10 [-4, 0, -6] = true := by decide +kernel
theorem sub10_54 : sub10 [-4, 0, -5] = true := by decide +kernel
theorem sub10_55 : sub10 [-4, 0, -4] = true := by decide +kernel
theorem sub10_56 : sub10 [-4, 0, -3] = true := by decide +kernel
theorem sub10_57 : sub10 [-4, 0, -2] = true := by decide +kernel
theorem sub10_58 : sub10 [-4, 0, -1] = true := by decide +kernel
theorem sub10_59 : sub10 [-4, 0, 0] = true := by decide +kernel
theorem sub10_60 : sub10 [-4, 0, 1] = true := by decide +kernel
theorem sub10_61 : sub10 [-4, 0, 2] = true := by decide +kernel
theorem sub10_62 : sub10 [-4, 0, 3] = true := by decide +kernel
theorem sub10_63 : sub10 [-4, 0, 4] = true := by decide +kernel
theorem sb10_1 : ∀ q ∈ blk10_1, sub10 q = true := by
  unfold blk10_1
  exact List.forall_mem_cons.2 ⟨sub10_32, List.forall_mem_cons.2 ⟨sub10_33, List.forall_mem_cons.2 ⟨sub10_34, List.forall_mem_cons.2 ⟨sub10_35, List.forall_mem_cons.2 ⟨sub10_36, List.forall_mem_cons.2 ⟨sub10_37, List.forall_mem_cons.2 ⟨sub10_38, List.forall_mem_cons.2 ⟨sub10_39, List.forall_mem_cons.2 ⟨sub10_40, List.forall_mem_cons.2 ⟨sub10_41, List.forall_mem_cons.2 ⟨sub10_42, List.forall_mem_cons.2 ⟨sub10_43, List.forall_mem_cons.2 ⟨sub10_44, List.forall_mem_cons.2 ⟨sub10_45, List.forall_mem_cons.2 ⟨sub10_46, List.forall_mem_cons.2 ⟨sub10_47, List.forall_mem_cons.2 ⟨sub10_48, List.forall_mem_cons.2 ⟨sub10_49, List.forall_mem_cons.2 ⟨sub10_50, List.forall_mem_cons.2 ⟨sub10_51, List.forall_mem_cons.2 ⟨sub10_52, List.forall_mem_cons.2 ⟨sub10_53, List.forall_mem_cons.2 ⟨sub10_54, List.forall_mem_cons.2 ⟨sub10_55, List.forall_mem_cons.2 ⟨sub10_56, List.forall_mem_cons.2 ⟨sub10_57, List.forall_mem_cons.2 ⟨sub10_58, List.forall_mem_cons.2 ⟨sub10_59, List.forall_mem_cons.2 ⟨sub10_60, List.forall_mem_cons.2 ⟨sub10_61, List.forall_mem_cons.2 ⟨sub10_62, List.forall_mem_cons.2 ⟨sub10_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_64 : sub10 [-4, 0, 5] = true := by decide +kernel
theorem sub10_65 : sub10 [-4, 0, 6] = true := by decide +kernel
theorem sub10_66 : sub10 [-4, 1, -9] = true := by decide +kernel
theorem sub10_67 : sub10 [-4, 1, -8] = true := by decide +kernel
theorem sub10_68 : sub10 [-4, 1, -7] = true := by decide +kernel
theorem sub10_69 : sub10 [-4, 1, -6] = true := by decide +kernel
theorem sub10_70 : sub10 [-4, 1, -5] = true := by decide +kernel
theorem sub10_71 : sub10 [-4, 1, -4] = true := by decide +kernel
theorem sub10_72 : sub10 [-4, 1, -3] = true := by decide +kernel
theorem sub10_73 : sub10 [-4, 1, -2] = true := by decide +kernel
theorem sub10_74 : sub10 [-4, 1, -1] = true := by decide +kernel
theorem sub10_75 : sub10 [-4, 1, 0] = true := by decide +kernel
theorem sub10_76 : sub10 [-4, 1, 1] = true := by decide +kernel
theorem sub10_77 : sub10 [-4, 1, 2] = true := by decide +kernel
theorem sub10_78 : sub10 [-4, 1, 3] = true := by decide +kernel
theorem sub10_79 : sub10 [-4, 1, 4] = true := by decide +kernel
theorem sub10_80 : sub10 [-4, 1, 5] = true := by decide +kernel
theorem sub10_81 : sub10 [-4, 2] = true := by decide +kernel
theorem sub10_82 : sub10 [-3, -6] = true := by decide +kernel
theorem sub10_83 : sub10 [-3, -5] = true := by decide +kernel
theorem sub10_84 : sub10 [-3, -4, -7] = true := by decide +kernel
theorem sub10_85 : sub10 [-3, -4, -6] = true := by decide +kernel
theorem sub10_86 : sub10 [-3, -4, -5] = true := by decide +kernel
theorem sub10_87 : sub10 [-3, -4, -4] = true := by decide +kernel
theorem sub10_88 : sub10 [-3, -4, -3] = true := by decide +kernel
theorem sub10_89 : sub10 [-3, -4, -2] = true := by decide +kernel
theorem sub10_90 : sub10 [-3, -4, -1] = true := by decide +kernel
theorem sub10_91 : sub10 [-3, -4, 0] = true := by decide +kernel
theorem sub10_92 : sub10 [-3, -4, 1] = true := by decide +kernel
theorem sub10_93 : sub10 [-3, -4, 2] = true := by decide +kernel
theorem sub10_94 : sub10 [-3, -4, 3] = true := by decide +kernel
theorem sub10_95 : sub10 [-3, -4, 4] = true := by decide +kernel
theorem sb10_2 : ∀ q ∈ blk10_2, sub10 q = true := by
  unfold blk10_2
  exact List.forall_mem_cons.2 ⟨sub10_64, List.forall_mem_cons.2 ⟨sub10_65, List.forall_mem_cons.2 ⟨sub10_66, List.forall_mem_cons.2 ⟨sub10_67, List.forall_mem_cons.2 ⟨sub10_68, List.forall_mem_cons.2 ⟨sub10_69, List.forall_mem_cons.2 ⟨sub10_70, List.forall_mem_cons.2 ⟨sub10_71, List.forall_mem_cons.2 ⟨sub10_72, List.forall_mem_cons.2 ⟨sub10_73, List.forall_mem_cons.2 ⟨sub10_74, List.forall_mem_cons.2 ⟨sub10_75, List.forall_mem_cons.2 ⟨sub10_76, List.forall_mem_cons.2 ⟨sub10_77, List.forall_mem_cons.2 ⟨sub10_78, List.forall_mem_cons.2 ⟨sub10_79, List.forall_mem_cons.2 ⟨sub10_80, List.forall_mem_cons.2 ⟨sub10_81, List.forall_mem_cons.2 ⟨sub10_82, List.forall_mem_cons.2 ⟨sub10_83, List.forall_mem_cons.2 ⟨sub10_84, List.forall_mem_cons.2 ⟨sub10_85, List.forall_mem_cons.2 ⟨sub10_86, List.forall_mem_cons.2 ⟨sub10_87, List.forall_mem_cons.2 ⟨sub10_88, List.forall_mem_cons.2 ⟨sub10_89, List.forall_mem_cons.2 ⟨sub10_90, List.forall_mem_cons.2 ⟨sub10_91, List.forall_mem_cons.2 ⟨sub10_92, List.forall_mem_cons.2 ⟨sub10_93, List.forall_mem_cons.2 ⟨sub10_94, List.forall_mem_cons.2 ⟨sub10_95, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_96 : sub10 [-3, -4, 5] = true := by decide +kernel
theorem sub10_97 : sub10 [-3, -4, 6] = true := by decide +kernel
theorem sub10_98 : sub10 [-3, -4, 7] = true := by decide +kernel
theorem sub10_99 : sub10 [-3, -3, -9] = true := by decide +kernel
theorem sub10_100 : sub10 [-3, -3, -8] = true := by decide +kernel
theorem sub10_101 : sub10 [-3, -3, -7] = true := by decide +kernel
theorem sub10_102 : sub10 [-3, -3, -6] = true := by decide +kernel
theorem sub10_103 : sub10 [-3, -3, -5] = true := by decide +kernel
theorem sub10_104 : sub10 [-3, -3, -4] = true := by decide +kernel
theorem sub10_105 : sub10 [-3, -3, -3] = true := by decide +kernel
theorem sub10_106 : sub10 [-3, -3, -2] = true := by decide +kernel
theorem sub10_107 : sub10 [-3, -3, -1] = true := by decide +kernel
theorem sub10_108 : sub10 [-3, -3, 0] = true := by decide +kernel
theorem sub10_109 : sub10 [-3, -3, 1] = true := by decide +kernel
theorem sub10_110 : sub10 [-3, -3, 2] = true := by decide +kernel
theorem sub10_111 : sub10 [-3, -3, 3] = true := by decide +kernel
theorem sub10_112 : sub10 [-3, -3, 4] = true := by decide +kernel
theorem sub10_113 : sub10 [-3, -3, 5] = true := by decide +kernel
theorem sub10_114 : sub10 [-3, -3, 6] = true := by decide +kernel
theorem sub10_115 : sub10 [-3, -3, 7] = true := by decide +kernel
theorem sub10_116 : sub10 [-3, -3, 8] = true := by decide +kernel
theorem sub10_117 : sub10 [-3, -2, -10] = true := by decide +kernel
theorem sub10_118 : sub10 [-3, -2, -9] = true := by decide +kernel
theorem sub10_119 : sub10 [-3, -2, -8] = true := by decide +kernel
theorem sub10_120 : sub10 [-3, -2, -7] = true := by decide +kernel
theorem sub10_121 : sub10 [-3, -2, -6] = true := by decide +kernel
theorem sub10_122 : sub10 [-3, -2, -5] = true := by decide +kernel
theorem sub10_123 : sub10 [-3, -2, -4] = true := by decide +kernel
theorem sub10_124 : sub10 [-3, -2, -3] = true := by decide +kernel
theorem sub10_125 : sub10 [-3, -2, -2] = true := by decide +kernel
theorem sub10_126 : sub10 [-3, -2, -1] = true := by decide +kernel
theorem sub10_127 : sub10 [-3, -2, 0] = true := by decide +kernel
theorem sb10_3 : ∀ q ∈ blk10_3, sub10 q = true := by
  unfold blk10_3
  exact List.forall_mem_cons.2 ⟨sub10_96, List.forall_mem_cons.2 ⟨sub10_97, List.forall_mem_cons.2 ⟨sub10_98, List.forall_mem_cons.2 ⟨sub10_99, List.forall_mem_cons.2 ⟨sub10_100, List.forall_mem_cons.2 ⟨sub10_101, List.forall_mem_cons.2 ⟨sub10_102, List.forall_mem_cons.2 ⟨sub10_103, List.forall_mem_cons.2 ⟨sub10_104, List.forall_mem_cons.2 ⟨sub10_105, List.forall_mem_cons.2 ⟨sub10_106, List.forall_mem_cons.2 ⟨sub10_107, List.forall_mem_cons.2 ⟨sub10_108, List.forall_mem_cons.2 ⟨sub10_109, List.forall_mem_cons.2 ⟨sub10_110, List.forall_mem_cons.2 ⟨sub10_111, List.forall_mem_cons.2 ⟨sub10_112, List.forall_mem_cons.2 ⟨sub10_113, List.forall_mem_cons.2 ⟨sub10_114, List.forall_mem_cons.2 ⟨sub10_115, List.forall_mem_cons.2 ⟨sub10_116, List.forall_mem_cons.2 ⟨sub10_117, List.forall_mem_cons.2 ⟨sub10_118, List.forall_mem_cons.2 ⟨sub10_119, List.forall_mem_cons.2 ⟨sub10_120, List.forall_mem_cons.2 ⟨sub10_121, List.forall_mem_cons.2 ⟨sub10_122, List.forall_mem_cons.2 ⟨sub10_123, List.forall_mem_cons.2 ⟨sub10_124, List.forall_mem_cons.2 ⟨sub10_125, List.forall_mem_cons.2 ⟨sub10_126, List.forall_mem_cons.2 ⟨sub10_127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_128 : sub10 [-3, -2, 1] = true := by decide +kernel
theorem sub10_129 : sub10 [-3, -2, 2] = true := by decide +kernel
theorem sub10_130 : sub10 [-3, -2, 3] = true := by decide +kernel
theorem sub10_131 : sub10 [-3, -2, 4] = true := by decide +kernel
theorem sub10_132 : sub10 [-3, -2, 5] = true := by decide +kernel
theorem sub10_133 : sub10 [-3, -2, 6] = true := by decide +kernel
theorem sub10_134 : sub10 [-3, -2, 7] = true := by decide +kernel
theorem sub10_135 : sub10 [-3, -2, 8] = true := by decide +kernel
theorem sub10_136 : sub10 [-3, -2, 9] = true := by decide +kernel
theorem sub10_137 : sub10 [-3, -1, -11] = true := by decide +kernel
theorem sub10_138 : sub10 [-3, -1, -10] = true := by decide +kernel
theorem sub10_139 : sub10 [-3, -1, -9] = true := by decide +kernel
theorem sub10_140 : sub10 [-3, -1, -8] = true := by decide +kernel
theorem sub10_141 : sub10 [-3, -1, -7] = true := by decide +kernel
theorem sub10_142 : sub10 [-3, -1, -6] = true := by decide +kernel
theorem sub10_143 : sub10 [-3, -1, -5] = true := by decide +kernel
theorem sub10_144 : sub10 [-3, -1, -4] = true := by decide +kernel
theorem sub10_145 : sub10 [-3, -1, -3] = true := by decide +kernel
theorem sub10_146 : sub10 [-3, -1, -2] = true := by decide +kernel
theorem sub10_147 : sub10 [-3, -1, -1] = true := by decide +kernel
theorem sub10_148 : sub10 [-3, -1, 0] = true := by decide +kernel
theorem sub10_149 : sub10 [-3, -1, 1] = true := by decide +kernel
theorem sub10_150 : sub10 [-3, -1, 2] = true := by decide +kernel
theorem sub10_151 : sub10 [-3, -1, 3] = true := by decide +kernel
theorem sub10_152 : sub10 [-3, -1, 4] = true := by decide +kernel
theorem sub10_153 : sub10 [-3, -1, 5] = true := by decide +kernel
theorem sub10_154 : sub10 [-3, -1, 6] = true := by decide +kernel
theorem sub10_155 : sub10 [-3, -1, 7] = true := by decide +kernel
theorem sub10_156 : sub10 [-3, -1, 8] = true := by decide +kernel
theorem sub10_157 : sub10 [-3, -1, 9] = true := by decide +kernel
theorem sub10_158 : sub10 [-3, 0, -11] = true := by decide +kernel
theorem sub10_159 : sub10 [-3, 0, -10] = true := by decide +kernel
theorem sb10_4 : ∀ q ∈ blk10_4, sub10 q = true := by
  unfold blk10_4
  exact List.forall_mem_cons.2 ⟨sub10_128, List.forall_mem_cons.2 ⟨sub10_129, List.forall_mem_cons.2 ⟨sub10_130, List.forall_mem_cons.2 ⟨sub10_131, List.forall_mem_cons.2 ⟨sub10_132, List.forall_mem_cons.2 ⟨sub10_133, List.forall_mem_cons.2 ⟨sub10_134, List.forall_mem_cons.2 ⟨sub10_135, List.forall_mem_cons.2 ⟨sub10_136, List.forall_mem_cons.2 ⟨sub10_137, List.forall_mem_cons.2 ⟨sub10_138, List.forall_mem_cons.2 ⟨sub10_139, List.forall_mem_cons.2 ⟨sub10_140, List.forall_mem_cons.2 ⟨sub10_141, List.forall_mem_cons.2 ⟨sub10_142, List.forall_mem_cons.2 ⟨sub10_143, List.forall_mem_cons.2 ⟨sub10_144, List.forall_mem_cons.2 ⟨sub10_145, List.forall_mem_cons.2 ⟨sub10_146, List.forall_mem_cons.2 ⟨sub10_147, List.forall_mem_cons.2 ⟨sub10_148, List.forall_mem_cons.2 ⟨sub10_149, List.forall_mem_cons.2 ⟨sub10_150, List.forall_mem_cons.2 ⟨sub10_151, List.forall_mem_cons.2 ⟨sub10_152, List.forall_mem_cons.2 ⟨sub10_153, List.forall_mem_cons.2 ⟨sub10_154, List.forall_mem_cons.2 ⟨sub10_155, List.forall_mem_cons.2 ⟨sub10_156, List.forall_mem_cons.2 ⟨sub10_157, List.forall_mem_cons.2 ⟨sub10_158, List.forall_mem_cons.2 ⟨sub10_159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_160 : sub10 [-3, 0, -9] = true := by decide +kernel
theorem sub10_161 : sub10 [-3, 0, -8] = true := by decide +kernel
theorem sub10_162 : sub10 [-3, 0, -7] = true := by decide +kernel
theorem sub10_163 : sub10 [-3, 0, -6] = true := by decide +kernel
theorem sub10_164 : sub10 [-3, 0, -5] = true := by decide +kernel
theorem sub10_165 : sub10 [-3, 0, -4] = true := by decide +kernel
theorem sub10_166 : sub10 [-3, 0, -3] = true := by decide +kernel
theorem sub10_167 : sub10 [-3, 0, -2] = true := by decide +kernel
theorem sub10_168 : sub10 [-3, 0, -1] = true := by decide +kernel
theorem sub10_169 : sub10 [-3, 0, 0] = true := by decide +kernel
theorem sub10_170 : sub10 [-3, 0, 1] = true := by decide +kernel
theorem sub10_171 : sub10 [-3, 0, 2] = true := by decide +kernel
theorem sub10_172 : sub10 [-3, 0, 3] = true := by decide +kernel
theorem sub10_173 : sub10 [-3, 0, 4] = true := by decide +kernel
theorem sub10_174 : sub10 [-3, 0, 5] = true := by decide +kernel
theorem sub10_175 : sub10 [-3, 0, 6] = true := by decide +kernel
theorem sub10_176 : sub10 [-3, 0, 7] = true := by decide +kernel
theorem sub10_177 : sub10 [-3, 0, 8] = true := by decide +kernel
theorem sub10_178 : sub10 [-3, 0, 9] = true := by decide +kernel
theorem sub10_179 : sub10 [-3, 1, -11] = true := by decide +kernel
theorem sub10_180 : sub10 [-3, 1, -10] = true := by decide +kernel
theorem sub10_181 : sub10 [-3, 1, -9] = true := by decide +kernel
theorem sub10_182 : sub10 [-3, 1, -8] = true := by decide +kernel
theorem sub10_183 : sub10 [-3, 1, -7] = true := by decide +kernel
theorem sub10_184 : sub10 [-3, 1, -6] = true := by decide +kernel
theorem sub10_185 : sub10 [-3, 1, -5] = true := by decide +kernel
theorem sub10_186 : sub10 [-3, 1, -4] = true := by decide +kernel
theorem sub10_187 : sub10 [-3, 1, -3] = true := by decide +kernel
theorem sub10_188 : sub10 [-3, 1, -2] = true := by decide +kernel
theorem sub10_189 : sub10 [-3, 1, -1] = true := by decide +kernel
theorem sub10_190 : sub10 [-3, 1, 0] = true := by decide +kernel
theorem sub10_191 : sub10 [-3, 1, 1] = true := by decide +kernel
theorem sb10_5 : ∀ q ∈ blk10_5, sub10 q = true := by
  unfold blk10_5
  exact List.forall_mem_cons.2 ⟨sub10_160, List.forall_mem_cons.2 ⟨sub10_161, List.forall_mem_cons.2 ⟨sub10_162, List.forall_mem_cons.2 ⟨sub10_163, List.forall_mem_cons.2 ⟨sub10_164, List.forall_mem_cons.2 ⟨sub10_165, List.forall_mem_cons.2 ⟨sub10_166, List.forall_mem_cons.2 ⟨sub10_167, List.forall_mem_cons.2 ⟨sub10_168, List.forall_mem_cons.2 ⟨sub10_169, List.forall_mem_cons.2 ⟨sub10_170, List.forall_mem_cons.2 ⟨sub10_171, List.forall_mem_cons.2 ⟨sub10_172, List.forall_mem_cons.2 ⟨sub10_173, List.forall_mem_cons.2 ⟨sub10_174, List.forall_mem_cons.2 ⟨sub10_175, List.forall_mem_cons.2 ⟨sub10_176, List.forall_mem_cons.2 ⟨sub10_177, List.forall_mem_cons.2 ⟨sub10_178, List.forall_mem_cons.2 ⟨sub10_179, List.forall_mem_cons.2 ⟨sub10_180, List.forall_mem_cons.2 ⟨sub10_181, List.forall_mem_cons.2 ⟨sub10_182, List.forall_mem_cons.2 ⟨sub10_183, List.forall_mem_cons.2 ⟨sub10_184, List.forall_mem_cons.2 ⟨sub10_185, List.forall_mem_cons.2 ⟨sub10_186, List.forall_mem_cons.2 ⟨sub10_187, List.forall_mem_cons.2 ⟨sub10_188, List.forall_mem_cons.2 ⟨sub10_189, List.forall_mem_cons.2 ⟨sub10_190, List.forall_mem_cons.2 ⟨sub10_191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_192 : sub10 [-3, 1, 2] = true := by decide +kernel
theorem sub10_193 : sub10 [-3, 1, 3] = true := by decide +kernel
theorem sub10_194 : sub10 [-3, 1, 4] = true := by decide +kernel
theorem sub10_195 : sub10 [-3, 1, 5] = true := by decide +kernel
theorem sub10_196 : sub10 [-3, 1, 6] = true := by decide +kernel
theorem sub10_197 : sub10 [-3, 1, 7] = true := by decide +kernel
theorem sub10_198 : sub10 [-3, 1, 8] = true := by decide +kernel
theorem sub10_199 : sub10 [-3, 2, -10] = true := by decide +kernel
theorem sub10_200 : sub10 [-3, 2, -9] = true := by decide +kernel
theorem sub10_201 : sub10 [-3, 2, -8] = true := by decide +kernel
theorem sub10_202 : sub10 [-3, 2, -7] = true := by decide +kernel
theorem sub10_203 : sub10 [-3, 2, -6] = true := by decide +kernel
theorem sub10_204 : sub10 [-3, 2, -5] = true := by decide +kernel
theorem sub10_205 : sub10 [-3, 2, -4] = true := by decide +kernel
theorem sub10_206 : sub10 [-3, 2, -3] = true := by decide +kernel
theorem sub10_207 : sub10 [-3, 2, -2] = true := by decide +kernel
theorem sub10_208 : sub10 [-3, 2, -1] = true := by decide +kernel
theorem sub10_209 : sub10 [-3, 2, 0] = true := by decide +kernel
theorem sub10_210 : sub10 [-3, 2, 1] = true := by decide +kernel
theorem sub10_211 : sub10 [-3, 2, 2] = true := by decide +kernel
theorem sub10_212 : sub10 [-3, 2, 3] = true := by decide +kernel
theorem sub10_213 : sub10 [-3, 2, 4] = true := by decide +kernel
theorem sub10_214 : sub10 [-3, 2, 5] = true := by decide +kernel
theorem sub10_215 : sub10 [-3, 2, 6] = true := by decide +kernel
theorem sub10_216 : sub10 [-3, 3, -9] = true := by decide +kernel
theorem sub10_217 : sub10 [-3, 3, -8] = true := by decide +kernel
theorem sub10_218 : sub10 [-3, 3, -7] = true := by decide +kernel
theorem sub10_219 : sub10 [-3, 3, -6] = true := by decide +kernel
theorem sub10_220 : sub10 [-3, 3, -5] = true := by decide +kernel
theorem sub10_221 : sub10 [-3, 3, -4] = true := by decide +kernel
theorem sub10_222 : sub10 [-3, 3, -3] = true := by decide +kernel
theorem sub10_223 : sub10 [-3, 3, -2] = true := by decide +kernel
theorem sb10_6 : ∀ q ∈ blk10_6, sub10 q = true := by
  unfold blk10_6
  exact List.forall_mem_cons.2 ⟨sub10_192, List.forall_mem_cons.2 ⟨sub10_193, List.forall_mem_cons.2 ⟨sub10_194, List.forall_mem_cons.2 ⟨sub10_195, List.forall_mem_cons.2 ⟨sub10_196, List.forall_mem_cons.2 ⟨sub10_197, List.forall_mem_cons.2 ⟨sub10_198, List.forall_mem_cons.2 ⟨sub10_199, List.forall_mem_cons.2 ⟨sub10_200, List.forall_mem_cons.2 ⟨sub10_201, List.forall_mem_cons.2 ⟨sub10_202, List.forall_mem_cons.2 ⟨sub10_203, List.forall_mem_cons.2 ⟨sub10_204, List.forall_mem_cons.2 ⟨sub10_205, List.forall_mem_cons.2 ⟨sub10_206, List.forall_mem_cons.2 ⟨sub10_207, List.forall_mem_cons.2 ⟨sub10_208, List.forall_mem_cons.2 ⟨sub10_209, List.forall_mem_cons.2 ⟨sub10_210, List.forall_mem_cons.2 ⟨sub10_211, List.forall_mem_cons.2 ⟨sub10_212, List.forall_mem_cons.2 ⟨sub10_213, List.forall_mem_cons.2 ⟨sub10_214, List.forall_mem_cons.2 ⟨sub10_215, List.forall_mem_cons.2 ⟨sub10_216, List.forall_mem_cons.2 ⟨sub10_217, List.forall_mem_cons.2 ⟨sub10_218, List.forall_mem_cons.2 ⟨sub10_219, List.forall_mem_cons.2 ⟨sub10_220, List.forall_mem_cons.2 ⟨sub10_221, List.forall_mem_cons.2 ⟨sub10_222, List.forall_mem_cons.2 ⟨sub10_223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_224 : sub10 [-3, 3, -1] = true := by decide +kernel
theorem sub10_225 : sub10 [-3, 3, 0] = true := by decide +kernel
theorem sub10_226 : sub10 [-3, 3, 1] = true := by decide +kernel
theorem sub10_227 : sub10 [-3, 3, 2] = true := by decide +kernel
theorem sub10_228 : sub10 [-3, 3, 3] = true := by decide +kernel
theorem sub10_229 : sub10 [-3, 3, 4] = true := by decide +kernel
theorem sub10_230 : sub10 [-3, 4] = true := by decide +kernel
theorem sub10_231 : sub10 [-2, -6] = true := by decide +kernel
theorem sub10_232 : sub10 [-2, -5] = true := by decide +kernel
theorem sub10_233 : sub10 [-2, -4, -8] = true := by decide +kernel
theorem sub10_234 : sub10 [-2, -4, -7] = true := by decide +kernel
theorem sub10_235 : sub10 [-2, -4, -6] = true := by decide +kernel
theorem sub10_236 : sub10 [-2, -4, -5] = true := by decide +kernel
theorem sub10_237 : sub10 [-2, -4, -4] = true := by decide +kernel
theorem sub10_238 : sub10 [-2, -4, -3] = true := by decide +kernel
theorem sub10_239 : sub10 [-2, -4, -2] = true := by decide +kernel
theorem sub10_240 : sub10 [-2, -4, -1] = true := by decide +kernel
theorem sub10_241 : sub10 [-2, -4, 0] = true := by decide +kernel
theorem sub10_242 : sub10 [-2, -4, 1] = true := by decide +kernel
theorem sub10_243 : sub10 [-2, -4, 2] = true := by decide +kernel
theorem sub10_244 : sub10 [-2, -4, 3] = true := by decide +kernel
theorem sub10_245 : sub10 [-2, -4, 4] = true := by decide +kernel
theorem sub10_246 : sub10 [-2, -4, 5] = true := by decide +kernel
theorem sub10_247 : sub10 [-2, -4, 6] = true := by decide +kernel
theorem sub10_248 : sub10 [-2, -4, 7] = true := by decide +kernel
theorem sub10_249 : sub10 [-2, -4, 8] = true := by decide +kernel
theorem sub10_250 : sub10 [-2, -4, 9] = true := by decide +kernel
theorem sub10_251 : sub10 [-2, -3, -10] = true := by decide +kernel
theorem sub10_252 : sub10 [-2, -3, -9] = true := by decide +kernel
theorem sub10_253 : sub10 [-2, -3, -8] = true := by decide +kernel
theorem sub10_254 : sub10 [-2, -3, -7] = true := by decide +kernel
theorem sub10_255 : sub10 [-2, -3, -6] = true := by decide +kernel
theorem sb10_7 : ∀ q ∈ blk10_7, sub10 q = true := by
  unfold blk10_7
  exact List.forall_mem_cons.2 ⟨sub10_224, List.forall_mem_cons.2 ⟨sub10_225, List.forall_mem_cons.2 ⟨sub10_226, List.forall_mem_cons.2 ⟨sub10_227, List.forall_mem_cons.2 ⟨sub10_228, List.forall_mem_cons.2 ⟨sub10_229, List.forall_mem_cons.2 ⟨sub10_230, List.forall_mem_cons.2 ⟨sub10_231, List.forall_mem_cons.2 ⟨sub10_232, List.forall_mem_cons.2 ⟨sub10_233, List.forall_mem_cons.2 ⟨sub10_234, List.forall_mem_cons.2 ⟨sub10_235, List.forall_mem_cons.2 ⟨sub10_236, List.forall_mem_cons.2 ⟨sub10_237, List.forall_mem_cons.2 ⟨sub10_238, List.forall_mem_cons.2 ⟨sub10_239, List.forall_mem_cons.2 ⟨sub10_240, List.forall_mem_cons.2 ⟨sub10_241, List.forall_mem_cons.2 ⟨sub10_242, List.forall_mem_cons.2 ⟨sub10_243, List.forall_mem_cons.2 ⟨sub10_244, List.forall_mem_cons.2 ⟨sub10_245, List.forall_mem_cons.2 ⟨sub10_246, List.forall_mem_cons.2 ⟨sub10_247, List.forall_mem_cons.2 ⟨sub10_248, List.forall_mem_cons.2 ⟨sub10_249, List.forall_mem_cons.2 ⟨sub10_250, List.forall_mem_cons.2 ⟨sub10_251, List.forall_mem_cons.2 ⟨sub10_252, List.forall_mem_cons.2 ⟨sub10_253, List.forall_mem_cons.2 ⟨sub10_254, List.forall_mem_cons.2 ⟨sub10_255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_256 : sub10 [-2, -3, -5] = true := by decide +kernel
theorem sub10_257 : sub10 [-2, -3, -4] = true := by decide +kernel
theorem sub10_258 : sub10 [-2, -3, -3] = true := by decide +kernel
theorem sub10_259 : sub10 [-2, -3, -2] = true := by decide +kernel
theorem sub10_260 : sub10 [-2, -3, -1] = true := by decide +kernel
theorem sub10_261 : sub10 [-2, -3, 0] = true := by decide +kernel
theorem sub10_262 : sub10 [-2, -3, 1] = true := by decide +kernel
theorem sub10_263 : sub10 [-2, -3, 2] = true := by decide +kernel
theorem sub10_264 : sub10 [-2, -3, 3] = true := by decide +kernel
theorem sub10_265 : sub10 [-2, -3, 4] = true := by decide +kernel
theorem sub10_266 : sub10 [-2, -3, 5] = true := by decide +kernel
theorem sub10_267 : sub10 [-2, -3, 6] = true := by decide +kernel
theorem sub10_268 : sub10 [-2, -3, 7] = true := by decide +kernel
theorem sub10_269 : sub10 [-2, -3, 8] = true := by decide +kernel
theorem sub10_270 : sub10 [-2, -3, 9] = true := by decide +kernel
theorem sub10_271 : sub10 [-2, -3, 10] = true := by decide +kernel
theorem sub10_272 : sub10 [-2, -2, -11] = true := by decide +kernel
theorem sub10_273 : sub10 [-2, -2, -10] = true := by decide +kernel
theorem sub10_274 : sub10 [-2, -2, -9] = true := by decide +kernel
theorem sub10_275 : sub10 [-2, -2, -8] = true := by decide +kernel
theorem sub10_276 : sub10 [-2, -2, -7] = true := by decide +kernel
theorem sub10_277 : sub10 [-2, -2, -6] = true := by decide +kernel
theorem sub10_278 : sub10 [-2, -2, -5] = true := by decide +kernel
theorem sub10_279 : sub10 [-2, -2, -4] = true := by decide +kernel
theorem sub10_280 : sub10 [-2, -2, -3] = true := by decide +kernel
theorem sub10_281 : sub10 [-2, -2, -2] = true := by decide +kernel
theorem sub10_282 : sub10 [-2, -2, -1] = true := by decide +kernel
theorem sub10_283 : sub10 [-2, -2, 0] = true := by decide +kernel
theorem sub10_284 : sub10 [-2, -2, 1] = true := by decide +kernel
theorem sub10_285 : sub10 [-2, -2, 2] = true := by decide +kernel
theorem sub10_286 : sub10 [-2, -2, 3] = true := by decide +kernel
theorem sub10_287 : sub10 [-2, -2, 4] = true := by decide +kernel
theorem sb10_8 : ∀ q ∈ blk10_8, sub10 q = true := by
  unfold blk10_8
  exact List.forall_mem_cons.2 ⟨sub10_256, List.forall_mem_cons.2 ⟨sub10_257, List.forall_mem_cons.2 ⟨sub10_258, List.forall_mem_cons.2 ⟨sub10_259, List.forall_mem_cons.2 ⟨sub10_260, List.forall_mem_cons.2 ⟨sub10_261, List.forall_mem_cons.2 ⟨sub10_262, List.forall_mem_cons.2 ⟨sub10_263, List.forall_mem_cons.2 ⟨sub10_264, List.forall_mem_cons.2 ⟨sub10_265, List.forall_mem_cons.2 ⟨sub10_266, List.forall_mem_cons.2 ⟨sub10_267, List.forall_mem_cons.2 ⟨sub10_268, List.forall_mem_cons.2 ⟨sub10_269, List.forall_mem_cons.2 ⟨sub10_270, List.forall_mem_cons.2 ⟨sub10_271, List.forall_mem_cons.2 ⟨sub10_272, List.forall_mem_cons.2 ⟨sub10_273, List.forall_mem_cons.2 ⟨sub10_274, List.forall_mem_cons.2 ⟨sub10_275, List.forall_mem_cons.2 ⟨sub10_276, List.forall_mem_cons.2 ⟨sub10_277, List.forall_mem_cons.2 ⟨sub10_278, List.forall_mem_cons.2 ⟨sub10_279, List.forall_mem_cons.2 ⟨sub10_280, List.forall_mem_cons.2 ⟨sub10_281, List.forall_mem_cons.2 ⟨sub10_282, List.forall_mem_cons.2 ⟨sub10_283, List.forall_mem_cons.2 ⟨sub10_284, List.forall_mem_cons.2 ⟨sub10_285, List.forall_mem_cons.2 ⟨sub10_286, List.forall_mem_cons.2 ⟨sub10_287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_288 : sub10 [-2, -2, 5] = true := by decide +kernel
theorem sub10_289 : sub10 [-2, -2, 6] = true := by decide +kernel
theorem sub10_290 : sub10 [-2, -2, 7] = true := by decide +kernel
theorem sub10_291 : sub10 [-2, -2, 8] = true := by decide +kernel
theorem sub10_292 : sub10 [-2, -2, 9] = true := by decide +kernel
theorem sub10_293 : sub10 [-2, -2, 10] = true := by decide +kernel
theorem sub10_294 : sub10 [-2, -2, 11] = true := by decide +kernel
theorem sub10_295 : sub10 [-2, -1, -12] = true := by decide +kernel
theorem sub10_296 : sub10 [-2, -1, -11] = true := by decide +kernel
theorem sub10_297 : sub10 [-2, -1, -10] = true := by decide +kernel
theorem sub10_298 : sub10 [-2, -1, -9] = true := by decide +kernel
theorem sub10_299 : sub10 [-2, -1, -8] = true := by decide +kernel
theorem sub10_300 : sub10 [-2, -1, -7] = true := by decide +kernel
theorem sub10_301 : sub10 [-2, -1, -6] = true := by decide +kernel
theorem sub10_302 : sub10 [-2, -1, -5] = true := by decide +kernel
theorem sub10_303 : sub10 [-2, -1, -4] = true := by decide +kernel
theorem sub10_304 : sub10 [-2, -1, -3] = true := by decide +kernel
theorem sub10_305 : sub10 [-2, -1, -2] = true := by decide +kernel
theorem sub10_306 : sub10 [-2, -1, -1] = true := by decide +kernel
theorem sub10_307 : sub10 [-2, -1, 0] = true := by decide +kernel
theorem sub10_308 : sub10 [-2, -1, 1] = true := by decide +kernel
theorem sub10_309 : sub10 [-2, -1, 2] = true := by decide +kernel
theorem sub10_310 : sub10 [-2, -1, 3] = true := by decide +kernel
theorem sub10_311 : sub10 [-2, -1, 4] = true := by decide +kernel
theorem sub10_312 : sub10 [-2, -1, 5] = true := by decide +kernel
theorem sub10_313 : sub10 [-2, -1, 6] = true := by decide +kernel
theorem sub10_314 : sub10 [-2, -1, 7] = true := by decide +kernel
theorem sub10_315 : sub10 [-2, -1, 8] = true := by decide +kernel
theorem sub10_316 : sub10 [-2, -1, 9] = true := by decide +kernel
theorem sub10_317 : sub10 [-2, -1, 10] = true := by decide +kernel
theorem sub10_318 : sub10 [-2, -1, 11] = true := by decide +kernel
theorem sub10_319 : sub10 [-2, 0, -13] = true := by decide +kernel
theorem sb10_9 : ∀ q ∈ blk10_9, sub10 q = true := by
  unfold blk10_9
  exact List.forall_mem_cons.2 ⟨sub10_288, List.forall_mem_cons.2 ⟨sub10_289, List.forall_mem_cons.2 ⟨sub10_290, List.forall_mem_cons.2 ⟨sub10_291, List.forall_mem_cons.2 ⟨sub10_292, List.forall_mem_cons.2 ⟨sub10_293, List.forall_mem_cons.2 ⟨sub10_294, List.forall_mem_cons.2 ⟨sub10_295, List.forall_mem_cons.2 ⟨sub10_296, List.forall_mem_cons.2 ⟨sub10_297, List.forall_mem_cons.2 ⟨sub10_298, List.forall_mem_cons.2 ⟨sub10_299, List.forall_mem_cons.2 ⟨sub10_300, List.forall_mem_cons.2 ⟨sub10_301, List.forall_mem_cons.2 ⟨sub10_302, List.forall_mem_cons.2 ⟨sub10_303, List.forall_mem_cons.2 ⟨sub10_304, List.forall_mem_cons.2 ⟨sub10_305, List.forall_mem_cons.2 ⟨sub10_306, List.forall_mem_cons.2 ⟨sub10_307, List.forall_mem_cons.2 ⟨sub10_308, List.forall_mem_cons.2 ⟨sub10_309, List.forall_mem_cons.2 ⟨sub10_310, List.forall_mem_cons.2 ⟨sub10_311, List.forall_mem_cons.2 ⟨sub10_312, List.forall_mem_cons.2 ⟨sub10_313, List.forall_mem_cons.2 ⟨sub10_314, List.forall_mem_cons.2 ⟨sub10_315, List.forall_mem_cons.2 ⟨sub10_316, List.forall_mem_cons.2 ⟨sub10_317, List.forall_mem_cons.2 ⟨sub10_318, List.forall_mem_cons.2 ⟨sub10_319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem sub10_320 : sub10 [-2, 0, -12] = true := by decide +kernel
theorem sub10_321 : sub10 [-2, 0, -11] = true := by decide +kernel
theorem sub10_322 : sub10 [-2, 0, -10] = true := by decide +kernel
theorem sub10_323 : sub10 [-2, 0, -9] = true := by decide +kernel
theorem sub10_324 : sub10 [-2, 0, -8] = true := by decide +kernel
theorem sub10_325 : sub10 [-2, 0, -7] = true := by decide +kernel
theorem sub10_326 : sub10 [-2, 0, -6] = true := by decide +kernel
theorem sub10_327 : sub10 [-2, 0, -5] = true := by decide +kernel
theorem sub10_328 : sub10 [-2, 0, -4] = true := by decide +kernel
theorem sub10_329 : sub10 [-2, 0, -3] = true := by decide +kernel
theorem sub10_330 : sub10 [-2, 0, -2] = true := by decide +kernel
theorem sub10_331 : sub10 [-2, 0, -1] = true := by decide +kernel
theorem sub10_332 : sub10 [-2, 0, 0] = true := by decide +kernel
theorem sub10_333 : sub10 [-2, 0, 1] = true := by decide +kernel
theorem sub10_334 : sub10 [-2, 0, 2] = true := by decide +kernel
theorem sub10_335 : sub10 [-2, 0, 3] = true := by decide +kernel
theorem sub10_336 : sub10 [-2, 0, 4] = true := by decide +kernel
theorem sub10_337 : sub10 [-2, 0, 5] = true := by decide +kernel
theorem sub10_338 : sub10 [-2, 0, 6] = true := by decide +kernel
theorem sub10_339 : sub10 [-2, 0, 7] = true := by decide +kernel
theorem sub10_340 : sub10 [-2, 0, 8] = true := by decide +kernel
theorem sub10_341 : sub10 [-2, 0, 9] = true := by decide +kernel
theorem sub10_342 : sub10 [-2, 0, 10] = true := by decide +kernel
theorem sub10_343 : sub10 [-2, 1, -12] = true := by decide +kernel
theorem sub10_344 : sub10 [-2, 1, -11] = true := by decide +kernel
theorem sub10_345 : sub10 [-2, 1, -10] = true := by decide +kernel
theorem sub10_346 : sub10 [-2, 1, -9] = true := by decide +kernel
theorem sub10_347 : sub10 [-2, 1, -8] = true := by decide +kernel
theorem sub10_348 : sub10 [-2, 1, -7] = true := by decide +kernel
theorem sub10_349 : sub10 [-2, 1, -6] = true := by decide +kernel
theorem sub10_350 : sub10 [-2, 1, -5] = true := by decide +kernel
theorem sub10_351 : sub10 [-2, 1, -4] = true := by decide +kernel
theorem sb10_10 : ∀ q ∈ blk10_10, sub10 q = true := by
  unfold blk10_10
  exact List.forall_mem_cons.2 ⟨sub10_320, List.forall_mem_cons.2 ⟨sub10_321, List.forall_mem_cons.2 ⟨sub10_322, List.forall_mem_cons.2 ⟨sub10_323, List.forall_mem_cons.2 ⟨sub10_324, List.forall_mem_cons.2 ⟨sub10_325, List.forall_mem_cons.2 ⟨sub10_326, List.forall_mem_cons.2 ⟨sub10_327, List.forall_mem_cons.2 ⟨sub10_328, List.forall_mem_cons.2 ⟨sub10_329, List.forall_mem_cons.2 ⟨sub10_330, List.forall_mem_cons.2 ⟨sub10_331, List.forall_mem_cons.2 ⟨sub10_332, List.forall_mem_cons.2 ⟨sub10_333, List.forall_mem_cons.2 ⟨sub10_334, List.forall_mem_cons.2 ⟨sub10_335, List.forall_mem_cons.2 ⟨sub10_336, List.forall_mem_cons.2 ⟨sub10_337, List.forall_mem_cons.2 ⟨sub10_338, List.forall_mem_cons.2 ⟨sub10_339, List.forall_mem_cons.2 ⟨sub10_340, List.forall_mem_cons.2 ⟨sub10_341, List.forall_mem_cons.2 ⟨sub10_342, List.forall_mem_cons.2 ⟨sub10_343, List.forall_mem_cons.2 ⟨sub10_344, List.forall_mem_cons.2 ⟨sub10_345, List.forall_mem_cons.2 ⟨sub10_346, List.forall_mem_cons.2 ⟨sub10_347, List.forall_mem_cons.2 ⟨sub10_348, List.forall_mem_cons.2 ⟨sub10_349, List.forall_mem_cons.2 ⟨sub10_350, List.forall_mem_cons.2 ⟨sub10_351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C080
