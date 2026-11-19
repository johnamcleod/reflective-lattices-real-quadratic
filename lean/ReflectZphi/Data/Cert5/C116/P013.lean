import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd6_1_3136 : subd6_1 [6, 2, -5] = true := by decide +kernel
theorem subd6_1_3137 : subd6_1 [6, 2, -4] = true := by decide +kernel
theorem subd6_1_3138 : subd6_1 [6, 2, -3] = true := by decide +kernel
theorem subd6_1_3139 : subd6_1 [6, 2, -2] = true := by decide +kernel
theorem subd6_1_3140 : subd6_1 [6, 2, -1] = true := by decide +kernel
theorem subd6_1_3141 : subd6_1 [6, 2, 0] = true := by decide +kernel
theorem subd6_1_3142 : subd6_1 [6, 2, 1] = true := by decide +kernel
theorem subd6_1_3143 : subd6_1 [6, 2, 2] = true := by decide +kernel
theorem subd6_1_3144 : subd6_1 [6, 2, 3] = true := by decide +kernel
theorem subd6_1_3145 : subd6_1 [6, 2, 4] = true := by decide +kernel
theorem subd6_1_3146 : subd6_1 [6, 3] = true := by decide +kernel
theorem subd6_1_3147 : subd6_1 [6, 4] = true := by decide +kernel
theorem subd6_1_3148 : subd6_1 [6, 5] = true := by decide +kernel
theorem subd6_1_3149 : subd6_1 [7, -9] = true := by decide +kernel
theorem subd6_1_3150 : subd6_1 [7, -8] = true := by decide +kernel
theorem subd6_1_3151 : subd6_1 [7, -7] = true := by decide +kernel
theorem subd6_1_3152 : subd6_1 [7, -6] = true := by decide +kernel
theorem subd6_1_3153 : subd6_1 [7, -5] = true := by decide +kernel
theorem subd6_1_3154 : subd6_1 [7, -4] = true := by decide +kernel
theorem subd6_1_3155 : subd6_1 [7, -3] = true := by decide +kernel
theorem subd6_1_3156 : subd6_1 [7, -2] = true := by decide +kernel
theorem subd6_1_3157 : subd6_1 [7, -1] = true := by decide +kernel
theorem subd6_1_3158 : subd6_1 [7, 0] = true := by decide +kernel
theorem subd6_1_3159 : subd6_1 [7, 1] = true := by decide +kernel
theorem subd6_1_3160 : subd6_1 [7, 2] = true := by decide +kernel
theorem subd6_1_3161 : subd6_1 [7, 3] = true := by decide +kernel
theorem subd6_1_3162 : subd6_1 [7, 4] = true := by decide +kernel
theorem subd6_1_3163 : subd6_1 [8, -8] = true := by decide +kernel
theorem subd6_1_3164 : subd6_1 [8, -7] = true := by decide +kernel
theorem subd6_1_3165 : subd6_1 [8, -6] = true := by decide +kernel
theorem subd6_1_3166 : subd6_1 [8, -5] = true := by decide +kernel
theorem subd6_1_3167 : subd6_1 [8, -4] = true := by decide +kernel
theorem sbd6_1_98 : ∀ q ∈ blkd6_1_98, subd6_1 q = true := by
  unfold blkd6_1_98
  exact List.forall_mem_cons.2 ⟨subd6_1_3136, List.forall_mem_cons.2 ⟨subd6_1_3137, List.forall_mem_cons.2 ⟨subd6_1_3138, List.forall_mem_cons.2 ⟨subd6_1_3139, List.forall_mem_cons.2 ⟨subd6_1_3140, List.forall_mem_cons.2 ⟨subd6_1_3141, List.forall_mem_cons.2 ⟨subd6_1_3142, List.forall_mem_cons.2 ⟨subd6_1_3143, List.forall_mem_cons.2 ⟨subd6_1_3144, List.forall_mem_cons.2 ⟨subd6_1_3145, List.forall_mem_cons.2 ⟨subd6_1_3146, List.forall_mem_cons.2 ⟨subd6_1_3147, List.forall_mem_cons.2 ⟨subd6_1_3148, List.forall_mem_cons.2 ⟨subd6_1_3149, List.forall_mem_cons.2 ⟨subd6_1_3150, List.forall_mem_cons.2 ⟨subd6_1_3151, List.forall_mem_cons.2 ⟨subd6_1_3152, List.forall_mem_cons.2 ⟨subd6_1_3153, List.forall_mem_cons.2 ⟨subd6_1_3154, List.forall_mem_cons.2 ⟨subd6_1_3155, List.forall_mem_cons.2 ⟨subd6_1_3156, List.forall_mem_cons.2 ⟨subd6_1_3157, List.forall_mem_cons.2 ⟨subd6_1_3158, List.forall_mem_cons.2 ⟨subd6_1_3159, List.forall_mem_cons.2 ⟨subd6_1_3160, List.forall_mem_cons.2 ⟨subd6_1_3161, List.forall_mem_cons.2 ⟨subd6_1_3162, List.forall_mem_cons.2 ⟨subd6_1_3163, List.forall_mem_cons.2 ⟨subd6_1_3164, List.forall_mem_cons.2 ⟨subd6_1_3165, List.forall_mem_cons.2 ⟨subd6_1_3166, List.forall_mem_cons.2 ⟨subd6_1_3167, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd6_1_3168 : subd6_1 [8, -3] = true := by decide +kernel
theorem subd6_1_3169 : subd6_1 [8, -2] = true := by decide +kernel
theorem subd6_1_3170 : subd6_1 [8, -1] = true := by decide +kernel
theorem subd6_1_3171 : subd6_1 [8, 0] = true := by decide +kernel
theorem subd6_1_3172 : subd6_1 [8, 1] = true := by decide +kernel
theorem subd6_1_3173 : subd6_1 [8, 2] = true := by decide +kernel
theorem subd6_1_3174 : subd6_1 [9] = true := by decide +kernel
theorem sbd6_1_99 : ∀ q ∈ blkd6_1_99, subd6_1 q = true := by
  unfold blkd6_1_99
  exact List.forall_mem_cons.2 ⟨subd6_1_3168, List.forall_mem_cons.2 ⟨subd6_1_3169, List.forall_mem_cons.2 ⟨subd6_1_3170, List.forall_mem_cons.2 ⟨subd6_1_3171, List.forall_mem_cons.2 ⟨subd6_1_3172, List.forall_mem_cons.2 ⟨subd6_1_3173, List.forall_mem_cons.2 ⟨subd6_1_3174, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd7_0 : ldCheck G d7_0.U d7_0.ms ldd7_0 = true := by decide +kernel
theorem pre_okd7_0 : subPre G cell7 d7_0 = true := by decide +kernel
theorem subd7_0_0 : subd7_0 [-4] = true := by decide +kernel
theorem subd7_0_1 : subd7_0 [-3, -3] = true := by decide +kernel
theorem subd7_0_2 : subd7_0 [-3, -2] = true := by decide +kernel
theorem subd7_0_3 : subd7_0 [-3, -1] = true := by decide +kernel
theorem subd7_0_4 : subd7_0 [-3, 0] = true := by decide +kernel
theorem subd7_0_5 : subd7_0 [-3, 1] = true := by decide +kernel
theorem subd7_0_6 : subd7_0 [-3, 2] = true := by decide +kernel
theorem subd7_0_7 : subd7_0 [-3, 3] = true := by decide +kernel
theorem subd7_0_8 : subd7_0 [-3, 4] = true := by decide +kernel
theorem subd7_0_9 : subd7_0 [-2, -4] = true := by decide +kernel
theorem subd7_0_10 : subd7_0 [-2, -3] = true := by decide +kernel
theorem subd7_0_11 : subd7_0 [-2, -2] = true := by decide +kernel
theorem subd7_0_12 : subd7_0 [-2, -1] = true := by decide +kernel
theorem subd7_0_13 : subd7_0 [-2, 0] = true := by decide +kernel
theorem subd7_0_14 : subd7_0 [-2, 1] = true := by decide +kernel
theorem subd7_0_15 : subd7_0 [-2, 2] = true := by decide +kernel
theorem subd7_0_16 : subd7_0 [-2, 3] = true := by decide +kernel
theorem subd7_0_17 : subd7_0 [-2, 4] = true := by decide +kernel
theorem subd7_0_18 : subd7_0 [-2, 5] = true := by decide +kernel
theorem subd7_0_19 : subd7_0 [-1, -5] = true := by decide +kernel
theorem subd7_0_20 : subd7_0 [-1, -4] = true := by decide +kernel
theorem subd7_0_21 : subd7_0 [-1, -3] = true := by decide +kernel
theorem subd7_0_22 : subd7_0 [-1, -2] = true := by decide +kernel
theorem subd7_0_23 : subd7_0 [-1, -1] = true := by decide +kernel
theorem subd7_0_24 : subd7_0 [-1, 0] = true := by decide +kernel
theorem subd7_0_25 : subd7_0 [-1, 1] = true := by decide +kernel
theorem subd7_0_26 : subd7_0 [-1, 2] = true := by decide +kernel
theorem subd7_0_27 : subd7_0 [-1, 3] = true := by decide +kernel
theorem subd7_0_28 : subd7_0 [-1, 4] = true := by decide +kernel
theorem subd7_0_29 : subd7_0 [-1, 5] = true := by decide +kernel
theorem subd7_0_30 : subd7_0 [0, -5] = true := by decide +kernel
theorem subd7_0_31 : subd7_0 [0, -4] = true := by decide +kernel
theorem sbd7_0_0 : ∀ q ∈ blkd7_0_0, subd7_0 q = true := by
  unfold blkd7_0_0
  exact List.forall_mem_cons.2 ⟨subd7_0_0, List.forall_mem_cons.2 ⟨subd7_0_1, List.forall_mem_cons.2 ⟨subd7_0_2, List.forall_mem_cons.2 ⟨subd7_0_3, List.forall_mem_cons.2 ⟨subd7_0_4, List.forall_mem_cons.2 ⟨subd7_0_5, List.forall_mem_cons.2 ⟨subd7_0_6, List.forall_mem_cons.2 ⟨subd7_0_7, List.forall_mem_cons.2 ⟨subd7_0_8, List.forall_mem_cons.2 ⟨subd7_0_9, List.forall_mem_cons.2 ⟨subd7_0_10, List.forall_mem_cons.2 ⟨subd7_0_11, List.forall_mem_cons.2 ⟨subd7_0_12, List.forall_mem_cons.2 ⟨subd7_0_13, List.forall_mem_cons.2 ⟨subd7_0_14, List.forall_mem_cons.2 ⟨subd7_0_15, List.forall_mem_cons.2 ⟨subd7_0_16, List.forall_mem_cons.2 ⟨subd7_0_17, List.forall_mem_cons.2 ⟨subd7_0_18, List.forall_mem_cons.2 ⟨subd7_0_19, List.forall_mem_cons.2 ⟨subd7_0_20, List.forall_mem_cons.2 ⟨subd7_0_21, List.forall_mem_cons.2 ⟨subd7_0_22, List.forall_mem_cons.2 ⟨subd7_0_23, List.forall_mem_cons.2 ⟨subd7_0_24, List.forall_mem_cons.2 ⟨subd7_0_25, List.forall_mem_cons.2 ⟨subd7_0_26, List.forall_mem_cons.2 ⟨subd7_0_27, List.forall_mem_cons.2 ⟨subd7_0_28, List.forall_mem_cons.2 ⟨subd7_0_29, List.forall_mem_cons.2 ⟨subd7_0_30, List.forall_mem_cons.2 ⟨subd7_0_31, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd7_0_32 : subd7_0 [0, -3] = true := by decide +kernel
theorem subd7_0_33 : subd7_0 [0, -2] = true := by decide +kernel
theorem subd7_0_34 : subd7_0 [0, -1] = true := by decide +kernel
theorem subd7_0_35 : subd7_0 [0, 0] = true := by decide +kernel
theorem subd7_0_36 : subd7_0 [0, 1] = true := by decide +kernel
theorem subd7_0_37 : subd7_0 [0, 2] = true := by decide +kernel
theorem subd7_0_38 : subd7_0 [0, 3] = true := by decide +kernel
theorem subd7_0_39 : subd7_0 [0, 4] = true := by decide +kernel
theorem subd7_0_40 : subd7_0 [1, -6] = true := by decide +kernel
theorem subd7_0_41 : subd7_0 [1, -5] = true := by decide +kernel
theorem subd7_0_42 : subd7_0 [1, -4] = true := by decide +kernel
theorem subd7_0_43 : subd7_0 [1, -3] = true := by decide +kernel
theorem subd7_0_44 : subd7_0 [1, -2] = true := by decide +kernel
theorem subd7_0_45 : subd7_0 [1, -1] = true := by decide +kernel
theorem subd7_0_46 : subd7_0 [1, 0] = true := by decide +kernel
theorem subd7_0_47 : subd7_0 [1, 1] = true := by decide +kernel
theorem subd7_0_48 : subd7_0 [1, 2] = true := by decide +kernel
theorem subd7_0_49 : subd7_0 [1, 3] = true := by decide +kernel
theorem subd7_0_50 : subd7_0 [1, 4] = true := by decide +kernel
theorem subd7_0_51 : subd7_0 [2, -6] = true := by decide +kernel
theorem subd7_0_52 : subd7_0 [2, -5] = true := by decide +kernel
theorem subd7_0_53 : subd7_0 [2, -4] = true := by decide +kernel
theorem subd7_0_54 : subd7_0 [2, -3] = true := by decide +kernel
theorem subd7_0_55 : subd7_0 [2, -2] = true := by decide +kernel
theorem subd7_0_56 : subd7_0 [2, -1] = true := by decide +kernel
theorem subd7_0_57 : subd7_0 [2, 0] = true := by decide +kernel
theorem subd7_0_58 : subd7_0 [2, 1] = true := by decide +kernel
theorem subd7_0_59 : subd7_0 [2, 2] = true := by decide +kernel
theorem subd7_0_60 : subd7_0 [2, 3] = true := by decide +kernel
theorem subd7_0_61 : subd7_0 [3, -5] = true := by decide +kernel
theorem subd7_0_62 : subd7_0 [3, -4] = true := by decide +kernel
theorem subd7_0_63 : subd7_0 [3, -3] = true := by decide +kernel
theorem sbd7_0_1 : ∀ q ∈ blkd7_0_1, subd7_0 q = true := by
  unfold blkd7_0_1
  exact List.forall_mem_cons.2 ⟨subd7_0_32, List.forall_mem_cons.2 ⟨subd7_0_33, List.forall_mem_cons.2 ⟨subd7_0_34, List.forall_mem_cons.2 ⟨subd7_0_35, List.forall_mem_cons.2 ⟨subd7_0_36, List.forall_mem_cons.2 ⟨subd7_0_37, List.forall_mem_cons.2 ⟨subd7_0_38, List.forall_mem_cons.2 ⟨subd7_0_39, List.forall_mem_cons.2 ⟨subd7_0_40, List.forall_mem_cons.2 ⟨subd7_0_41, List.forall_mem_cons.2 ⟨subd7_0_42, List.forall_mem_cons.2 ⟨subd7_0_43, List.forall_mem_cons.2 ⟨subd7_0_44, List.forall_mem_cons.2 ⟨subd7_0_45, List.forall_mem_cons.2 ⟨subd7_0_46, List.forall_mem_cons.2 ⟨subd7_0_47, List.forall_mem_cons.2 ⟨subd7_0_48, List.forall_mem_cons.2 ⟨subd7_0_49, List.forall_mem_cons.2 ⟨subd7_0_50, List.forall_mem_cons.2 ⟨subd7_0_51, List.forall_mem_cons.2 ⟨subd7_0_52, List.forall_mem_cons.2 ⟨subd7_0_53, List.forall_mem_cons.2 ⟨subd7_0_54, List.forall_mem_cons.2 ⟨subd7_0_55, List.forall_mem_cons.2 ⟨subd7_0_56, List.forall_mem_cons.2 ⟨subd7_0_57, List.forall_mem_cons.2 ⟨subd7_0_58, List.forall_mem_cons.2 ⟨subd7_0_59, List.forall_mem_cons.2 ⟨subd7_0_60, List.forall_mem_cons.2 ⟨subd7_0_61, List.forall_mem_cons.2 ⟨subd7_0_62, List.forall_mem_cons.2 ⟨subd7_0_63, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
