import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_1_3872 : subd8_1 [6, -10] = true := by decide +kernel
theorem subd8_1_3873 : subd8_1 [6, -9] = true := by decide +kernel
theorem subd8_1_3874 : subd8_1 [6, -8] = true := by decide +kernel
theorem subd8_1_3875 : subd8_1 [6, -7, -10] = true := by decide +kernel
theorem subd8_1_3876 : subd8_1 [6, -7, -9] = true := by decide +kernel
theorem subd8_1_3877 : subd8_1 [6, -7, -8] = true := by decide +kernel
theorem subd8_1_3878 : subd8_1 [6, -7, -7] = true := by decide +kernel
theorem subd8_1_3879 : subd8_1 [6, -7, -6] = true := by decide +kernel
theorem subd8_1_3880 : subd8_1 [6, -7, -5] = true := by decide +kernel
theorem subd8_1_3881 : subd8_1 [6, -7, -4] = true := by decide +kernel
theorem subd8_1_3882 : subd8_1 [6, -7, -3] = true := by decide +kernel
theorem subd8_1_3883 : subd8_1 [6, -7, -2] = true := by decide +kernel
theorem subd8_1_3884 : subd8_1 [6, -7, -1] = true := by decide +kernel
theorem subd8_1_3885 : subd8_1 [6, -7, 0] = true := by decide +kernel
theorem subd8_1_3886 : subd8_1 [6, -7, 1] = true := by decide +kernel
theorem subd8_1_3887 : subd8_1 [6, -7, 2] = true := by decide +kernel
theorem subd8_1_3888 : subd8_1 [6, -7, 3] = true := by decide +kernel
theorem subd8_1_3889 : subd8_1 [6, -7, 4] = true := by decide +kernel
theorem subd8_1_3890 : subd8_1 [6, -6, -10] = true := by decide +kernel
theorem subd8_1_3891 : subd8_1 [6, -6, -9] = true := by decide +kernel
theorem subd8_1_3892 : subd8_1 [6, -6, -8] = true := by decide +kernel
theorem subd8_1_3893 : subd8_1 [6, -6, -7] = true := by decide +kernel
theorem subd8_1_3894 : subd8_1 [6, -6, -6] = true := by decide +kernel
theorem subd8_1_3895 : subd8_1 [6, -6, -5] = true := by decide +kernel
theorem subd8_1_3896 : subd8_1 [6, -6, -4] = true := by decide +kernel
theorem subd8_1_3897 : subd8_1 [6, -6, -3] = true := by decide +kernel
theorem subd8_1_3898 : subd8_1 [6, -6, -2] = true := by decide +kernel
theorem subd8_1_3899 : subd8_1 [6, -6, -1] = true := by decide +kernel
theorem subd8_1_3900 : subd8_1 [6, -6, 0] = true := by decide +kernel
theorem subd8_1_3901 : subd8_1 [6, -6, 1] = true := by decide +kernel
theorem subd8_1_3902 : subd8_1 [6, -6, 2] = true := by decide +kernel
theorem subd8_1_3903 : subd8_1 [6, -6, 3] = true := by decide +kernel
theorem sbd8_1_121 : ∀ q ∈ blkd8_1_121, subd8_1 q = true := by
  unfold blkd8_1_121
  exact List.forall_mem_cons.2 ⟨subd8_1_3872, List.forall_mem_cons.2 ⟨subd8_1_3873, List.forall_mem_cons.2 ⟨subd8_1_3874, List.forall_mem_cons.2 ⟨subd8_1_3875, List.forall_mem_cons.2 ⟨subd8_1_3876, List.forall_mem_cons.2 ⟨subd8_1_3877, List.forall_mem_cons.2 ⟨subd8_1_3878, List.forall_mem_cons.2 ⟨subd8_1_3879, List.forall_mem_cons.2 ⟨subd8_1_3880, List.forall_mem_cons.2 ⟨subd8_1_3881, List.forall_mem_cons.2 ⟨subd8_1_3882, List.forall_mem_cons.2 ⟨subd8_1_3883, List.forall_mem_cons.2 ⟨subd8_1_3884, List.forall_mem_cons.2 ⟨subd8_1_3885, List.forall_mem_cons.2 ⟨subd8_1_3886, List.forall_mem_cons.2 ⟨subd8_1_3887, List.forall_mem_cons.2 ⟨subd8_1_3888, List.forall_mem_cons.2 ⟨subd8_1_3889, List.forall_mem_cons.2 ⟨subd8_1_3890, List.forall_mem_cons.2 ⟨subd8_1_3891, List.forall_mem_cons.2 ⟨subd8_1_3892, List.forall_mem_cons.2 ⟨subd8_1_3893, List.forall_mem_cons.2 ⟨subd8_1_3894, List.forall_mem_cons.2 ⟨subd8_1_3895, List.forall_mem_cons.2 ⟨subd8_1_3896, List.forall_mem_cons.2 ⟨subd8_1_3897, List.forall_mem_cons.2 ⟨subd8_1_3898, List.forall_mem_cons.2 ⟨subd8_1_3899, List.forall_mem_cons.2 ⟨subd8_1_3900, List.forall_mem_cons.2 ⟨subd8_1_3901, List.forall_mem_cons.2 ⟨subd8_1_3902, List.forall_mem_cons.2 ⟨subd8_1_3903, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_3904 : subd8_1 [6, -6, 4] = true := by decide +kernel
theorem subd8_1_3905 : subd8_1 [6, -6, 5] = true := by decide +kernel
theorem subd8_1_3906 : subd8_1 [6, -5, -10] = true := by decide +kernel
theorem subd8_1_3907 : subd8_1 [6, -5, -9] = true := by decide +kernel
theorem subd8_1_3908 : subd8_1 [6, -5, -8] = true := by decide +kernel
theorem subd8_1_3909 : subd8_1 [6, -5, -7] = true := by decide +kernel
theorem subd8_1_3910 : subd8_1 [6, -5, -6] = true := by decide +kernel
theorem subd8_1_3911 : subd8_1 [6, -5, -5] = true := by decide +kernel
theorem subd8_1_3912 : subd8_1 [6, -5, -4] = true := by decide +kernel
theorem subd8_1_3913 : subd8_1 [6, -5, -3] = true := by decide +kernel
theorem subd8_1_3914 : subd8_1 [6, -5, -2] = true := by decide +kernel
theorem subd8_1_3915 : subd8_1 [6, -5, -1] = true := by decide +kernel
theorem subd8_1_3916 : subd8_1 [6, -5, 0] = true := by decide +kernel
theorem subd8_1_3917 : subd8_1 [6, -5, 1] = true := by decide +kernel
theorem subd8_1_3918 : subd8_1 [6, -5, 2] = true := by decide +kernel
theorem subd8_1_3919 : subd8_1 [6, -5, 3] = true := by decide +kernel
theorem subd8_1_3920 : subd8_1 [6, -5, 4] = true := by decide +kernel
theorem subd8_1_3921 : subd8_1 [6, -5, 5] = true := by decide +kernel
theorem subd8_1_3922 : subd8_1 [6, -5, 6] = true := by decide +kernel
theorem subd8_1_3923 : subd8_1 [6, -4, -11] = true := by decide +kernel
theorem subd8_1_3924 : subd8_1 [6, -4, -10] = true := by decide +kernel
theorem subd8_1_3925 : subd8_1 [6, -4, -9] = true := by decide +kernel
theorem subd8_1_3926 : subd8_1 [6, -4, -8] = true := by decide +kernel
theorem subd8_1_3927 : subd8_1 [6, -4, -7] = true := by decide +kernel
theorem subd8_1_3928 : subd8_1 [6, -4, -6] = true := by decide +kernel
theorem subd8_1_3929 : subd8_1 [6, -4, -5] = true := by decide +kernel
theorem subd8_1_3930 : subd8_1 [6, -4, -4] = true := by decide +kernel
theorem subd8_1_3931 : subd8_1 [6, -4, -3] = true := by decide +kernel
theorem subd8_1_3932 : subd8_1 [6, -4, -2] = true := by decide +kernel
theorem subd8_1_3933 : subd8_1 [6, -4, -1] = true := by decide +kernel
theorem subd8_1_3934 : subd8_1 [6, -4, 0] = true := by decide +kernel
theorem subd8_1_3935 : subd8_1 [6, -4, 1] = true := by decide +kernel
theorem sbd8_1_122 : ∀ q ∈ blkd8_1_122, subd8_1 q = true := by
  unfold blkd8_1_122
  exact List.forall_mem_cons.2 ⟨subd8_1_3904, List.forall_mem_cons.2 ⟨subd8_1_3905, List.forall_mem_cons.2 ⟨subd8_1_3906, List.forall_mem_cons.2 ⟨subd8_1_3907, List.forall_mem_cons.2 ⟨subd8_1_3908, List.forall_mem_cons.2 ⟨subd8_1_3909, List.forall_mem_cons.2 ⟨subd8_1_3910, List.forall_mem_cons.2 ⟨subd8_1_3911, List.forall_mem_cons.2 ⟨subd8_1_3912, List.forall_mem_cons.2 ⟨subd8_1_3913, List.forall_mem_cons.2 ⟨subd8_1_3914, List.forall_mem_cons.2 ⟨subd8_1_3915, List.forall_mem_cons.2 ⟨subd8_1_3916, List.forall_mem_cons.2 ⟨subd8_1_3917, List.forall_mem_cons.2 ⟨subd8_1_3918, List.forall_mem_cons.2 ⟨subd8_1_3919, List.forall_mem_cons.2 ⟨subd8_1_3920, List.forall_mem_cons.2 ⟨subd8_1_3921, List.forall_mem_cons.2 ⟨subd8_1_3922, List.forall_mem_cons.2 ⟨subd8_1_3923, List.forall_mem_cons.2 ⟨subd8_1_3924, List.forall_mem_cons.2 ⟨subd8_1_3925, List.forall_mem_cons.2 ⟨subd8_1_3926, List.forall_mem_cons.2 ⟨subd8_1_3927, List.forall_mem_cons.2 ⟨subd8_1_3928, List.forall_mem_cons.2 ⟨subd8_1_3929, List.forall_mem_cons.2 ⟨subd8_1_3930, List.forall_mem_cons.2 ⟨subd8_1_3931, List.forall_mem_cons.2 ⟨subd8_1_3932, List.forall_mem_cons.2 ⟨subd8_1_3933, List.forall_mem_cons.2 ⟨subd8_1_3934, List.forall_mem_cons.2 ⟨subd8_1_3935, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_3936 : subd8_1 [6, -4, 2] = true := by decide +kernel
theorem subd8_1_3937 : subd8_1 [6, -4, 3] = true := by decide +kernel
theorem subd8_1_3938 : subd8_1 [6, -4, 4] = true := by decide +kernel
theorem subd8_1_3939 : subd8_1 [6, -4, 5] = true := by decide +kernel
theorem subd8_1_3940 : subd8_1 [6, -4, 6] = true := by decide +kernel
theorem subd8_1_3941 : subd8_1 [6, -4, 7] = true := by decide +kernel
theorem subd8_1_3942 : subd8_1 [6, -3, -10] = true := by decide +kernel
theorem subd8_1_3943 : subd8_1 [6, -3, -9] = true := by decide +kernel
theorem subd8_1_3944 : subd8_1 [6, -3, -8] = true := by decide +kernel
theorem subd8_1_3945 : subd8_1 [6, -3, -7] = true := by decide +kernel
theorem subd8_1_3946 : subd8_1 [6, -3, -6] = true := by decide +kernel
theorem subd8_1_3947 : subd8_1 [6, -3, -5] = true := by decide +kernel
theorem subd8_1_3948 : subd8_1 [6, -3, -4] = true := by decide +kernel
theorem subd8_1_3949 : subd8_1 [6, -3, -3] = true := by decide +kernel
theorem subd8_1_3950 : subd8_1 [6, -3, -2] = true := by decide +kernel
theorem subd8_1_3951 : subd8_1 [6, -3, -1] = true := by decide +kernel
theorem subd8_1_3952 : subd8_1 [6, -3, 0] = true := by decide +kernel
theorem subd8_1_3953 : subd8_1 [6, -3, 1] = true := by decide +kernel
theorem subd8_1_3954 : subd8_1 [6, -3, 2] = true := by decide +kernel
theorem subd8_1_3955 : subd8_1 [6, -3, 3] = true := by decide +kernel
theorem subd8_1_3956 : subd8_1 [6, -3, 4] = true := by decide +kernel
theorem subd8_1_3957 : subd8_1 [6, -3, 5] = true := by decide +kernel
theorem subd8_1_3958 : subd8_1 [6, -3, 6] = true := by decide +kernel
theorem subd8_1_3959 : subd8_1 [6, -3, 7] = true := by decide +kernel
theorem subd8_1_3960 : subd8_1 [6, -2, -10] = true := by decide +kernel
theorem subd8_1_3961 : subd8_1 [6, -2, -9] = true := by decide +kernel
theorem subd8_1_3962 : subd8_1 [6, -2, -8] = true := by decide +kernel
theorem subd8_1_3963 : subd8_1 [6, -2, -7] = true := by decide +kernel
theorem subd8_1_3964 : subd8_1 [6, -2, -6] = true := by decide +kernel
theorem subd8_1_3965 : subd8_1 [6, -2, -5] = true := by decide +kernel
theorem subd8_1_3966 : subd8_1 [6, -2, -4] = true := by decide +kernel
theorem subd8_1_3967 : subd8_1 [6, -2, -3] = true := by decide +kernel
theorem sbd8_1_123 : ∀ q ∈ blkd8_1_123, subd8_1 q = true := by
  unfold blkd8_1_123
  exact List.forall_mem_cons.2 ⟨subd8_1_3936, List.forall_mem_cons.2 ⟨subd8_1_3937, List.forall_mem_cons.2 ⟨subd8_1_3938, List.forall_mem_cons.2 ⟨subd8_1_3939, List.forall_mem_cons.2 ⟨subd8_1_3940, List.forall_mem_cons.2 ⟨subd8_1_3941, List.forall_mem_cons.2 ⟨subd8_1_3942, List.forall_mem_cons.2 ⟨subd8_1_3943, List.forall_mem_cons.2 ⟨subd8_1_3944, List.forall_mem_cons.2 ⟨subd8_1_3945, List.forall_mem_cons.2 ⟨subd8_1_3946, List.forall_mem_cons.2 ⟨subd8_1_3947, List.forall_mem_cons.2 ⟨subd8_1_3948, List.forall_mem_cons.2 ⟨subd8_1_3949, List.forall_mem_cons.2 ⟨subd8_1_3950, List.forall_mem_cons.2 ⟨subd8_1_3951, List.forall_mem_cons.2 ⟨subd8_1_3952, List.forall_mem_cons.2 ⟨subd8_1_3953, List.forall_mem_cons.2 ⟨subd8_1_3954, List.forall_mem_cons.2 ⟨subd8_1_3955, List.forall_mem_cons.2 ⟨subd8_1_3956, List.forall_mem_cons.2 ⟨subd8_1_3957, List.forall_mem_cons.2 ⟨subd8_1_3958, List.forall_mem_cons.2 ⟨subd8_1_3959, List.forall_mem_cons.2 ⟨subd8_1_3960, List.forall_mem_cons.2 ⟨subd8_1_3961, List.forall_mem_cons.2 ⟨subd8_1_3962, List.forall_mem_cons.2 ⟨subd8_1_3963, List.forall_mem_cons.2 ⟨subd8_1_3964, List.forall_mem_cons.2 ⟨subd8_1_3965, List.forall_mem_cons.2 ⟨subd8_1_3966, List.forall_mem_cons.2 ⟨subd8_1_3967, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_3968 : subd8_1 [6, -2, -2] = true := by decide +kernel
theorem subd8_1_3969 : subd8_1 [6, -2, -1] = true := by decide +kernel
theorem subd8_1_3970 : subd8_1 [6, -2, 0] = true := by decide +kernel
theorem subd8_1_3971 : subd8_1 [6, -2, 1] = true := by decide +kernel
theorem subd8_1_3972 : subd8_1 [6, -2, 2] = true := by decide +kernel
theorem subd8_1_3973 : subd8_1 [6, -2, 3] = true := by decide +kernel
theorem subd8_1_3974 : subd8_1 [6, -2, 4] = true := by decide +kernel
theorem subd8_1_3975 : subd8_1 [6, -2, 5] = true := by decide +kernel
theorem subd8_1_3976 : subd8_1 [6, -2, 6] = true := by decide +kernel
theorem subd8_1_3977 : subd8_1 [6, -2, 7] = true := by decide +kernel
theorem subd8_1_3978 : subd8_1 [6, -2, 8] = true := by decide +kernel
theorem subd8_1_3979 : subd8_1 [6, -1, -10] = true := by decide +kernel
theorem subd8_1_3980 : subd8_1 [6, -1, -9] = true := by decide +kernel
theorem subd8_1_3981 : subd8_1 [6, -1, -8] = true := by decide +kernel
theorem subd8_1_3982 : subd8_1 [6, -1, -7] = true := by decide +kernel
theorem subd8_1_3983 : subd8_1 [6, -1, -6] = true := by decide +kernel
theorem subd8_1_3984 : subd8_1 [6, -1, -5] = true := by decide +kernel
theorem subd8_1_3985 : subd8_1 [6, -1, -4] = true := by decide +kernel
theorem subd8_1_3986 : subd8_1 [6, -1, -3] = true := by decide +kernel
theorem subd8_1_3987 : subd8_1 [6, -1, -2] = true := by decide +kernel
theorem subd8_1_3988 : subd8_1 [6, -1, -1] = true := by decide +kernel
theorem subd8_1_3989 : subd8_1 [6, -1, 0] = true := by decide +kernel
theorem subd8_1_3990 : subd8_1 [6, -1, 1] = true := by decide +kernel
theorem subd8_1_3991 : subd8_1 [6, -1, 2] = true := by decide +kernel
theorem subd8_1_3992 : subd8_1 [6, -1, 3] = true := by decide +kernel
theorem subd8_1_3993 : subd8_1 [6, -1, 4] = true := by decide +kernel
theorem subd8_1_3994 : subd8_1 [6, -1, 5] = true := by decide +kernel
theorem subd8_1_3995 : subd8_1 [6, -1, 6] = true := by decide +kernel
theorem subd8_1_3996 : subd8_1 [6, -1, 7] = true := by decide +kernel
theorem subd8_1_3997 : subd8_1 [6, -1, 8] = true := by decide +kernel
theorem subd8_1_3998 : subd8_1 [6, 0, -10] = true := by decide +kernel
theorem subd8_1_3999 : subd8_1 [6, 0, -9] = true := by decide +kernel
theorem sbd8_1_124 : ∀ q ∈ blkd8_1_124, subd8_1 q = true := by
  unfold blkd8_1_124
  exact List.forall_mem_cons.2 ⟨subd8_1_3968, List.forall_mem_cons.2 ⟨subd8_1_3969, List.forall_mem_cons.2 ⟨subd8_1_3970, List.forall_mem_cons.2 ⟨subd8_1_3971, List.forall_mem_cons.2 ⟨subd8_1_3972, List.forall_mem_cons.2 ⟨subd8_1_3973, List.forall_mem_cons.2 ⟨subd8_1_3974, List.forall_mem_cons.2 ⟨subd8_1_3975, List.forall_mem_cons.2 ⟨subd8_1_3976, List.forall_mem_cons.2 ⟨subd8_1_3977, List.forall_mem_cons.2 ⟨subd8_1_3978, List.forall_mem_cons.2 ⟨subd8_1_3979, List.forall_mem_cons.2 ⟨subd8_1_3980, List.forall_mem_cons.2 ⟨subd8_1_3981, List.forall_mem_cons.2 ⟨subd8_1_3982, List.forall_mem_cons.2 ⟨subd8_1_3983, List.forall_mem_cons.2 ⟨subd8_1_3984, List.forall_mem_cons.2 ⟨subd8_1_3985, List.forall_mem_cons.2 ⟨subd8_1_3986, List.forall_mem_cons.2 ⟨subd8_1_3987, List.forall_mem_cons.2 ⟨subd8_1_3988, List.forall_mem_cons.2 ⟨subd8_1_3989, List.forall_mem_cons.2 ⟨subd8_1_3990, List.forall_mem_cons.2 ⟨subd8_1_3991, List.forall_mem_cons.2 ⟨subd8_1_3992, List.forall_mem_cons.2 ⟨subd8_1_3993, List.forall_mem_cons.2 ⟨subd8_1_3994, List.forall_mem_cons.2 ⟨subd8_1_3995, List.forall_mem_cons.2 ⟨subd8_1_3996, List.forall_mem_cons.2 ⟨subd8_1_3997, List.forall_mem_cons.2 ⟨subd8_1_3998, List.forall_mem_cons.2 ⟨subd8_1_3999, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4000 : subd8_1 [6, 0, -8] = true := by decide +kernel
theorem subd8_1_4001 : subd8_1 [6, 0, -7] = true := by decide +kernel
theorem subd8_1_4002 : subd8_1 [6, 0, -6] = true := by decide +kernel
theorem subd8_1_4003 : subd8_1 [6, 0, -5] = true := by decide +kernel
theorem subd8_1_4004 : subd8_1 [6, 0, -4] = true := by decide +kernel
theorem subd8_1_4005 : subd8_1 [6, 0, -3] = true := by decide +kernel
theorem subd8_1_4006 : subd8_1 [6, 0, -2] = true := by decide +kernel
theorem subd8_1_4007 : subd8_1 [6, 0, -1] = true := by decide +kernel
theorem subd8_1_4008 : subd8_1 [6, 0, 0] = true := by decide +kernel
theorem subd8_1_4009 : subd8_1 [6, 0, 1] = true := by decide +kernel
theorem subd8_1_4010 : subd8_1 [6, 0, 2] = true := by decide +kernel
theorem subd8_1_4011 : subd8_1 [6, 0, 3] = true := by decide +kernel
theorem subd8_1_4012 : subd8_1 [6, 0, 4] = true := by decide +kernel
theorem subd8_1_4013 : subd8_1 [6, 0, 5] = true := by decide +kernel
theorem subd8_1_4014 : subd8_1 [6, 0, 6] = true := by decide +kernel
theorem subd8_1_4015 : subd8_1 [6, 0, 7] = true := by decide +kernel
theorem subd8_1_4016 : subd8_1 [6, 0, 8] = true := by decide +kernel
theorem subd8_1_4017 : subd8_1 [6, 1, -9] = true := by decide +kernel
theorem subd8_1_4018 : subd8_1 [6, 1, -8] = true := by decide +kernel
theorem subd8_1_4019 : subd8_1 [6, 1, -7] = true := by decide +kernel
theorem subd8_1_4020 : subd8_1 [6, 1, -6] = true := by decide +kernel
theorem subd8_1_4021 : subd8_1 [6, 1, -5] = true := by decide +kernel
theorem subd8_1_4022 : subd8_1 [6, 1, -4] = true := by decide +kernel
theorem subd8_1_4023 : subd8_1 [6, 1, -3] = true := by decide +kernel
theorem subd8_1_4024 : subd8_1 [6, 1, -2] = true := by decide +kernel
theorem subd8_1_4025 : subd8_1 [6, 1, -1] = true := by decide +kernel
theorem subd8_1_4026 : subd8_1 [6, 1, 0] = true := by decide +kernel
theorem subd8_1_4027 : subd8_1 [6, 1, 1] = true := by decide +kernel
theorem subd8_1_4028 : subd8_1 [6, 1, 2] = true := by decide +kernel
theorem subd8_1_4029 : subd8_1 [6, 1, 3] = true := by decide +kernel
theorem subd8_1_4030 : subd8_1 [6, 1, 4] = true := by decide +kernel
theorem subd8_1_4031 : subd8_1 [6, 1, 5] = true := by decide +kernel
theorem sbd8_1_125 : ∀ q ∈ blkd8_1_125, subd8_1 q = true := by
  unfold blkd8_1_125
  exact List.forall_mem_cons.2 ⟨subd8_1_4000, List.forall_mem_cons.2 ⟨subd8_1_4001, List.forall_mem_cons.2 ⟨subd8_1_4002, List.forall_mem_cons.2 ⟨subd8_1_4003, List.forall_mem_cons.2 ⟨subd8_1_4004, List.forall_mem_cons.2 ⟨subd8_1_4005, List.forall_mem_cons.2 ⟨subd8_1_4006, List.forall_mem_cons.2 ⟨subd8_1_4007, List.forall_mem_cons.2 ⟨subd8_1_4008, List.forall_mem_cons.2 ⟨subd8_1_4009, List.forall_mem_cons.2 ⟨subd8_1_4010, List.forall_mem_cons.2 ⟨subd8_1_4011, List.forall_mem_cons.2 ⟨subd8_1_4012, List.forall_mem_cons.2 ⟨subd8_1_4013, List.forall_mem_cons.2 ⟨subd8_1_4014, List.forall_mem_cons.2 ⟨subd8_1_4015, List.forall_mem_cons.2 ⟨subd8_1_4016, List.forall_mem_cons.2 ⟨subd8_1_4017, List.forall_mem_cons.2 ⟨subd8_1_4018, List.forall_mem_cons.2 ⟨subd8_1_4019, List.forall_mem_cons.2 ⟨subd8_1_4020, List.forall_mem_cons.2 ⟨subd8_1_4021, List.forall_mem_cons.2 ⟨subd8_1_4022, List.forall_mem_cons.2 ⟨subd8_1_4023, List.forall_mem_cons.2 ⟨subd8_1_4024, List.forall_mem_cons.2 ⟨subd8_1_4025, List.forall_mem_cons.2 ⟨subd8_1_4026, List.forall_mem_cons.2 ⟨subd8_1_4027, List.forall_mem_cons.2 ⟨subd8_1_4028, List.forall_mem_cons.2 ⟨subd8_1_4029, List.forall_mem_cons.2 ⟨subd8_1_4030, List.forall_mem_cons.2 ⟨subd8_1_4031, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4032 : subd8_1 [6, 1, 6] = true := by decide +kernel
theorem subd8_1_4033 : subd8_1 [6, 1, 7] = true := by decide +kernel
theorem subd8_1_4034 : subd8_1 [6, 1, 8] = true := by decide +kernel
theorem subd8_1_4035 : subd8_1 [6, 2, -8] = true := by decide +kernel
theorem subd8_1_4036 : subd8_1 [6, 2, -7] = true := by decide +kernel
theorem subd8_1_4037 : subd8_1 [6, 2, -6] = true := by decide +kernel
theorem subd8_1_4038 : subd8_1 [6, 2, -5] = true := by decide +kernel
theorem subd8_1_4039 : subd8_1 [6, 2, -4] = true := by decide +kernel
theorem subd8_1_4040 : subd8_1 [6, 2, -3] = true := by decide +kernel
theorem subd8_1_4041 : subd8_1 [6, 2, -2] = true := by decide +kernel
theorem subd8_1_4042 : subd8_1 [6, 2, -1] = true := by decide +kernel
theorem subd8_1_4043 : subd8_1 [6, 2, 0] = true := by decide +kernel
theorem subd8_1_4044 : subd8_1 [6, 2, 1] = true := by decide +kernel
theorem subd8_1_4045 : subd8_1 [6, 2, 2] = true := by decide +kernel
theorem subd8_1_4046 : subd8_1 [6, 2, 3] = true := by decide +kernel
theorem subd8_1_4047 : subd8_1 [6, 2, 4] = true := by decide +kernel
theorem subd8_1_4048 : subd8_1 [6, 2, 5] = true := by decide +kernel
theorem subd8_1_4049 : subd8_1 [6, 2, 6] = true := by decide +kernel
theorem subd8_1_4050 : subd8_1 [6, 2, 7] = true := by decide +kernel
theorem subd8_1_4051 : subd8_1 [6, 2, 8] = true := by decide +kernel
theorem subd8_1_4052 : subd8_1 [6, 3, -8] = true := by decide +kernel
theorem subd8_1_4053 : subd8_1 [6, 3, -7] = true := by decide +kernel
theorem subd8_1_4054 : subd8_1 [6, 3, -6] = true := by decide +kernel
theorem subd8_1_4055 : subd8_1 [6, 3, -5] = true := by decide +kernel
theorem subd8_1_4056 : subd8_1 [6, 3, -4] = true := by decide +kernel
theorem subd8_1_4057 : subd8_1 [6, 3, -3] = true := by decide +kernel
theorem subd8_1_4058 : subd8_1 [6, 3, -2] = true := by decide +kernel
theorem subd8_1_4059 : subd8_1 [6, 3, -1] = true := by decide +kernel
theorem subd8_1_4060 : subd8_1 [6, 3, 0] = true := by decide +kernel
theorem subd8_1_4061 : subd8_1 [6, 3, 1] = true := by decide +kernel
theorem subd8_1_4062 : subd8_1 [6, 3, 2] = true := by decide +kernel
theorem subd8_1_4063 : subd8_1 [6, 3, 3] = true := by decide +kernel
theorem sbd8_1_126 : ∀ q ∈ blkd8_1_126, subd8_1 q = true := by
  unfold blkd8_1_126
  exact List.forall_mem_cons.2 ⟨subd8_1_4032, List.forall_mem_cons.2 ⟨subd8_1_4033, List.forall_mem_cons.2 ⟨subd8_1_4034, List.forall_mem_cons.2 ⟨subd8_1_4035, List.forall_mem_cons.2 ⟨subd8_1_4036, List.forall_mem_cons.2 ⟨subd8_1_4037, List.forall_mem_cons.2 ⟨subd8_1_4038, List.forall_mem_cons.2 ⟨subd8_1_4039, List.forall_mem_cons.2 ⟨subd8_1_4040, List.forall_mem_cons.2 ⟨subd8_1_4041, List.forall_mem_cons.2 ⟨subd8_1_4042, List.forall_mem_cons.2 ⟨subd8_1_4043, List.forall_mem_cons.2 ⟨subd8_1_4044, List.forall_mem_cons.2 ⟨subd8_1_4045, List.forall_mem_cons.2 ⟨subd8_1_4046, List.forall_mem_cons.2 ⟨subd8_1_4047, List.forall_mem_cons.2 ⟨subd8_1_4048, List.forall_mem_cons.2 ⟨subd8_1_4049, List.forall_mem_cons.2 ⟨subd8_1_4050, List.forall_mem_cons.2 ⟨subd8_1_4051, List.forall_mem_cons.2 ⟨subd8_1_4052, List.forall_mem_cons.2 ⟨subd8_1_4053, List.forall_mem_cons.2 ⟨subd8_1_4054, List.forall_mem_cons.2 ⟨subd8_1_4055, List.forall_mem_cons.2 ⟨subd8_1_4056, List.forall_mem_cons.2 ⟨subd8_1_4057, List.forall_mem_cons.2 ⟨subd8_1_4058, List.forall_mem_cons.2 ⟨subd8_1_4059, List.forall_mem_cons.2 ⟨subd8_1_4060, List.forall_mem_cons.2 ⟨subd8_1_4061, List.forall_mem_cons.2 ⟨subd8_1_4062, List.forall_mem_cons.2 ⟨subd8_1_4063, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4064 : subd8_1 [6, 3, 4] = true := by decide +kernel
theorem subd8_1_4065 : subd8_1 [6, 3, 5] = true := by decide +kernel
theorem subd8_1_4066 : subd8_1 [6, 3, 6] = true := by decide +kernel
theorem subd8_1_4067 : subd8_1 [6, 3, 7] = true := by decide +kernel
theorem subd8_1_4068 : subd8_1 [6, 3, 8] = true := by decide +kernel
theorem subd8_1_4069 : subd8_1 [6, 4, -7] = true := by decide +kernel
theorem subd8_1_4070 : subd8_1 [6, 4, -6] = true := by decide +kernel
theorem subd8_1_4071 : subd8_1 [6, 4, -5] = true := by decide +kernel
theorem subd8_1_4072 : subd8_1 [6, 4, -4] = true := by decide +kernel
theorem subd8_1_4073 : subd8_1 [6, 4, -3] = true := by decide +kernel
theorem subd8_1_4074 : subd8_1 [6, 4, -2] = true := by decide +kernel
theorem subd8_1_4075 : subd8_1 [6, 4, -1] = true := by decide +kernel
theorem subd8_1_4076 : subd8_1 [6, 4, 0] = true := by decide +kernel
theorem subd8_1_4077 : subd8_1 [6, 4, 1] = true := by decide +kernel
theorem subd8_1_4078 : subd8_1 [6, 4, 2] = true := by decide +kernel
theorem subd8_1_4079 : subd8_1 [6, 4, 3] = true := by decide +kernel
theorem subd8_1_4080 : subd8_1 [6, 4, 4] = true := by decide +kernel
theorem subd8_1_4081 : subd8_1 [6, 4, 5] = true := by decide +kernel
theorem subd8_1_4082 : subd8_1 [6, 4, 6] = true := by decide +kernel
theorem subd8_1_4083 : subd8_1 [6, 4, 7] = true := by decide +kernel
theorem subd8_1_4084 : subd8_1 [6, 4, 8] = true := by decide +kernel
theorem subd8_1_4085 : subd8_1 [6, 5] = true := by decide +kernel
theorem subd8_1_4086 : subd8_1 [6, 6] = true := by decide +kernel
theorem subd8_1_4087 : subd8_1 [6, 7] = true := by decide +kernel
theorem subd8_1_4088 : subd8_1 [7, -11] = true := by decide +kernel
theorem subd8_1_4089 : subd8_1 [7, -10] = true := by decide +kernel
theorem subd8_1_4090 : subd8_1 [7, -9] = true := by decide +kernel
theorem subd8_1_4091 : subd8_1 [7, -8] = true := by decide +kernel
theorem subd8_1_4092 : subd8_1 [7, -7] = true := by decide +kernel
theorem subd8_1_4093 : subd8_1 [7, -6, -10] = true := by decide +kernel
theorem subd8_1_4094 : subd8_1 [7, -6, -9] = true := by decide +kernel
theorem subd8_1_4095 : subd8_1 [7, -6, -8] = true := by decide +kernel
theorem sbd8_1_127 : ∀ q ∈ blkd8_1_127, subd8_1 q = true := by
  unfold blkd8_1_127
  exact List.forall_mem_cons.2 ⟨subd8_1_4064, List.forall_mem_cons.2 ⟨subd8_1_4065, List.forall_mem_cons.2 ⟨subd8_1_4066, List.forall_mem_cons.2 ⟨subd8_1_4067, List.forall_mem_cons.2 ⟨subd8_1_4068, List.forall_mem_cons.2 ⟨subd8_1_4069, List.forall_mem_cons.2 ⟨subd8_1_4070, List.forall_mem_cons.2 ⟨subd8_1_4071, List.forall_mem_cons.2 ⟨subd8_1_4072, List.forall_mem_cons.2 ⟨subd8_1_4073, List.forall_mem_cons.2 ⟨subd8_1_4074, List.forall_mem_cons.2 ⟨subd8_1_4075, List.forall_mem_cons.2 ⟨subd8_1_4076, List.forall_mem_cons.2 ⟨subd8_1_4077, List.forall_mem_cons.2 ⟨subd8_1_4078, List.forall_mem_cons.2 ⟨subd8_1_4079, List.forall_mem_cons.2 ⟨subd8_1_4080, List.forall_mem_cons.2 ⟨subd8_1_4081, List.forall_mem_cons.2 ⟨subd8_1_4082, List.forall_mem_cons.2 ⟨subd8_1_4083, List.forall_mem_cons.2 ⟨subd8_1_4084, List.forall_mem_cons.2 ⟨subd8_1_4085, List.forall_mem_cons.2 ⟨subd8_1_4086, List.forall_mem_cons.2 ⟨subd8_1_4087, List.forall_mem_cons.2 ⟨subd8_1_4088, List.forall_mem_cons.2 ⟨subd8_1_4089, List.forall_mem_cons.2 ⟨subd8_1_4090, List.forall_mem_cons.2 ⟨subd8_1_4091, List.forall_mem_cons.2 ⟨subd8_1_4092, List.forall_mem_cons.2 ⟨subd8_1_4093, List.forall_mem_cons.2 ⟨subd8_1_4094, List.forall_mem_cons.2 ⟨subd8_1_4095, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4096 : subd8_1 [7, -6, -7] = true := by decide +kernel
theorem subd8_1_4097 : subd8_1 [7, -6, -6] = true := by decide +kernel
theorem subd8_1_4098 : subd8_1 [7, -6, -5] = true := by decide +kernel
theorem subd8_1_4099 : subd8_1 [7, -6, -4] = true := by decide +kernel
theorem subd8_1_4100 : subd8_1 [7, -6, -3] = true := by decide +kernel
theorem subd8_1_4101 : subd8_1 [7, -6, -2] = true := by decide +kernel
theorem subd8_1_4102 : subd8_1 [7, -6, -1] = true := by decide +kernel
theorem subd8_1_4103 : subd8_1 [7, -6, 0] = true := by decide +kernel
theorem subd8_1_4104 : subd8_1 [7, -6, 1] = true := by decide +kernel
theorem subd8_1_4105 : subd8_1 [7, -6, 2] = true := by decide +kernel
theorem subd8_1_4106 : subd8_1 [7, -6, 3] = true := by decide +kernel
theorem subd8_1_4107 : subd8_1 [7, -6, 4] = true := by decide +kernel
theorem subd8_1_4108 : subd8_1 [7, -6, 5] = true := by decide +kernel
theorem subd8_1_4109 : subd8_1 [7, -5, -10] = true := by decide +kernel
theorem subd8_1_4110 : subd8_1 [7, -5, -9] = true := by decide +kernel
theorem subd8_1_4111 : subd8_1 [7, -5, -8] = true := by decide +kernel
theorem subd8_1_4112 : subd8_1 [7, -5, -7] = true := by decide +kernel
theorem subd8_1_4113 : subd8_1 [7, -5, -6] = true := by decide +kernel
theorem subd8_1_4114 : subd8_1 [7, -5, -5] = true := by decide +kernel
theorem subd8_1_4115 : subd8_1 [7, -5, -4] = true := by decide +kernel
theorem subd8_1_4116 : subd8_1 [7, -5, -3] = true := by decide +kernel
theorem subd8_1_4117 : subd8_1 [7, -5, -2] = true := by decide +kernel
theorem subd8_1_4118 : subd8_1 [7, -5, -1] = true := by decide +kernel
theorem subd8_1_4119 : subd8_1 [7, -5, 0] = true := by decide +kernel
theorem subd8_1_4120 : subd8_1 [7, -5, 1] = true := by decide +kernel
theorem subd8_1_4121 : subd8_1 [7, -5, 2] = true := by decide +kernel
theorem subd8_1_4122 : subd8_1 [7, -5, 3] = true := by decide +kernel
theorem subd8_1_4123 : subd8_1 [7, -5, 4] = true := by decide +kernel
theorem subd8_1_4124 : subd8_1 [7, -5, 5] = true := by decide +kernel
theorem subd8_1_4125 : subd8_1 [7, -4, -10] = true := by decide +kernel
theorem subd8_1_4126 : subd8_1 [7, -4, -9] = true := by decide +kernel
theorem subd8_1_4127 : subd8_1 [7, -4, -8] = true := by decide +kernel
theorem sbd8_1_128 : ∀ q ∈ blkd8_1_128, subd8_1 q = true := by
  unfold blkd8_1_128
  exact List.forall_mem_cons.2 ⟨subd8_1_4096, List.forall_mem_cons.2 ⟨subd8_1_4097, List.forall_mem_cons.2 ⟨subd8_1_4098, List.forall_mem_cons.2 ⟨subd8_1_4099, List.forall_mem_cons.2 ⟨subd8_1_4100, List.forall_mem_cons.2 ⟨subd8_1_4101, List.forall_mem_cons.2 ⟨subd8_1_4102, List.forall_mem_cons.2 ⟨subd8_1_4103, List.forall_mem_cons.2 ⟨subd8_1_4104, List.forall_mem_cons.2 ⟨subd8_1_4105, List.forall_mem_cons.2 ⟨subd8_1_4106, List.forall_mem_cons.2 ⟨subd8_1_4107, List.forall_mem_cons.2 ⟨subd8_1_4108, List.forall_mem_cons.2 ⟨subd8_1_4109, List.forall_mem_cons.2 ⟨subd8_1_4110, List.forall_mem_cons.2 ⟨subd8_1_4111, List.forall_mem_cons.2 ⟨subd8_1_4112, List.forall_mem_cons.2 ⟨subd8_1_4113, List.forall_mem_cons.2 ⟨subd8_1_4114, List.forall_mem_cons.2 ⟨subd8_1_4115, List.forall_mem_cons.2 ⟨subd8_1_4116, List.forall_mem_cons.2 ⟨subd8_1_4117, List.forall_mem_cons.2 ⟨subd8_1_4118, List.forall_mem_cons.2 ⟨subd8_1_4119, List.forall_mem_cons.2 ⟨subd8_1_4120, List.forall_mem_cons.2 ⟨subd8_1_4121, List.forall_mem_cons.2 ⟨subd8_1_4122, List.forall_mem_cons.2 ⟨subd8_1_4123, List.forall_mem_cons.2 ⟨subd8_1_4124, List.forall_mem_cons.2 ⟨subd8_1_4125, List.forall_mem_cons.2 ⟨subd8_1_4126, List.forall_mem_cons.2 ⟨subd8_1_4127, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4128 : subd8_1 [7, -4, -7] = true := by decide +kernel
theorem subd8_1_4129 : subd8_1 [7, -4, -6] = true := by decide +kernel
theorem subd8_1_4130 : subd8_1 [7, -4, -5] = true := by decide +kernel
theorem subd8_1_4131 : subd8_1 [7, -4, -4] = true := by decide +kernel
theorem subd8_1_4132 : subd8_1 [7, -4, -3] = true := by decide +kernel
theorem subd8_1_4133 : subd8_1 [7, -4, -2] = true := by decide +kernel
theorem subd8_1_4134 : subd8_1 [7, -4, -1] = true := by decide +kernel
theorem subd8_1_4135 : subd8_1 [7, -4, 0] = true := by decide +kernel
theorem subd8_1_4136 : subd8_1 [7, -4, 1] = true := by decide +kernel
theorem subd8_1_4137 : subd8_1 [7, -4, 2] = true := by decide +kernel
theorem subd8_1_4138 : subd8_1 [7, -4, 3] = true := by decide +kernel
theorem subd8_1_4139 : subd8_1 [7, -4, 4] = true := by decide +kernel
theorem subd8_1_4140 : subd8_1 [7, -4, 5] = true := by decide +kernel
theorem subd8_1_4141 : subd8_1 [7, -4, 6] = true := by decide +kernel
theorem subd8_1_4142 : subd8_1 [7, -3, -10] = true := by decide +kernel
theorem subd8_1_4143 : subd8_1 [7, -3, -9] = true := by decide +kernel
theorem subd8_1_4144 : subd8_1 [7, -3, -8] = true := by decide +kernel
theorem subd8_1_4145 : subd8_1 [7, -3, -7] = true := by decide +kernel
theorem subd8_1_4146 : subd8_1 [7, -3, -6] = true := by decide +kernel
theorem subd8_1_4147 : subd8_1 [7, -3, -5] = true := by decide +kernel
theorem subd8_1_4148 : subd8_1 [7, -3, -4] = true := by decide +kernel
theorem subd8_1_4149 : subd8_1 [7, -3, -3] = true := by decide +kernel
theorem subd8_1_4150 : subd8_1 [7, -3, -2] = true := by decide +kernel
theorem subd8_1_4151 : subd8_1 [7, -3, -1] = true := by decide +kernel
theorem subd8_1_4152 : subd8_1 [7, -3, 0] = true := by decide +kernel
theorem subd8_1_4153 : subd8_1 [7, -3, 1] = true := by decide +kernel
theorem subd8_1_4154 : subd8_1 [7, -3, 2] = true := by decide +kernel
theorem subd8_1_4155 : subd8_1 [7, -3, 3] = true := by decide +kernel
theorem subd8_1_4156 : subd8_1 [7, -3, 4] = true := by decide +kernel
theorem subd8_1_4157 : subd8_1 [7, -3, 5] = true := by decide +kernel
theorem subd8_1_4158 : subd8_1 [7, -3, 6] = true := by decide +kernel
theorem subd8_1_4159 : subd8_1 [7, -3, 7] = true := by decide +kernel
theorem sbd8_1_129 : ∀ q ∈ blkd8_1_129, subd8_1 q = true := by
  unfold blkd8_1_129
  exact List.forall_mem_cons.2 ⟨subd8_1_4128, List.forall_mem_cons.2 ⟨subd8_1_4129, List.forall_mem_cons.2 ⟨subd8_1_4130, List.forall_mem_cons.2 ⟨subd8_1_4131, List.forall_mem_cons.2 ⟨subd8_1_4132, List.forall_mem_cons.2 ⟨subd8_1_4133, List.forall_mem_cons.2 ⟨subd8_1_4134, List.forall_mem_cons.2 ⟨subd8_1_4135, List.forall_mem_cons.2 ⟨subd8_1_4136, List.forall_mem_cons.2 ⟨subd8_1_4137, List.forall_mem_cons.2 ⟨subd8_1_4138, List.forall_mem_cons.2 ⟨subd8_1_4139, List.forall_mem_cons.2 ⟨subd8_1_4140, List.forall_mem_cons.2 ⟨subd8_1_4141, List.forall_mem_cons.2 ⟨subd8_1_4142, List.forall_mem_cons.2 ⟨subd8_1_4143, List.forall_mem_cons.2 ⟨subd8_1_4144, List.forall_mem_cons.2 ⟨subd8_1_4145, List.forall_mem_cons.2 ⟨subd8_1_4146, List.forall_mem_cons.2 ⟨subd8_1_4147, List.forall_mem_cons.2 ⟨subd8_1_4148, List.forall_mem_cons.2 ⟨subd8_1_4149, List.forall_mem_cons.2 ⟨subd8_1_4150, List.forall_mem_cons.2 ⟨subd8_1_4151, List.forall_mem_cons.2 ⟨subd8_1_4152, List.forall_mem_cons.2 ⟨subd8_1_4153, List.forall_mem_cons.2 ⟨subd8_1_4154, List.forall_mem_cons.2 ⟨subd8_1_4155, List.forall_mem_cons.2 ⟨subd8_1_4156, List.forall_mem_cons.2 ⟨subd8_1_4157, List.forall_mem_cons.2 ⟨subd8_1_4158, List.forall_mem_cons.2 ⟨subd8_1_4159, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4160 : subd8_1 [7, -2, -10] = true := by decide +kernel
theorem subd8_1_4161 : subd8_1 [7, -2, -9] = true := by decide +kernel
theorem subd8_1_4162 : subd8_1 [7, -2, -8] = true := by decide +kernel
theorem subd8_1_4163 : subd8_1 [7, -2, -7] = true := by decide +kernel
theorem subd8_1_4164 : subd8_1 [7, -2, -6] = true := by decide +kernel
theorem subd8_1_4165 : subd8_1 [7, -2, -5] = true := by decide +kernel
theorem subd8_1_4166 : subd8_1 [7, -2, -4] = true := by decide +kernel
theorem subd8_1_4167 : subd8_1 [7, -2, -3] = true := by decide +kernel
theorem subd8_1_4168 : subd8_1 [7, -2, -2] = true := by decide +kernel
theorem subd8_1_4169 : subd8_1 [7, -2, -1] = true := by decide +kernel
theorem subd8_1_4170 : subd8_1 [7, -2, 0] = true := by decide +kernel
theorem subd8_1_4171 : subd8_1 [7, -2, 1] = true := by decide +kernel
theorem subd8_1_4172 : subd8_1 [7, -2, 2] = true := by decide +kernel
theorem subd8_1_4173 : subd8_1 [7, -2, 3] = true := by decide +kernel
theorem subd8_1_4174 : subd8_1 [7, -2, 4] = true := by decide +kernel
theorem subd8_1_4175 : subd8_1 [7, -2, 5] = true := by decide +kernel
theorem subd8_1_4176 : subd8_1 [7, -2, 6] = true := by decide +kernel
theorem subd8_1_4177 : subd8_1 [7, -2, 7] = true := by decide +kernel
theorem subd8_1_4178 : subd8_1 [7, -1, -9] = true := by decide +kernel
theorem subd8_1_4179 : subd8_1 [7, -1, -8] = true := by decide +kernel
theorem subd8_1_4180 : subd8_1 [7, -1, -7] = true := by decide +kernel
theorem subd8_1_4181 : subd8_1 [7, -1, -6] = true := by decide +kernel
theorem subd8_1_4182 : subd8_1 [7, -1, -5] = true := by decide +kernel
theorem subd8_1_4183 : subd8_1 [7, -1, -4] = true := by decide +kernel
theorem subd8_1_4184 : subd8_1 [7, -1, -3] = true := by decide +kernel
theorem subd8_1_4185 : subd8_1 [7, -1, -2] = true := by decide +kernel
theorem subd8_1_4186 : subd8_1 [7, -1, -1] = true := by decide +kernel
theorem subd8_1_4187 : subd8_1 [7, -1, 0] = true := by decide +kernel
theorem subd8_1_4188 : subd8_1 [7, -1, 1] = true := by decide +kernel
theorem subd8_1_4189 : subd8_1 [7, -1, 2] = true := by decide +kernel
theorem subd8_1_4190 : subd8_1 [7, -1, 3] = true := by decide +kernel
theorem subd8_1_4191 : subd8_1 [7, -1, 4] = true := by decide +kernel
theorem sbd8_1_130 : ∀ q ∈ blkd8_1_130, subd8_1 q = true := by
  unfold blkd8_1_130
  exact List.forall_mem_cons.2 ⟨subd8_1_4160, List.forall_mem_cons.2 ⟨subd8_1_4161, List.forall_mem_cons.2 ⟨subd8_1_4162, List.forall_mem_cons.2 ⟨subd8_1_4163, List.forall_mem_cons.2 ⟨subd8_1_4164, List.forall_mem_cons.2 ⟨subd8_1_4165, List.forall_mem_cons.2 ⟨subd8_1_4166, List.forall_mem_cons.2 ⟨subd8_1_4167, List.forall_mem_cons.2 ⟨subd8_1_4168, List.forall_mem_cons.2 ⟨subd8_1_4169, List.forall_mem_cons.2 ⟨subd8_1_4170, List.forall_mem_cons.2 ⟨subd8_1_4171, List.forall_mem_cons.2 ⟨subd8_1_4172, List.forall_mem_cons.2 ⟨subd8_1_4173, List.forall_mem_cons.2 ⟨subd8_1_4174, List.forall_mem_cons.2 ⟨subd8_1_4175, List.forall_mem_cons.2 ⟨subd8_1_4176, List.forall_mem_cons.2 ⟨subd8_1_4177, List.forall_mem_cons.2 ⟨subd8_1_4178, List.forall_mem_cons.2 ⟨subd8_1_4179, List.forall_mem_cons.2 ⟨subd8_1_4180, List.forall_mem_cons.2 ⟨subd8_1_4181, List.forall_mem_cons.2 ⟨subd8_1_4182, List.forall_mem_cons.2 ⟨subd8_1_4183, List.forall_mem_cons.2 ⟨subd8_1_4184, List.forall_mem_cons.2 ⟨subd8_1_4185, List.forall_mem_cons.2 ⟨subd8_1_4186, List.forall_mem_cons.2 ⟨subd8_1_4187, List.forall_mem_cons.2 ⟨subd8_1_4188, List.forall_mem_cons.2 ⟨subd8_1_4189, List.forall_mem_cons.2 ⟨subd8_1_4190, List.forall_mem_cons.2 ⟨subd8_1_4191, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4192 : subd8_1 [7, -1, 5] = true := by decide +kernel
theorem subd8_1_4193 : subd8_1 [7, -1, 6] = true := by decide +kernel
theorem subd8_1_4194 : subd8_1 [7, -1, 7] = true := by decide +kernel
theorem subd8_1_4195 : subd8_1 [7, 0, -9] = true := by decide +kernel
theorem subd8_1_4196 : subd8_1 [7, 0, -8] = true := by decide +kernel
theorem subd8_1_4197 : subd8_1 [7, 0, -7] = true := by decide +kernel
theorem subd8_1_4198 : subd8_1 [7, 0, -6] = true := by decide +kernel
theorem subd8_1_4199 : subd8_1 [7, 0, -5] = true := by decide +kernel
theorem subd8_1_4200 : subd8_1 [7, 0, -4] = true := by decide +kernel
theorem subd8_1_4201 : subd8_1 [7, 0, -3] = true := by decide +kernel
theorem subd8_1_4202 : subd8_1 [7, 0, -2] = true := by decide +kernel
theorem subd8_1_4203 : subd8_1 [7, 0, -1] = true := by decide +kernel
theorem subd8_1_4204 : subd8_1 [7, 0, 0] = true := by decide +kernel
theorem subd8_1_4205 : subd8_1 [7, 0, 1] = true := by decide +kernel
theorem subd8_1_4206 : subd8_1 [7, 0, 2] = true := by decide +kernel
theorem subd8_1_4207 : subd8_1 [7, 0, 3] = true := by decide +kernel
theorem subd8_1_4208 : subd8_1 [7, 0, 4] = true := by decide +kernel
theorem subd8_1_4209 : subd8_1 [7, 0, 5] = true := by decide +kernel
theorem subd8_1_4210 : subd8_1 [7, 0, 6] = true := by decide +kernel
theorem subd8_1_4211 : subd8_1 [7, 0, 7] = true := by decide +kernel
theorem subd8_1_4212 : subd8_1 [7, 1, -8] = true := by decide +kernel
theorem subd8_1_4213 : subd8_1 [7, 1, -7] = true := by decide +kernel
theorem subd8_1_4214 : subd8_1 [7, 1, -6] = true := by decide +kernel
theorem subd8_1_4215 : subd8_1 [7, 1, -5] = true := by decide +kernel
theorem subd8_1_4216 : subd8_1 [7, 1, -4] = true := by decide +kernel
theorem subd8_1_4217 : subd8_1 [7, 1, -3] = true := by decide +kernel
theorem subd8_1_4218 : subd8_1 [7, 1, -2] = true := by decide +kernel
theorem subd8_1_4219 : subd8_1 [7, 1, -1] = true := by decide +kernel
theorem subd8_1_4220 : subd8_1 [7, 1, 0] = true := by decide +kernel
theorem subd8_1_4221 : subd8_1 [7, 1, 1] = true := by decide +kernel
theorem subd8_1_4222 : subd8_1 [7, 1, 2] = true := by decide +kernel
theorem subd8_1_4223 : subd8_1 [7, 1, 3] = true := by decide +kernel
theorem sbd8_1_131 : ∀ q ∈ blkd8_1_131, subd8_1 q = true := by
  unfold blkd8_1_131
  exact List.forall_mem_cons.2 ⟨subd8_1_4192, List.forall_mem_cons.2 ⟨subd8_1_4193, List.forall_mem_cons.2 ⟨subd8_1_4194, List.forall_mem_cons.2 ⟨subd8_1_4195, List.forall_mem_cons.2 ⟨subd8_1_4196, List.forall_mem_cons.2 ⟨subd8_1_4197, List.forall_mem_cons.2 ⟨subd8_1_4198, List.forall_mem_cons.2 ⟨subd8_1_4199, List.forall_mem_cons.2 ⟨subd8_1_4200, List.forall_mem_cons.2 ⟨subd8_1_4201, List.forall_mem_cons.2 ⟨subd8_1_4202, List.forall_mem_cons.2 ⟨subd8_1_4203, List.forall_mem_cons.2 ⟨subd8_1_4204, List.forall_mem_cons.2 ⟨subd8_1_4205, List.forall_mem_cons.2 ⟨subd8_1_4206, List.forall_mem_cons.2 ⟨subd8_1_4207, List.forall_mem_cons.2 ⟨subd8_1_4208, List.forall_mem_cons.2 ⟨subd8_1_4209, List.forall_mem_cons.2 ⟨subd8_1_4210, List.forall_mem_cons.2 ⟨subd8_1_4211, List.forall_mem_cons.2 ⟨subd8_1_4212, List.forall_mem_cons.2 ⟨subd8_1_4213, List.forall_mem_cons.2 ⟨subd8_1_4214, List.forall_mem_cons.2 ⟨subd8_1_4215, List.forall_mem_cons.2 ⟨subd8_1_4216, List.forall_mem_cons.2 ⟨subd8_1_4217, List.forall_mem_cons.2 ⟨subd8_1_4218, List.forall_mem_cons.2 ⟨subd8_1_4219, List.forall_mem_cons.2 ⟨subd8_1_4220, List.forall_mem_cons.2 ⟨subd8_1_4221, List.forall_mem_cons.2 ⟨subd8_1_4222, List.forall_mem_cons.2 ⟨subd8_1_4223, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4224 : subd8_1 [7, 1, 4] = true := by decide +kernel
theorem subd8_1_4225 : subd8_1 [7, 1, 5] = true := by decide +kernel
theorem subd8_1_4226 : subd8_1 [7, 1, 6] = true := by decide +kernel
theorem subd8_1_4227 : subd8_1 [7, 1, 7] = true := by decide +kernel
theorem subd8_1_4228 : subd8_1 [7, 2, -8] = true := by decide +kernel
theorem subd8_1_4229 : subd8_1 [7, 2, -7] = true := by decide +kernel
theorem subd8_1_4230 : subd8_1 [7, 2, -6] = true := by decide +kernel
theorem subd8_1_4231 : subd8_1 [7, 2, -5] = true := by decide +kernel
theorem subd8_1_4232 : subd8_1 [7, 2, -4] = true := by decide +kernel
theorem subd8_1_4233 : subd8_1 [7, 2, -3] = true := by decide +kernel
theorem subd8_1_4234 : subd8_1 [7, 2, -2] = true := by decide +kernel
theorem subd8_1_4235 : subd8_1 [7, 2, -1] = true := by decide +kernel
theorem subd8_1_4236 : subd8_1 [7, 2, 0] = true := by decide +kernel
theorem subd8_1_4237 : subd8_1 [7, 2, 1] = true := by decide +kernel
theorem subd8_1_4238 : subd8_1 [7, 2, 2] = true := by decide +kernel
theorem subd8_1_4239 : subd8_1 [7, 2, 3] = true := by decide +kernel
theorem subd8_1_4240 : subd8_1 [7, 2, 4] = true := by decide +kernel
theorem subd8_1_4241 : subd8_1 [7, 2, 5] = true := by decide +kernel
theorem subd8_1_4242 : subd8_1 [7, 2, 6] = true := by decide +kernel
theorem subd8_1_4243 : subd8_1 [7, 2, 7] = true := by decide +kernel
theorem subd8_1_4244 : subd8_1 [7, 3, -7] = true := by decide +kernel
theorem subd8_1_4245 : subd8_1 [7, 3, -6] = true := by decide +kernel
theorem subd8_1_4246 : subd8_1 [7, 3, -5] = true := by decide +kernel
theorem subd8_1_4247 : subd8_1 [7, 3, -4] = true := by decide +kernel
theorem subd8_1_4248 : subd8_1 [7, 3, -3] = true := by decide +kernel
theorem subd8_1_4249 : subd8_1 [7, 3, -2] = true := by decide +kernel
theorem subd8_1_4250 : subd8_1 [7, 3, -1] = true := by decide +kernel
theorem subd8_1_4251 : subd8_1 [7, 3, 0] = true := by decide +kernel
theorem subd8_1_4252 : subd8_1 [7, 3, 1] = true := by decide +kernel
theorem subd8_1_4253 : subd8_1 [7, 3, 2] = true := by decide +kernel
theorem subd8_1_4254 : subd8_1 [7, 3, 3] = true := by decide +kernel
theorem subd8_1_4255 : subd8_1 [7, 3, 4] = true := by decide +kernel
theorem sbd8_1_132 : ∀ q ∈ blkd8_1_132, subd8_1 q = true := by
  unfold blkd8_1_132
  exact List.forall_mem_cons.2 ⟨subd8_1_4224, List.forall_mem_cons.2 ⟨subd8_1_4225, List.forall_mem_cons.2 ⟨subd8_1_4226, List.forall_mem_cons.2 ⟨subd8_1_4227, List.forall_mem_cons.2 ⟨subd8_1_4228, List.forall_mem_cons.2 ⟨subd8_1_4229, List.forall_mem_cons.2 ⟨subd8_1_4230, List.forall_mem_cons.2 ⟨subd8_1_4231, List.forall_mem_cons.2 ⟨subd8_1_4232, List.forall_mem_cons.2 ⟨subd8_1_4233, List.forall_mem_cons.2 ⟨subd8_1_4234, List.forall_mem_cons.2 ⟨subd8_1_4235, List.forall_mem_cons.2 ⟨subd8_1_4236, List.forall_mem_cons.2 ⟨subd8_1_4237, List.forall_mem_cons.2 ⟨subd8_1_4238, List.forall_mem_cons.2 ⟨subd8_1_4239, List.forall_mem_cons.2 ⟨subd8_1_4240, List.forall_mem_cons.2 ⟨subd8_1_4241, List.forall_mem_cons.2 ⟨subd8_1_4242, List.forall_mem_cons.2 ⟨subd8_1_4243, List.forall_mem_cons.2 ⟨subd8_1_4244, List.forall_mem_cons.2 ⟨subd8_1_4245, List.forall_mem_cons.2 ⟨subd8_1_4246, List.forall_mem_cons.2 ⟨subd8_1_4247, List.forall_mem_cons.2 ⟨subd8_1_4248, List.forall_mem_cons.2 ⟨subd8_1_4249, List.forall_mem_cons.2 ⟨subd8_1_4250, List.forall_mem_cons.2 ⟨subd8_1_4251, List.forall_mem_cons.2 ⟨subd8_1_4252, List.forall_mem_cons.2 ⟨subd8_1_4253, List.forall_mem_cons.2 ⟨subd8_1_4254, List.forall_mem_cons.2 ⟨subd8_1_4255, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4256 : subd8_1 [7, 3, 5] = true := by decide +kernel
theorem subd8_1_4257 : subd8_1 [7, 3, 6] = true := by decide +kernel
theorem subd8_1_4258 : subd8_1 [7, 3, 7] = true := by decide +kernel
theorem subd8_1_4259 : subd8_1 [7, 4] = true := by decide +kernel
theorem subd8_1_4260 : subd8_1 [7, 5] = true := by decide +kernel
theorem subd8_1_4261 : subd8_1 [7, 6] = true := by decide +kernel
theorem subd8_1_4262 : subd8_1 [8, -10] = true := by decide +kernel
theorem subd8_1_4263 : subd8_1 [8, -9] = true := by decide +kernel
theorem subd8_1_4264 : subd8_1 [8, -8] = true := by decide +kernel
theorem subd8_1_4265 : subd8_1 [8, -7] = true := by decide +kernel
theorem subd8_1_4266 : subd8_1 [8, -6] = true := by decide +kernel
theorem subd8_1_4267 : subd8_1 [8, -5, -9] = true := by decide +kernel
theorem subd8_1_4268 : subd8_1 [8, -5, -8] = true := by decide +kernel
theorem subd8_1_4269 : subd8_1 [8, -5, -7] = true := by decide +kernel
theorem subd8_1_4270 : subd8_1 [8, -5, -6] = true := by decide +kernel
theorem subd8_1_4271 : subd8_1 [8, -5, -5] = true := by decide +kernel
theorem subd8_1_4272 : subd8_1 [8, -5, -4] = true := by decide +kernel
theorem subd8_1_4273 : subd8_1 [8, -5, -3] = true := by decide +kernel
theorem subd8_1_4274 : subd8_1 [8, -5, -2] = true := by decide +kernel
theorem subd8_1_4275 : subd8_1 [8, -5, -1] = true := by decide +kernel
theorem subd8_1_4276 : subd8_1 [8, -5, 0] = true := by decide +kernel
theorem subd8_1_4277 : subd8_1 [8, -5, 1] = true := by decide +kernel
theorem subd8_1_4278 : subd8_1 [8, -5, 2] = true := by decide +kernel
theorem subd8_1_4279 : subd8_1 [8, -5, 3] = true := by decide +kernel
theorem subd8_1_4280 : subd8_1 [8, -5, 4] = true := by decide +kernel
theorem subd8_1_4281 : subd8_1 [8, -5, 5] = true := by decide +kernel
theorem subd8_1_4282 : subd8_1 [8, -4, -9] = true := by decide +kernel
theorem subd8_1_4283 : subd8_1 [8, -4, -8] = true := by decide +kernel
theorem subd8_1_4284 : subd8_1 [8, -4, -7] = true := by decide +kernel
theorem subd8_1_4285 : subd8_1 [8, -4, -6] = true := by decide +kernel
theorem subd8_1_4286 : subd8_1 [8, -4, -5] = true := by decide +kernel
theorem subd8_1_4287 : subd8_1 [8, -4, -4] = true := by decide +kernel
theorem sbd8_1_133 : ∀ q ∈ blkd8_1_133, subd8_1 q = true := by
  unfold blkd8_1_133
  exact List.forall_mem_cons.2 ⟨subd8_1_4256, List.forall_mem_cons.2 ⟨subd8_1_4257, List.forall_mem_cons.2 ⟨subd8_1_4258, List.forall_mem_cons.2 ⟨subd8_1_4259, List.forall_mem_cons.2 ⟨subd8_1_4260, List.forall_mem_cons.2 ⟨subd8_1_4261, List.forall_mem_cons.2 ⟨subd8_1_4262, List.forall_mem_cons.2 ⟨subd8_1_4263, List.forall_mem_cons.2 ⟨subd8_1_4264, List.forall_mem_cons.2 ⟨subd8_1_4265, List.forall_mem_cons.2 ⟨subd8_1_4266, List.forall_mem_cons.2 ⟨subd8_1_4267, List.forall_mem_cons.2 ⟨subd8_1_4268, List.forall_mem_cons.2 ⟨subd8_1_4269, List.forall_mem_cons.2 ⟨subd8_1_4270, List.forall_mem_cons.2 ⟨subd8_1_4271, List.forall_mem_cons.2 ⟨subd8_1_4272, List.forall_mem_cons.2 ⟨subd8_1_4273, List.forall_mem_cons.2 ⟨subd8_1_4274, List.forall_mem_cons.2 ⟨subd8_1_4275, List.forall_mem_cons.2 ⟨subd8_1_4276, List.forall_mem_cons.2 ⟨subd8_1_4277, List.forall_mem_cons.2 ⟨subd8_1_4278, List.forall_mem_cons.2 ⟨subd8_1_4279, List.forall_mem_cons.2 ⟨subd8_1_4280, List.forall_mem_cons.2 ⟨subd8_1_4281, List.forall_mem_cons.2 ⟨subd8_1_4282, List.forall_mem_cons.2 ⟨subd8_1_4283, List.forall_mem_cons.2 ⟨subd8_1_4284, List.forall_mem_cons.2 ⟨subd8_1_4285, List.forall_mem_cons.2 ⟨subd8_1_4286, List.forall_mem_cons.2 ⟨subd8_1_4287, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4288 : subd8_1 [8, -4, -3] = true := by decide +kernel
theorem subd8_1_4289 : subd8_1 [8, -4, -2] = true := by decide +kernel
theorem subd8_1_4290 : subd8_1 [8, -4, -1] = true := by decide +kernel
theorem subd8_1_4291 : subd8_1 [8, -4, 0] = true := by decide +kernel
theorem subd8_1_4292 : subd8_1 [8, -4, 1] = true := by decide +kernel
theorem subd8_1_4293 : subd8_1 [8, -4, 2] = true := by decide +kernel
theorem subd8_1_4294 : subd8_1 [8, -4, 3] = true := by decide +kernel
theorem subd8_1_4295 : subd8_1 [8, -4, 4] = true := by decide +kernel
theorem subd8_1_4296 : subd8_1 [8, -4, 5] = true := by decide +kernel
theorem subd8_1_4297 : subd8_1 [8, -3, -9] = true := by decide +kernel
theorem subd8_1_4298 : subd8_1 [8, -3, -8] = true := by decide +kernel
theorem subd8_1_4299 : subd8_1 [8, -3, -7] = true := by decide +kernel
theorem subd8_1_4300 : subd8_1 [8, -3, -6] = true := by decide +kernel
theorem subd8_1_4301 : subd8_1 [8, -3, -5] = true := by decide +kernel
theorem subd8_1_4302 : subd8_1 [8, -3, -4] = true := by decide +kernel
theorem subd8_1_4303 : subd8_1 [8, -3, -3] = true := by decide +kernel
theorem subd8_1_4304 : subd8_1 [8, -3, -2] = true := by decide +kernel
theorem subd8_1_4305 : subd8_1 [8, -3, -1] = true := by decide +kernel
theorem subd8_1_4306 : subd8_1 [8, -3, 0] = true := by decide +kernel
theorem subd8_1_4307 : subd8_1 [8, -3, 1] = true := by decide +kernel
theorem subd8_1_4308 : subd8_1 [8, -3, 2] = true := by decide +kernel
theorem subd8_1_4309 : subd8_1 [8, -3, 3] = true := by decide +kernel
theorem subd8_1_4310 : subd8_1 [8, -3, 4] = true := by decide +kernel
theorem subd8_1_4311 : subd8_1 [8, -3, 5] = true := by decide +kernel
theorem subd8_1_4312 : subd8_1 [8, -3, 6] = true := by decide +kernel
theorem subd8_1_4313 : subd8_1 [8, -2, -9] = true := by decide +kernel
theorem subd8_1_4314 : subd8_1 [8, -2, -8] = true := by decide +kernel
theorem subd8_1_4315 : subd8_1 [8, -2, -7] = true := by decide +kernel
theorem subd8_1_4316 : subd8_1 [8, -2, -6] = true := by decide +kernel
theorem subd8_1_4317 : subd8_1 [8, -2, -5] = true := by decide +kernel
theorem subd8_1_4318 : subd8_1 [8, -2, -4] = true := by decide +kernel
theorem subd8_1_4319 : subd8_1 [8, -2, -3] = true := by decide +kernel
theorem sbd8_1_134 : ∀ q ∈ blkd8_1_134, subd8_1 q = true := by
  unfold blkd8_1_134
  exact List.forall_mem_cons.2 ⟨subd8_1_4288, List.forall_mem_cons.2 ⟨subd8_1_4289, List.forall_mem_cons.2 ⟨subd8_1_4290, List.forall_mem_cons.2 ⟨subd8_1_4291, List.forall_mem_cons.2 ⟨subd8_1_4292, List.forall_mem_cons.2 ⟨subd8_1_4293, List.forall_mem_cons.2 ⟨subd8_1_4294, List.forall_mem_cons.2 ⟨subd8_1_4295, List.forall_mem_cons.2 ⟨subd8_1_4296, List.forall_mem_cons.2 ⟨subd8_1_4297, List.forall_mem_cons.2 ⟨subd8_1_4298, List.forall_mem_cons.2 ⟨subd8_1_4299, List.forall_mem_cons.2 ⟨subd8_1_4300, List.forall_mem_cons.2 ⟨subd8_1_4301, List.forall_mem_cons.2 ⟨subd8_1_4302, List.forall_mem_cons.2 ⟨subd8_1_4303, List.forall_mem_cons.2 ⟨subd8_1_4304, List.forall_mem_cons.2 ⟨subd8_1_4305, List.forall_mem_cons.2 ⟨subd8_1_4306, List.forall_mem_cons.2 ⟨subd8_1_4307, List.forall_mem_cons.2 ⟨subd8_1_4308, List.forall_mem_cons.2 ⟨subd8_1_4309, List.forall_mem_cons.2 ⟨subd8_1_4310, List.forall_mem_cons.2 ⟨subd8_1_4311, List.forall_mem_cons.2 ⟨subd8_1_4312, List.forall_mem_cons.2 ⟨subd8_1_4313, List.forall_mem_cons.2 ⟨subd8_1_4314, List.forall_mem_cons.2 ⟨subd8_1_4315, List.forall_mem_cons.2 ⟨subd8_1_4316, List.forall_mem_cons.2 ⟨subd8_1_4317, List.forall_mem_cons.2 ⟨subd8_1_4318, List.forall_mem_cons.2 ⟨subd8_1_4319, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_1_4320 : subd8_1 [8, -2, -2] = true := by decide +kernel
theorem subd8_1_4321 : subd8_1 [8, -2, -1] = true := by decide +kernel
theorem subd8_1_4322 : subd8_1 [8, -2, 0] = true := by decide +kernel
theorem subd8_1_4323 : subd8_1 [8, -2, 1] = true := by decide +kernel
theorem subd8_1_4324 : subd8_1 [8, -2, 2] = true := by decide +kernel
theorem subd8_1_4325 : subd8_1 [8, -2, 3] = true := by decide +kernel
theorem subd8_1_4326 : subd8_1 [8, -2, 4] = true := by decide +kernel
theorem subd8_1_4327 : subd8_1 [8, -2, 5] = true := by decide +kernel
theorem subd8_1_4328 : subd8_1 [8, -2, 6] = true := by decide +kernel
theorem subd8_1_4329 : subd8_1 [8, -1, -9] = true := by decide +kernel
theorem subd8_1_4330 : subd8_1 [8, -1, -8] = true := by decide +kernel
theorem subd8_1_4331 : subd8_1 [8, -1, -7] = true := by decide +kernel
theorem subd8_1_4332 : subd8_1 [8, -1, -6] = true := by decide +kernel
theorem subd8_1_4333 : subd8_1 [8, -1, -5] = true := by decide +kernel
theorem subd8_1_4334 : subd8_1 [8, -1, -4] = true := by decide +kernel
theorem subd8_1_4335 : subd8_1 [8, -1, -3] = true := by decide +kernel
theorem subd8_1_4336 : subd8_1 [8, -1, -2] = true := by decide +kernel
theorem subd8_1_4337 : subd8_1 [8, -1, -1] = true := by decide +kernel
theorem subd8_1_4338 : subd8_1 [8, -1, 0] = true := by decide +kernel
theorem subd8_1_4339 : subd8_1 [8, -1, 1] = true := by decide +kernel
theorem subd8_1_4340 : subd8_1 [8, -1, 2] = true := by decide +kernel
theorem subd8_1_4341 : subd8_1 [8, -1, 3] = true := by decide +kernel
theorem subd8_1_4342 : subd8_1 [8, -1, 4] = true := by decide +kernel
theorem subd8_1_4343 : subd8_1 [8, -1, 5] = true := by decide +kernel
theorem subd8_1_4344 : subd8_1 [8, -1, 6] = true := by decide +kernel
theorem subd8_1_4345 : subd8_1 [8, 0, -8] = true := by decide +kernel
theorem subd8_1_4346 : subd8_1 [8, 0, -7] = true := by decide +kernel
theorem subd8_1_4347 : subd8_1 [8, 0, -6] = true := by decide +kernel
theorem subd8_1_4348 : subd8_1 [8, 0, -5] = true := by decide +kernel
theorem subd8_1_4349 : subd8_1 [8, 0, -4] = true := by decide +kernel
theorem subd8_1_4350 : subd8_1 [8, 0, -3] = true := by decide +kernel
theorem subd8_1_4351 : subd8_1 [8, 0, -2] = true := by decide +kernel
theorem sbd8_1_135 : ∀ q ∈ blkd8_1_135, subd8_1 q = true := by
  unfold blkd8_1_135
  exact List.forall_mem_cons.2 ⟨subd8_1_4320, List.forall_mem_cons.2 ⟨subd8_1_4321, List.forall_mem_cons.2 ⟨subd8_1_4322, List.forall_mem_cons.2 ⟨subd8_1_4323, List.forall_mem_cons.2 ⟨subd8_1_4324, List.forall_mem_cons.2 ⟨subd8_1_4325, List.forall_mem_cons.2 ⟨subd8_1_4326, List.forall_mem_cons.2 ⟨subd8_1_4327, List.forall_mem_cons.2 ⟨subd8_1_4328, List.forall_mem_cons.2 ⟨subd8_1_4329, List.forall_mem_cons.2 ⟨subd8_1_4330, List.forall_mem_cons.2 ⟨subd8_1_4331, List.forall_mem_cons.2 ⟨subd8_1_4332, List.forall_mem_cons.2 ⟨subd8_1_4333, List.forall_mem_cons.2 ⟨subd8_1_4334, List.forall_mem_cons.2 ⟨subd8_1_4335, List.forall_mem_cons.2 ⟨subd8_1_4336, List.forall_mem_cons.2 ⟨subd8_1_4337, List.forall_mem_cons.2 ⟨subd8_1_4338, List.forall_mem_cons.2 ⟨subd8_1_4339, List.forall_mem_cons.2 ⟨subd8_1_4340, List.forall_mem_cons.2 ⟨subd8_1_4341, List.forall_mem_cons.2 ⟨subd8_1_4342, List.forall_mem_cons.2 ⟨subd8_1_4343, List.forall_mem_cons.2 ⟨subd8_1_4344, List.forall_mem_cons.2 ⟨subd8_1_4345, List.forall_mem_cons.2 ⟨subd8_1_4346, List.forall_mem_cons.2 ⟨subd8_1_4347, List.forall_mem_cons.2 ⟨subd8_1_4348, List.forall_mem_cons.2 ⟨subd8_1_4349, List.forall_mem_cons.2 ⟨subd8_1_4350, List.forall_mem_cons.2 ⟨subd8_1_4351, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
