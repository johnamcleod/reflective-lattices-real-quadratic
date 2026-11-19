import ReflectZphi.Data.Cert5.C093.Base

namespace ReflectZphi.Data.Cert5.C093

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd8_0_864 : subd8_0 [2, 2, 6] = true := by decide +kernel
theorem subd8_0_865 : subd8_0 [2, 2, 7] = true := by decide +kernel
theorem subd8_0_866 : subd8_0 [2, 2, 8] = true := by decide +kernel
theorem subd8_0_867 : subd8_0 [2, 3, -8] = true := by decide +kernel
theorem subd8_0_868 : subd8_0 [2, 3, -7] = true := by decide +kernel
theorem subd8_0_869 : subd8_0 [2, 3, -6] = true := by decide +kernel
theorem subd8_0_870 : subd8_0 [2, 3, -5] = true := by decide +kernel
theorem subd8_0_871 : subd8_0 [2, 3, -4] = true := by decide +kernel
theorem subd8_0_872 : subd8_0 [2, 3, -3] = true := by decide +kernel
theorem subd8_0_873 : subd8_0 [2, 3, -2] = true := by decide +kernel
theorem subd8_0_874 : subd8_0 [2, 3, -1] = true := by decide +kernel
theorem subd8_0_875 : subd8_0 [2, 3, 0] = true := by decide +kernel
theorem subd8_0_876 : subd8_0 [2, 3, 1] = true := by decide +kernel
theorem subd8_0_877 : subd8_0 [2, 3, 2] = true := by decide +kernel
theorem subd8_0_878 : subd8_0 [2, 3, 3] = true := by decide +kernel
theorem subd8_0_879 : subd8_0 [2, 3, 4] = true := by decide +kernel
theorem subd8_0_880 : subd8_0 [2, 3, 5] = true := by decide +kernel
theorem subd8_0_881 : subd8_0 [2, 3, 6] = true := by decide +kernel
theorem subd8_0_882 : subd8_0 [2, 3, 7] = true := by decide +kernel
theorem subd8_0_883 : subd8_0 [2, 4, -7] = true := by decide +kernel
theorem subd8_0_884 : subd8_0 [2, 4, -6] = true := by decide +kernel
theorem subd8_0_885 : subd8_0 [2, 4, -5] = true := by decide +kernel
theorem subd8_0_886 : subd8_0 [2, 4, -4] = true := by decide +kernel
theorem subd8_0_887 : subd8_0 [2, 4, -3] = true := by decide +kernel
theorem subd8_0_888 : subd8_0 [2, 4, -2] = true := by decide +kernel
theorem subd8_0_889 : subd8_0 [2, 4, -1] = true := by decide +kernel
theorem subd8_0_890 : subd8_0 [2, 4, 0] = true := by decide +kernel
theorem subd8_0_891 : subd8_0 [2, 4, 1] = true := by decide +kernel
theorem subd8_0_892 : subd8_0 [2, 4, 2] = true := by decide +kernel
theorem subd8_0_893 : subd8_0 [2, 4, 3] = true := by decide +kernel
theorem subd8_0_894 : subd8_0 [2, 4, 4] = true := by decide +kernel
theorem subd8_0_895 : subd8_0 [2, 4, 5] = true := by decide +kernel
theorem sbd8_0_27 : ∀ q ∈ blkd8_0_27, subd8_0 q = true := by
  unfold blkd8_0_27
  exact List.forall_mem_cons.2 ⟨subd8_0_864, List.forall_mem_cons.2 ⟨subd8_0_865, List.forall_mem_cons.2 ⟨subd8_0_866, List.forall_mem_cons.2 ⟨subd8_0_867, List.forall_mem_cons.2 ⟨subd8_0_868, List.forall_mem_cons.2 ⟨subd8_0_869, List.forall_mem_cons.2 ⟨subd8_0_870, List.forall_mem_cons.2 ⟨subd8_0_871, List.forall_mem_cons.2 ⟨subd8_0_872, List.forall_mem_cons.2 ⟨subd8_0_873, List.forall_mem_cons.2 ⟨subd8_0_874, List.forall_mem_cons.2 ⟨subd8_0_875, List.forall_mem_cons.2 ⟨subd8_0_876, List.forall_mem_cons.2 ⟨subd8_0_877, List.forall_mem_cons.2 ⟨subd8_0_878, List.forall_mem_cons.2 ⟨subd8_0_879, List.forall_mem_cons.2 ⟨subd8_0_880, List.forall_mem_cons.2 ⟨subd8_0_881, List.forall_mem_cons.2 ⟨subd8_0_882, List.forall_mem_cons.2 ⟨subd8_0_883, List.forall_mem_cons.2 ⟨subd8_0_884, List.forall_mem_cons.2 ⟨subd8_0_885, List.forall_mem_cons.2 ⟨subd8_0_886, List.forall_mem_cons.2 ⟨subd8_0_887, List.forall_mem_cons.2 ⟨subd8_0_888, List.forall_mem_cons.2 ⟨subd8_0_889, List.forall_mem_cons.2 ⟨subd8_0_890, List.forall_mem_cons.2 ⟨subd8_0_891, List.forall_mem_cons.2 ⟨subd8_0_892, List.forall_mem_cons.2 ⟨subd8_0_893, List.forall_mem_cons.2 ⟨subd8_0_894, List.forall_mem_cons.2 ⟨subd8_0_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_896 : subd8_0 [2, 4, 6] = true := by decide +kernel
theorem subd8_0_897 : subd8_0 [2, 4, 7] = true := by decide +kernel
theorem subd8_0_898 : subd8_0 [2, 5] = true := by decide +kernel
theorem subd8_0_899 : subd8_0 [2, 6] = true := by decide +kernel
theorem subd8_0_900 : subd8_0 [3, -5] = true := by decide +kernel
theorem subd8_0_901 : subd8_0 [3, -4] = true := by decide +kernel
theorem subd8_0_902 : subd8_0 [3, -3] = true := by decide +kernel
theorem subd8_0_903 : subd8_0 [3, -2, -8] = true := by decide +kernel
theorem subd8_0_904 : subd8_0 [3, -2, -7] = true := by decide +kernel
theorem subd8_0_905 : subd8_0 [3, -2, -6] = true := by decide +kernel
theorem subd8_0_906 : subd8_0 [3, -2, -5] = true := by decide +kernel
theorem subd8_0_907 : subd8_0 [3, -2, -4] = true := by decide +kernel
theorem subd8_0_908 : subd8_0 [3, -2, -3] = true := by decide +kernel
theorem subd8_0_909 : subd8_0 [3, -2, -2] = true := by decide +kernel
theorem subd8_0_910 : subd8_0 [3, -2, -1] = true := by decide +kernel
theorem subd8_0_911 : subd8_0 [3, -2, 0] = true := by decide +kernel
theorem subd8_0_912 : subd8_0 [3, -2, 1] = true := by decide +kernel
theorem subd8_0_913 : subd8_0 [3, -2, 2] = true := by decide +kernel
theorem subd8_0_914 : subd8_0 [3, -2, 3] = true := by decide +kernel
theorem subd8_0_915 : subd8_0 [3, -2, 4] = true := by decide +kernel
theorem subd8_0_916 : subd8_0 [3, -2, 5] = true := by decide +kernel
theorem subd8_0_917 : subd8_0 [3, -1, -8] = true := by decide +kernel
theorem subd8_0_918 : subd8_0 [3, -1, -7] = true := by decide +kernel
theorem subd8_0_919 : subd8_0 [3, -1, -6] = true := by decide +kernel
theorem subd8_0_920 : subd8_0 [3, -1, -5] = true := by decide +kernel
theorem subd8_0_921 : subd8_0 [3, -1, -4] = true := by decide +kernel
theorem subd8_0_922 : subd8_0 [3, -1, -3] = true := by decide +kernel
theorem subd8_0_923 : subd8_0 [3, -1, -2] = true := by decide +kernel
theorem subd8_0_924 : subd8_0 [3, -1, -1] = true := by decide +kernel
theorem subd8_0_925 : subd8_0 [3, -1, 0] = true := by decide +kernel
theorem subd8_0_926 : subd8_0 [3, -1, 1] = true := by decide +kernel
theorem subd8_0_927 : subd8_0 [3, -1, 2] = true := by decide +kernel
theorem sbd8_0_28 : ∀ q ∈ blkd8_0_28, subd8_0 q = true := by
  unfold blkd8_0_28
  exact List.forall_mem_cons.2 ⟨subd8_0_896, List.forall_mem_cons.2 ⟨subd8_0_897, List.forall_mem_cons.2 ⟨subd8_0_898, List.forall_mem_cons.2 ⟨subd8_0_899, List.forall_mem_cons.2 ⟨subd8_0_900, List.forall_mem_cons.2 ⟨subd8_0_901, List.forall_mem_cons.2 ⟨subd8_0_902, List.forall_mem_cons.2 ⟨subd8_0_903, List.forall_mem_cons.2 ⟨subd8_0_904, List.forall_mem_cons.2 ⟨subd8_0_905, List.forall_mem_cons.2 ⟨subd8_0_906, List.forall_mem_cons.2 ⟨subd8_0_907, List.forall_mem_cons.2 ⟨subd8_0_908, List.forall_mem_cons.2 ⟨subd8_0_909, List.forall_mem_cons.2 ⟨subd8_0_910, List.forall_mem_cons.2 ⟨subd8_0_911, List.forall_mem_cons.2 ⟨subd8_0_912, List.forall_mem_cons.2 ⟨subd8_0_913, List.forall_mem_cons.2 ⟨subd8_0_914, List.forall_mem_cons.2 ⟨subd8_0_915, List.forall_mem_cons.2 ⟨subd8_0_916, List.forall_mem_cons.2 ⟨subd8_0_917, List.forall_mem_cons.2 ⟨subd8_0_918, List.forall_mem_cons.2 ⟨subd8_0_919, List.forall_mem_cons.2 ⟨subd8_0_920, List.forall_mem_cons.2 ⟨subd8_0_921, List.forall_mem_cons.2 ⟨subd8_0_922, List.forall_mem_cons.2 ⟨subd8_0_923, List.forall_mem_cons.2 ⟨subd8_0_924, List.forall_mem_cons.2 ⟨subd8_0_925, List.forall_mem_cons.2 ⟨subd8_0_926, List.forall_mem_cons.2 ⟨subd8_0_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_928 : subd8_0 [3, -1, 3] = true := by decide +kernel
theorem subd8_0_929 : subd8_0 [3, -1, 4] = true := by decide +kernel
theorem subd8_0_930 : subd8_0 [3, -1, 5] = true := by decide +kernel
theorem subd8_0_931 : subd8_0 [3, -1, 6] = true := by decide +kernel
theorem subd8_0_932 : subd8_0 [3, 0, -8] = true := by decide +kernel
theorem subd8_0_933 : subd8_0 [3, 0, -7] = true := by decide +kernel
theorem subd8_0_934 : subd8_0 [3, 0, -6] = true := by decide +kernel
theorem subd8_0_935 : subd8_0 [3, 0, -5] = true := by decide +kernel
theorem subd8_0_936 : subd8_0 [3, 0, -4] = true := by decide +kernel
theorem subd8_0_937 : subd8_0 [3, 0, -3] = true := by decide +kernel
theorem subd8_0_938 : subd8_0 [3, 0, -2] = true := by decide +kernel
theorem subd8_0_939 : subd8_0 [3, 0, -1] = true := by decide +kernel
theorem subd8_0_940 : subd8_0 [3, 0, 0] = true := by decide +kernel
theorem subd8_0_941 : subd8_0 [3, 0, 1] = true := by decide +kernel
theorem subd8_0_942 : subd8_0 [3, 0, 2] = true := by decide +kernel
theorem subd8_0_943 : subd8_0 [3, 0, 3] = true := by decide +kernel
theorem subd8_0_944 : subd8_0 [3, 0, 4] = true := by decide +kernel
theorem subd8_0_945 : subd8_0 [3, 0, 5] = true := by decide +kernel
theorem subd8_0_946 : subd8_0 [3, 0, 6] = true := by decide +kernel
theorem subd8_0_947 : subd8_0 [3, 0, 7] = true := by decide +kernel
theorem subd8_0_948 : subd8_0 [3, 1, -8] = true := by decide +kernel
theorem subd8_0_949 : subd8_0 [3, 1, -7] = true := by decide +kernel
theorem subd8_0_950 : subd8_0 [3, 1, -6] = true := by decide +kernel
theorem subd8_0_951 : subd8_0 [3, 1, -5] = true := by decide +kernel
theorem subd8_0_952 : subd8_0 [3, 1, -4] = true := by decide +kernel
theorem subd8_0_953 : subd8_0 [3, 1, -3] = true := by decide +kernel
theorem subd8_0_954 : subd8_0 [3, 1, -2] = true := by decide +kernel
theorem subd8_0_955 : subd8_0 [3, 1, -1] = true := by decide +kernel
theorem subd8_0_956 : subd8_0 [3, 1, 0] = true := by decide +kernel
theorem subd8_0_957 : subd8_0 [3, 1, 1] = true := by decide +kernel
theorem subd8_0_958 : subd8_0 [3, 1, 2] = true := by decide +kernel
theorem subd8_0_959 : subd8_0 [3, 1, 3] = true := by decide +kernel
theorem sbd8_0_29 : ∀ q ∈ blkd8_0_29, subd8_0 q = true := by
  unfold blkd8_0_29
  exact List.forall_mem_cons.2 ⟨subd8_0_928, List.forall_mem_cons.2 ⟨subd8_0_929, List.forall_mem_cons.2 ⟨subd8_0_930, List.forall_mem_cons.2 ⟨subd8_0_931, List.forall_mem_cons.2 ⟨subd8_0_932, List.forall_mem_cons.2 ⟨subd8_0_933, List.forall_mem_cons.2 ⟨subd8_0_934, List.forall_mem_cons.2 ⟨subd8_0_935, List.forall_mem_cons.2 ⟨subd8_0_936, List.forall_mem_cons.2 ⟨subd8_0_937, List.forall_mem_cons.2 ⟨subd8_0_938, List.forall_mem_cons.2 ⟨subd8_0_939, List.forall_mem_cons.2 ⟨subd8_0_940, List.forall_mem_cons.2 ⟨subd8_0_941, List.forall_mem_cons.2 ⟨subd8_0_942, List.forall_mem_cons.2 ⟨subd8_0_943, List.forall_mem_cons.2 ⟨subd8_0_944, List.forall_mem_cons.2 ⟨subd8_0_945, List.forall_mem_cons.2 ⟨subd8_0_946, List.forall_mem_cons.2 ⟨subd8_0_947, List.forall_mem_cons.2 ⟨subd8_0_948, List.forall_mem_cons.2 ⟨subd8_0_949, List.forall_mem_cons.2 ⟨subd8_0_950, List.forall_mem_cons.2 ⟨subd8_0_951, List.forall_mem_cons.2 ⟨subd8_0_952, List.forall_mem_cons.2 ⟨subd8_0_953, List.forall_mem_cons.2 ⟨subd8_0_954, List.forall_mem_cons.2 ⟨subd8_0_955, List.forall_mem_cons.2 ⟨subd8_0_956, List.forall_mem_cons.2 ⟨subd8_0_957, List.forall_mem_cons.2 ⟨subd8_0_958, List.forall_mem_cons.2 ⟨subd8_0_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_960 : subd8_0 [3, 1, 4] = true := by decide +kernel
theorem subd8_0_961 : subd8_0 [3, 1, 5] = true := by decide +kernel
theorem subd8_0_962 : subd8_0 [3, 1, 6] = true := by decide +kernel
theorem subd8_0_963 : subd8_0 [3, 1, 7] = true := by decide +kernel
theorem subd8_0_964 : subd8_0 [3, 2, -8] = true := by decide +kernel
theorem subd8_0_965 : subd8_0 [3, 2, -7] = true := by decide +kernel
theorem subd8_0_966 : subd8_0 [3, 2, -6] = true := by decide +kernel
theorem subd8_0_967 : subd8_0 [3, 2, -5] = true := by decide +kernel
theorem subd8_0_968 : subd8_0 [3, 2, -4] = true := by decide +kernel
theorem subd8_0_969 : subd8_0 [3, 2, -3] = true := by decide +kernel
theorem subd8_0_970 : subd8_0 [3, 2, -2] = true := by decide +kernel
theorem subd8_0_971 : subd8_0 [3, 2, -1] = true := by decide +kernel
theorem subd8_0_972 : subd8_0 [3, 2, 0] = true := by decide +kernel
theorem subd8_0_973 : subd8_0 [3, 2, 1] = true := by decide +kernel
theorem subd8_0_974 : subd8_0 [3, 2, 2] = true := by decide +kernel
theorem subd8_0_975 : subd8_0 [3, 2, 3] = true := by decide +kernel
theorem subd8_0_976 : subd8_0 [3, 2, 4] = true := by decide +kernel
theorem subd8_0_977 : subd8_0 [3, 2, 5] = true := by decide +kernel
theorem subd8_0_978 : subd8_0 [3, 2, 6] = true := by decide +kernel
theorem subd8_0_979 : subd8_0 [3, 2, 7] = true := by decide +kernel
theorem subd8_0_980 : subd8_0 [3, 3, -8] = true := by decide +kernel
theorem subd8_0_981 : subd8_0 [3, 3, -7] = true := by decide +kernel
theorem subd8_0_982 : subd8_0 [3, 3, -6] = true := by decide +kernel
theorem subd8_0_983 : subd8_0 [3, 3, -5] = true := by decide +kernel
theorem subd8_0_984 : subd8_0 [3, 3, -4] = true := by decide +kernel
theorem subd8_0_985 : subd8_0 [3, 3, -3] = true := by decide +kernel
theorem subd8_0_986 : subd8_0 [3, 3, -2] = true := by decide +kernel
theorem subd8_0_987 : subd8_0 [3, 3, -1] = true := by decide +kernel
theorem subd8_0_988 : subd8_0 [3, 3, 0] = true := by decide +kernel
theorem subd8_0_989 : subd8_0 [3, 3, 1] = true := by decide +kernel
theorem subd8_0_990 : subd8_0 [3, 3, 2] = true := by decide +kernel
theorem subd8_0_991 : subd8_0 [3, 3, 3] = true := by decide +kernel
theorem sbd8_0_30 : ∀ q ∈ blkd8_0_30, subd8_0 q = true := by
  unfold blkd8_0_30
  exact List.forall_mem_cons.2 ⟨subd8_0_960, List.forall_mem_cons.2 ⟨subd8_0_961, List.forall_mem_cons.2 ⟨subd8_0_962, List.forall_mem_cons.2 ⟨subd8_0_963, List.forall_mem_cons.2 ⟨subd8_0_964, List.forall_mem_cons.2 ⟨subd8_0_965, List.forall_mem_cons.2 ⟨subd8_0_966, List.forall_mem_cons.2 ⟨subd8_0_967, List.forall_mem_cons.2 ⟨subd8_0_968, List.forall_mem_cons.2 ⟨subd8_0_969, List.forall_mem_cons.2 ⟨subd8_0_970, List.forall_mem_cons.2 ⟨subd8_0_971, List.forall_mem_cons.2 ⟨subd8_0_972, List.forall_mem_cons.2 ⟨subd8_0_973, List.forall_mem_cons.2 ⟨subd8_0_974, List.forall_mem_cons.2 ⟨subd8_0_975, List.forall_mem_cons.2 ⟨subd8_0_976, List.forall_mem_cons.2 ⟨subd8_0_977, List.forall_mem_cons.2 ⟨subd8_0_978, List.forall_mem_cons.2 ⟨subd8_0_979, List.forall_mem_cons.2 ⟨subd8_0_980, List.forall_mem_cons.2 ⟨subd8_0_981, List.forall_mem_cons.2 ⟨subd8_0_982, List.forall_mem_cons.2 ⟨subd8_0_983, List.forall_mem_cons.2 ⟨subd8_0_984, List.forall_mem_cons.2 ⟨subd8_0_985, List.forall_mem_cons.2 ⟨subd8_0_986, List.forall_mem_cons.2 ⟨subd8_0_987, List.forall_mem_cons.2 ⟨subd8_0_988, List.forall_mem_cons.2 ⟨subd8_0_989, List.forall_mem_cons.2 ⟨subd8_0_990, List.forall_mem_cons.2 ⟨subd8_0_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_992 : subd8_0 [3, 3, 4] = true := by decide +kernel
theorem subd8_0_993 : subd8_0 [3, 3, 5] = true := by decide +kernel
theorem subd8_0_994 : subd8_0 [3, 3, 6] = true := by decide +kernel
theorem subd8_0_995 : subd8_0 [3, 3, 7] = true := by decide +kernel
theorem subd8_0_996 : subd8_0 [3, 4, -7] = true := by decide +kernel
theorem subd8_0_997 : subd8_0 [3, 4, -6] = true := by decide +kernel
theorem subd8_0_998 : subd8_0 [3, 4, -5] = true := by decide +kernel
theorem subd8_0_999 : subd8_0 [3, 4, -4] = true := by decide +kernel
theorem subd8_0_1000 : subd8_0 [3, 4, -3] = true := by decide +kernel
theorem subd8_0_1001 : subd8_0 [3, 4, -2] = true := by decide +kernel
theorem subd8_0_1002 : subd8_0 [3, 4, -1] = true := by decide +kernel
theorem subd8_0_1003 : subd8_0 [3, 4, 0] = true := by decide +kernel
theorem subd8_0_1004 : subd8_0 [3, 4, 1] = true := by decide +kernel
theorem subd8_0_1005 : subd8_0 [3, 4, 2] = true := by decide +kernel
theorem subd8_0_1006 : subd8_0 [3, 4, 3] = true := by decide +kernel
theorem subd8_0_1007 : subd8_0 [3, 4, 4] = true := by decide +kernel
theorem subd8_0_1008 : subd8_0 [3, 4, 5] = true := by decide +kernel
theorem subd8_0_1009 : subd8_0 [3, 4, 6] = true := by decide +kernel
theorem subd8_0_1010 : subd8_0 [3, 5] = true := by decide +kernel
theorem subd8_0_1011 : subd8_0 [3, 6] = true := by decide +kernel
theorem subd8_0_1012 : subd8_0 [4, -4] = true := by decide +kernel
theorem subd8_0_1013 : subd8_0 [4, -3] = true := by decide +kernel
theorem subd8_0_1014 : subd8_0 [4, -2] = true := by decide +kernel
theorem subd8_0_1015 : subd8_0 [4, -1] = true := by decide +kernel
theorem subd8_0_1016 : subd8_0 [4, 0] = true := by decide +kernel
theorem subd8_0_1017 : subd8_0 [4, 1, -7] = true := by decide +kernel
theorem subd8_0_1018 : subd8_0 [4, 1, -6] = true := by decide +kernel
theorem subd8_0_1019 : subd8_0 [4, 1, -5] = true := by decide +kernel
theorem subd8_0_1020 : subd8_0 [4, 1, -4] = true := by decide +kernel
theorem subd8_0_1021 : subd8_0 [4, 1, -3] = true := by decide +kernel
theorem subd8_0_1022 : subd8_0 [4, 1, -2] = true := by decide +kernel
theorem subd8_0_1023 : subd8_0 [4, 1, -1] = true := by decide +kernel
theorem sbd8_0_31 : ∀ q ∈ blkd8_0_31, subd8_0 q = true := by
  unfold blkd8_0_31
  exact List.forall_mem_cons.2 ⟨subd8_0_992, List.forall_mem_cons.2 ⟨subd8_0_993, List.forall_mem_cons.2 ⟨subd8_0_994, List.forall_mem_cons.2 ⟨subd8_0_995, List.forall_mem_cons.2 ⟨subd8_0_996, List.forall_mem_cons.2 ⟨subd8_0_997, List.forall_mem_cons.2 ⟨subd8_0_998, List.forall_mem_cons.2 ⟨subd8_0_999, List.forall_mem_cons.2 ⟨subd8_0_1000, List.forall_mem_cons.2 ⟨subd8_0_1001, List.forall_mem_cons.2 ⟨subd8_0_1002, List.forall_mem_cons.2 ⟨subd8_0_1003, List.forall_mem_cons.2 ⟨subd8_0_1004, List.forall_mem_cons.2 ⟨subd8_0_1005, List.forall_mem_cons.2 ⟨subd8_0_1006, List.forall_mem_cons.2 ⟨subd8_0_1007, List.forall_mem_cons.2 ⟨subd8_0_1008, List.forall_mem_cons.2 ⟨subd8_0_1009, List.forall_mem_cons.2 ⟨subd8_0_1010, List.forall_mem_cons.2 ⟨subd8_0_1011, List.forall_mem_cons.2 ⟨subd8_0_1012, List.forall_mem_cons.2 ⟨subd8_0_1013, List.forall_mem_cons.2 ⟨subd8_0_1014, List.forall_mem_cons.2 ⟨subd8_0_1015, List.forall_mem_cons.2 ⟨subd8_0_1016, List.forall_mem_cons.2 ⟨subd8_0_1017, List.forall_mem_cons.2 ⟨subd8_0_1018, List.forall_mem_cons.2 ⟨subd8_0_1019, List.forall_mem_cons.2 ⟨subd8_0_1020, List.forall_mem_cons.2 ⟨subd8_0_1021, List.forall_mem_cons.2 ⟨subd8_0_1022, List.forall_mem_cons.2 ⟨subd8_0_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_1024 : subd8_0 [4, 1, 0] = true := by decide +kernel
theorem subd8_0_1025 : subd8_0 [4, 1, 1] = true := by decide +kernel
theorem subd8_0_1026 : subd8_0 [4, 1, 2] = true := by decide +kernel
theorem subd8_0_1027 : subd8_0 [4, 1, 3] = true := by decide +kernel
theorem subd8_0_1028 : subd8_0 [4, 1, 4] = true := by decide +kernel
theorem subd8_0_1029 : subd8_0 [4, 1, 5] = true := by decide +kernel
theorem subd8_0_1030 : subd8_0 [4, 1, 6] = true := by decide +kernel
theorem subd8_0_1031 : subd8_0 [4, 2, -7] = true := by decide +kernel
theorem subd8_0_1032 : subd8_0 [4, 2, -6] = true := by decide +kernel
theorem subd8_0_1033 : subd8_0 [4, 2, -5] = true := by decide +kernel
theorem subd8_0_1034 : subd8_0 [4, 2, -4] = true := by decide +kernel
theorem subd8_0_1035 : subd8_0 [4, 2, -3] = true := by decide +kernel
theorem subd8_0_1036 : subd8_0 [4, 2, -2] = true := by decide +kernel
theorem subd8_0_1037 : subd8_0 [4, 2, -1] = true := by decide +kernel
theorem subd8_0_1038 : subd8_0 [4, 2, 0] = true := by decide +kernel
theorem subd8_0_1039 : subd8_0 [4, 2, 1] = true := by decide +kernel
theorem subd8_0_1040 : subd8_0 [4, 2, 2] = true := by decide +kernel
theorem subd8_0_1041 : subd8_0 [4, 2, 3] = true := by decide +kernel
theorem subd8_0_1042 : subd8_0 [4, 2, 4] = true := by decide +kernel
theorem subd8_0_1043 : subd8_0 [4, 2, 5] = true := by decide +kernel
theorem subd8_0_1044 : subd8_0 [4, 2, 6] = true := by decide +kernel
theorem subd8_0_1045 : subd8_0 [4, 3] = true := by decide +kernel
theorem subd8_0_1046 : subd8_0 [4, 4] = true := by decide +kernel
theorem subd8_0_1047 : subd8_0 [4, 5] = true := by decide +kernel
theorem subd8_0_1048 : subd8_0 [4, 6] = true := by decide +kernel
theorem subd8_0_1049 : subd8_0 [5, -2] = true := by decide +kernel
theorem subd8_0_1050 : subd8_0 [5, -1] = true := by decide +kernel
theorem subd8_0_1051 : subd8_0 [5, 0] = true := by decide +kernel
theorem subd8_0_1052 : subd8_0 [5, 1] = true := by decide +kernel
theorem subd8_0_1053 : subd8_0 [5, 2] = true := by decide +kernel
theorem subd8_0_1054 : subd8_0 [5, 3] = true := by decide +kernel
theorem subd8_0_1055 : subd8_0 [5, 4] = true := by decide +kernel
theorem sbd8_0_32 : ∀ q ∈ blkd8_0_32, subd8_0 q = true := by
  unfold blkd8_0_32
  exact List.forall_mem_cons.2 ⟨subd8_0_1024, List.forall_mem_cons.2 ⟨subd8_0_1025, List.forall_mem_cons.2 ⟨subd8_0_1026, List.forall_mem_cons.2 ⟨subd8_0_1027, List.forall_mem_cons.2 ⟨subd8_0_1028, List.forall_mem_cons.2 ⟨subd8_0_1029, List.forall_mem_cons.2 ⟨subd8_0_1030, List.forall_mem_cons.2 ⟨subd8_0_1031, List.forall_mem_cons.2 ⟨subd8_0_1032, List.forall_mem_cons.2 ⟨subd8_0_1033, List.forall_mem_cons.2 ⟨subd8_0_1034, List.forall_mem_cons.2 ⟨subd8_0_1035, List.forall_mem_cons.2 ⟨subd8_0_1036, List.forall_mem_cons.2 ⟨subd8_0_1037, List.forall_mem_cons.2 ⟨subd8_0_1038, List.forall_mem_cons.2 ⟨subd8_0_1039, List.forall_mem_cons.2 ⟨subd8_0_1040, List.forall_mem_cons.2 ⟨subd8_0_1041, List.forall_mem_cons.2 ⟨subd8_0_1042, List.forall_mem_cons.2 ⟨subd8_0_1043, List.forall_mem_cons.2 ⟨subd8_0_1044, List.forall_mem_cons.2 ⟨subd8_0_1045, List.forall_mem_cons.2 ⟨subd8_0_1046, List.forall_mem_cons.2 ⟨subd8_0_1047, List.forall_mem_cons.2 ⟨subd8_0_1048, List.forall_mem_cons.2 ⟨subd8_0_1049, List.forall_mem_cons.2 ⟨subd8_0_1050, List.forall_mem_cons.2 ⟨subd8_0_1051, List.forall_mem_cons.2 ⟨subd8_0_1052, List.forall_mem_cons.2 ⟨subd8_0_1053, List.forall_mem_cons.2 ⟨subd8_0_1054, List.forall_mem_cons.2 ⟨subd8_0_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd8_0_1056 : subd8_0 [5, 5] = true := by decide +kernel
theorem sbd8_0_33 : ∀ q ∈ blkd8_0_33, subd8_0 q = true := by
  unfold blkd8_0_33
  exact List.forall_mem_cons.2 ⟨subd8_0_1056, List.forall_mem_nil _⟩
theorem ld_okd8_1 : ldCheck G d8_1.U d8_1.ms ldd8_1 = true := by decide +kernel
theorem pre_okd8_1 : subPre G cell8 d8_1 = true := by decide +kernel
theorem subd8_1_0 : subd8_1 [] = true := by decide +kernel
theorem sbd8_1_0 : ∀ q ∈ blkd8_1_0, subd8_1 q = true := by
  unfold blkd8_1_0
  exact List.forall_mem_cons.2 ⟨subd8_1_0, List.forall_mem_nil _⟩
theorem ld_okd8_2 : ldCheck G d8_2.U d8_2.ms ldd8_2 = true := by decide +kernel
theorem pre_okd8_2 : subPre G cell8 d8_2 = true := by decide +kernel
theorem subd8_2_0 : subd8_2 [-1] = true := by decide +kernel
theorem subd8_2_1 : subd8_2 [0] = true := by decide +kernel
theorem subd8_2_2 : subd8_2 [1] = true := by decide +kernel
theorem sbd8_2_0 : ∀ q ∈ blkd8_2_0, subd8_2 q = true := by
  unfold blkd8_2_0
  exact List.forall_mem_cons.2 ⟨subd8_2_0, List.forall_mem_cons.2 ⟨subd8_2_1, List.forall_mem_cons.2 ⟨subd8_2_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_3 : ldCheck G d8_3.U d8_3.ms ldd8_3 = true := by decide +kernel
theorem pre_okd8_3 : subPre G cell8 d8_3 = true := by decide +kernel
theorem subd8_3_0 : subd8_3 [-1] = true := by decide +kernel
theorem subd8_3_1 : subd8_3 [0] = true := by decide +kernel
theorem subd8_3_2 : subd8_3 [1] = true := by decide +kernel
theorem sbd8_3_0 : ∀ q ∈ blkd8_3_0, subd8_3 q = true := by
  unfold blkd8_3_0
  exact List.forall_mem_cons.2 ⟨subd8_3_0, List.forall_mem_cons.2 ⟨subd8_3_1, List.forall_mem_cons.2 ⟨subd8_3_2, List.forall_mem_nil _⟩⟩⟩
theorem ld_okd8_4 : ldCheck G d8_4.U d8_4.ms ldd8_4 = true := by decide +kernel
theorem pre_okd8_4 : subPre G cell8 d8_4 = true := by decide +kernel
theorem subd8_4_0 : subd8_4 [] = true := by decide +kernel
theorem sbd8_4_0 : ∀ q ∈ blkd8_4_0, subd8_4 q = true := by
  unfold blkd8_4_0
  exact List.forall_mem_cons.2 ⟨subd8_4_0, List.forall_mem_nil _⟩

end ReflectZphi.Data.Cert5.C093
