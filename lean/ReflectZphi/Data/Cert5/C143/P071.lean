import ReflectZphi.Data.Cert5.C143.Base

namespace ReflectZphi.Data.Cert5.C143

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd19_2_864 : subd19_2 [2, 3, -5] = true := by decide +kernel
theorem subd19_2_865 : subd19_2 [2, 3, -4] = true := by decide +kernel
theorem subd19_2_866 : subd19_2 [2, 3, -3] = true := by decide +kernel
theorem subd19_2_867 : subd19_2 [2, 3, -2] = true := by decide +kernel
theorem subd19_2_868 : subd19_2 [2, 3, -1] = true := by decide +kernel
theorem subd19_2_869 : subd19_2 [2, 3, 0] = true := by decide +kernel
theorem subd19_2_870 : subd19_2 [2, 3, 1] = true := by decide +kernel
theorem subd19_2_871 : subd19_2 [2, 3, 2] = true := by decide +kernel
theorem subd19_2_872 : subd19_2 [2, 3, 3] = true := by decide +kernel
theorem subd19_2_873 : subd19_2 [2, 3, 4] = true := by decide +kernel
theorem subd19_2_874 : subd19_2 [2, 3, 5] = true := by decide +kernel
theorem subd19_2_875 : subd19_2 [2, 3, 6] = true := by decide +kernel
theorem subd19_2_876 : subd19_2 [2, 4] = true := by decide +kernel
theorem subd19_2_877 : subd19_2 [2, 5] = true := by decide +kernel
theorem subd19_2_878 : subd19_2 [2, 6] = true := by decide +kernel
theorem subd19_2_879 : subd19_2 [3, -8] = true := by decide +kernel
theorem subd19_2_880 : subd19_2 [3, -7] = true := by decide +kernel
theorem subd19_2_881 : subd19_2 [3, -6] = true := by decide +kernel
theorem subd19_2_882 : subd19_2 [3, -5] = true := by decide +kernel
theorem subd19_2_883 : subd19_2 [3, -4, -7] = true := by decide +kernel
theorem subd19_2_884 : subd19_2 [3, -4, -6] = true := by decide +kernel
theorem subd19_2_885 : subd19_2 [3, -4, -5] = true := by decide +kernel
theorem subd19_2_886 : subd19_2 [3, -4, -4] = true := by decide +kernel
theorem subd19_2_887 : subd19_2 [3, -4, -3] = true := by decide +kernel
theorem subd19_2_888 : subd19_2 [3, -4, -2] = true := by decide +kernel
theorem subd19_2_889 : subd19_2 [3, -4, -1] = true := by decide +kernel
theorem subd19_2_890 : subd19_2 [3, -4, 0] = true := by decide +kernel
theorem subd19_2_891 : subd19_2 [3, -4, 1] = true := by decide +kernel
theorem subd19_2_892 : subd19_2 [3, -4, 2] = true := by decide +kernel
theorem subd19_2_893 : subd19_2 [3, -4, 3] = true := by decide +kernel
theorem subd19_2_894 : subd19_2 [3, -4, 4] = true := by decide +kernel
theorem subd19_2_895 : subd19_2 [3, -4, 5] = true := by decide +kernel
theorem sbd19_2_27 : ∀ q ∈ blkd19_2_27, subd19_2 q = true := by
  unfold blkd19_2_27
  exact List.forall_mem_cons.2 ⟨subd19_2_864, List.forall_mem_cons.2 ⟨subd19_2_865, List.forall_mem_cons.2 ⟨subd19_2_866, List.forall_mem_cons.2 ⟨subd19_2_867, List.forall_mem_cons.2 ⟨subd19_2_868, List.forall_mem_cons.2 ⟨subd19_2_869, List.forall_mem_cons.2 ⟨subd19_2_870, List.forall_mem_cons.2 ⟨subd19_2_871, List.forall_mem_cons.2 ⟨subd19_2_872, List.forall_mem_cons.2 ⟨subd19_2_873, List.forall_mem_cons.2 ⟨subd19_2_874, List.forall_mem_cons.2 ⟨subd19_2_875, List.forall_mem_cons.2 ⟨subd19_2_876, List.forall_mem_cons.2 ⟨subd19_2_877, List.forall_mem_cons.2 ⟨subd19_2_878, List.forall_mem_cons.2 ⟨subd19_2_879, List.forall_mem_cons.2 ⟨subd19_2_880, List.forall_mem_cons.2 ⟨subd19_2_881, List.forall_mem_cons.2 ⟨subd19_2_882, List.forall_mem_cons.2 ⟨subd19_2_883, List.forall_mem_cons.2 ⟨subd19_2_884, List.forall_mem_cons.2 ⟨subd19_2_885, List.forall_mem_cons.2 ⟨subd19_2_886, List.forall_mem_cons.2 ⟨subd19_2_887, List.forall_mem_cons.2 ⟨subd19_2_888, List.forall_mem_cons.2 ⟨subd19_2_889, List.forall_mem_cons.2 ⟨subd19_2_890, List.forall_mem_cons.2 ⟨subd19_2_891, List.forall_mem_cons.2 ⟨subd19_2_892, List.forall_mem_cons.2 ⟨subd19_2_893, List.forall_mem_cons.2 ⟨subd19_2_894, List.forall_mem_cons.2 ⟨subd19_2_895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_896 : subd19_2 [3, -4, 6] = true := by decide +kernel
theorem subd19_2_897 : subd19_2 [3, -3, -7] = true := by decide +kernel
theorem subd19_2_898 : subd19_2 [3, -3, -6] = true := by decide +kernel
theorem subd19_2_899 : subd19_2 [3, -3, -5] = true := by decide +kernel
theorem subd19_2_900 : subd19_2 [3, -3, -4] = true := by decide +kernel
theorem subd19_2_901 : subd19_2 [3, -3, -3] = true := by decide +kernel
theorem subd19_2_902 : subd19_2 [3, -3, -2] = true := by decide +kernel
theorem subd19_2_903 : subd19_2 [3, -3, -1] = true := by decide +kernel
theorem subd19_2_904 : subd19_2 [3, -3, 0] = true := by decide +kernel
theorem subd19_2_905 : subd19_2 [3, -3, 1] = true := by decide +kernel
theorem subd19_2_906 : subd19_2 [3, -3, 2] = true := by decide +kernel
theorem subd19_2_907 : subd19_2 [3, -3, 3] = true := by decide +kernel
theorem subd19_2_908 : subd19_2 [3, -3, 4] = true := by decide +kernel
theorem subd19_2_909 : subd19_2 [3, -3, 5] = true := by decide +kernel
theorem subd19_2_910 : subd19_2 [3, -3, 6] = true := by decide +kernel
theorem subd19_2_911 : subd19_2 [3, -3, 7] = true := by decide +kernel
theorem subd19_2_912 : subd19_2 [3, -2, -7] = true := by decide +kernel
theorem subd19_2_913 : subd19_2 [3, -2, -6] = true := by decide +kernel
theorem subd19_2_914 : subd19_2 [3, -2, -5] = true := by decide +kernel
theorem subd19_2_915 : subd19_2 [3, -2, -4] = true := by decide +kernel
theorem subd19_2_916 : subd19_2 [3, -2, -3] = true := by decide +kernel
theorem subd19_2_917 : subd19_2 [3, -2, -2] = true := by decide +kernel
theorem subd19_2_918 : subd19_2 [3, -2, -1] = true := by decide +kernel
theorem subd19_2_919 : subd19_2 [3, -2, 0] = true := by decide +kernel
theorem subd19_2_920 : subd19_2 [3, -2, 1] = true := by decide +kernel
theorem subd19_2_921 : subd19_2 [3, -2, 2] = true := by decide +kernel
theorem subd19_2_922 : subd19_2 [3, -2, 3] = true := by decide +kernel
theorem subd19_2_923 : subd19_2 [3, -2, 4] = true := by decide +kernel
theorem subd19_2_924 : subd19_2 [3, -2, 5] = true := by decide +kernel
theorem subd19_2_925 : subd19_2 [3, -2, 6] = true := by decide +kernel
theorem subd19_2_926 : subd19_2 [3, -2, 7] = true := by decide +kernel
theorem subd19_2_927 : subd19_2 [3, -1, -7] = true := by decide +kernel
theorem sbd19_2_28 : ∀ q ∈ blkd19_2_28, subd19_2 q = true := by
  unfold blkd19_2_28
  exact List.forall_mem_cons.2 ⟨subd19_2_896, List.forall_mem_cons.2 ⟨subd19_2_897, List.forall_mem_cons.2 ⟨subd19_2_898, List.forall_mem_cons.2 ⟨subd19_2_899, List.forall_mem_cons.2 ⟨subd19_2_900, List.forall_mem_cons.2 ⟨subd19_2_901, List.forall_mem_cons.2 ⟨subd19_2_902, List.forall_mem_cons.2 ⟨subd19_2_903, List.forall_mem_cons.2 ⟨subd19_2_904, List.forall_mem_cons.2 ⟨subd19_2_905, List.forall_mem_cons.2 ⟨subd19_2_906, List.forall_mem_cons.2 ⟨subd19_2_907, List.forall_mem_cons.2 ⟨subd19_2_908, List.forall_mem_cons.2 ⟨subd19_2_909, List.forall_mem_cons.2 ⟨subd19_2_910, List.forall_mem_cons.2 ⟨subd19_2_911, List.forall_mem_cons.2 ⟨subd19_2_912, List.forall_mem_cons.2 ⟨subd19_2_913, List.forall_mem_cons.2 ⟨subd19_2_914, List.forall_mem_cons.2 ⟨subd19_2_915, List.forall_mem_cons.2 ⟨subd19_2_916, List.forall_mem_cons.2 ⟨subd19_2_917, List.forall_mem_cons.2 ⟨subd19_2_918, List.forall_mem_cons.2 ⟨subd19_2_919, List.forall_mem_cons.2 ⟨subd19_2_920, List.forall_mem_cons.2 ⟨subd19_2_921, List.forall_mem_cons.2 ⟨subd19_2_922, List.forall_mem_cons.2 ⟨subd19_2_923, List.forall_mem_cons.2 ⟨subd19_2_924, List.forall_mem_cons.2 ⟨subd19_2_925, List.forall_mem_cons.2 ⟨subd19_2_926, List.forall_mem_cons.2 ⟨subd19_2_927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_928 : subd19_2 [3, -1, -6] = true := by decide +kernel
theorem subd19_2_929 : subd19_2 [3, -1, -5] = true := by decide +kernel
theorem subd19_2_930 : subd19_2 [3, -1, -4] = true := by decide +kernel
theorem subd19_2_931 : subd19_2 [3, -1, -3] = true := by decide +kernel
theorem subd19_2_932 : subd19_2 [3, -1, -2] = true := by decide +kernel
theorem subd19_2_933 : subd19_2 [3, -1, -1] = true := by decide +kernel
theorem subd19_2_934 : subd19_2 [3, -1, 0] = true := by decide +kernel
theorem subd19_2_935 : subd19_2 [3, -1, 1] = true := by decide +kernel
theorem subd19_2_936 : subd19_2 [3, -1, 2] = true := by decide +kernel
theorem subd19_2_937 : subd19_2 [3, -1, 3] = true := by decide +kernel
theorem subd19_2_938 : subd19_2 [3, -1, 4] = true := by decide +kernel
theorem subd19_2_939 : subd19_2 [3, -1, 5] = true := by decide +kernel
theorem subd19_2_940 : subd19_2 [3, -1, 6] = true := by decide +kernel
theorem subd19_2_941 : subd19_2 [3, -1, 7] = true := by decide +kernel
theorem subd19_2_942 : subd19_2 [3, 0, -7] = true := by decide +kernel
theorem subd19_2_943 : subd19_2 [3, 0, -6] = true := by decide +kernel
theorem subd19_2_944 : subd19_2 [3, 0, -5] = true := by decide +kernel
theorem subd19_2_945 : subd19_2 [3, 0, -4] = true := by decide +kernel
theorem subd19_2_946 : subd19_2 [3, 0, -3] = true := by decide +kernel
theorem subd19_2_947 : subd19_2 [3, 0, -2] = true := by decide +kernel
theorem subd19_2_948 : subd19_2 [3, 0, -1] = true := by decide +kernel
theorem subd19_2_949 : subd19_2 [3, 0, 0] = true := by decide +kernel
theorem subd19_2_950 : subd19_2 [3, 0, 1] = true := by decide +kernel
theorem subd19_2_951 : subd19_2 [3, 0, 2] = true := by decide +kernel
theorem subd19_2_952 : subd19_2 [3, 0, 3] = true := by decide +kernel
theorem subd19_2_953 : subd19_2 [3, 0, 4] = true := by decide +kernel
theorem subd19_2_954 : subd19_2 [3, 0, 5] = true := by decide +kernel
theorem subd19_2_955 : subd19_2 [3, 0, 6] = true := by decide +kernel
theorem subd19_2_956 : subd19_2 [3, 0, 7] = true := by decide +kernel
theorem subd19_2_957 : subd19_2 [3, 1, -7] = true := by decide +kernel
theorem subd19_2_958 : subd19_2 [3, 1, -6] = true := by decide +kernel
theorem subd19_2_959 : subd19_2 [3, 1, -5] = true := by decide +kernel
theorem sbd19_2_29 : ∀ q ∈ blkd19_2_29, subd19_2 q = true := by
  unfold blkd19_2_29
  exact List.forall_mem_cons.2 ⟨subd19_2_928, List.forall_mem_cons.2 ⟨subd19_2_929, List.forall_mem_cons.2 ⟨subd19_2_930, List.forall_mem_cons.2 ⟨subd19_2_931, List.forall_mem_cons.2 ⟨subd19_2_932, List.forall_mem_cons.2 ⟨subd19_2_933, List.forall_mem_cons.2 ⟨subd19_2_934, List.forall_mem_cons.2 ⟨subd19_2_935, List.forall_mem_cons.2 ⟨subd19_2_936, List.forall_mem_cons.2 ⟨subd19_2_937, List.forall_mem_cons.2 ⟨subd19_2_938, List.forall_mem_cons.2 ⟨subd19_2_939, List.forall_mem_cons.2 ⟨subd19_2_940, List.forall_mem_cons.2 ⟨subd19_2_941, List.forall_mem_cons.2 ⟨subd19_2_942, List.forall_mem_cons.2 ⟨subd19_2_943, List.forall_mem_cons.2 ⟨subd19_2_944, List.forall_mem_cons.2 ⟨subd19_2_945, List.forall_mem_cons.2 ⟨subd19_2_946, List.forall_mem_cons.2 ⟨subd19_2_947, List.forall_mem_cons.2 ⟨subd19_2_948, List.forall_mem_cons.2 ⟨subd19_2_949, List.forall_mem_cons.2 ⟨subd19_2_950, List.forall_mem_cons.2 ⟨subd19_2_951, List.forall_mem_cons.2 ⟨subd19_2_952, List.forall_mem_cons.2 ⟨subd19_2_953, List.forall_mem_cons.2 ⟨subd19_2_954, List.forall_mem_cons.2 ⟨subd19_2_955, List.forall_mem_cons.2 ⟨subd19_2_956, List.forall_mem_cons.2 ⟨subd19_2_957, List.forall_mem_cons.2 ⟨subd19_2_958, List.forall_mem_cons.2 ⟨subd19_2_959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_960 : subd19_2 [3, 1, -4] = true := by decide +kernel
theorem subd19_2_961 : subd19_2 [3, 1, -3] = true := by decide +kernel
theorem subd19_2_962 : subd19_2 [3, 1, -2] = true := by decide +kernel
theorem subd19_2_963 : subd19_2 [3, 1, -1] = true := by decide +kernel
theorem subd19_2_964 : subd19_2 [3, 1, 0] = true := by decide +kernel
theorem subd19_2_965 : subd19_2 [3, 1, 1] = true := by decide +kernel
theorem subd19_2_966 : subd19_2 [3, 1, 2] = true := by decide +kernel
theorem subd19_2_967 : subd19_2 [3, 1, 3] = true := by decide +kernel
theorem subd19_2_968 : subd19_2 [3, 1, 4] = true := by decide +kernel
theorem subd19_2_969 : subd19_2 [3, 1, 5] = true := by decide +kernel
theorem subd19_2_970 : subd19_2 [3, 1, 6] = true := by decide +kernel
theorem subd19_2_971 : subd19_2 [3, 1, 7] = true := by decide +kernel
theorem subd19_2_972 : subd19_2 [3, 2, -7] = true := by decide +kernel
theorem subd19_2_973 : subd19_2 [3, 2, -6] = true := by decide +kernel
theorem subd19_2_974 : subd19_2 [3, 2, -5] = true := by decide +kernel
theorem subd19_2_975 : subd19_2 [3, 2, -4] = true := by decide +kernel
theorem subd19_2_976 : subd19_2 [3, 2, -3] = true := by decide +kernel
theorem subd19_2_977 : subd19_2 [3, 2, -2] = true := by decide +kernel
theorem subd19_2_978 : subd19_2 [3, 2, -1] = true := by decide +kernel
theorem subd19_2_979 : subd19_2 [3, 2, 0] = true := by decide +kernel
theorem subd19_2_980 : subd19_2 [3, 2, 1] = true := by decide +kernel
theorem subd19_2_981 : subd19_2 [3, 2, 2] = true := by decide +kernel
theorem subd19_2_982 : subd19_2 [3, 2, 3] = true := by decide +kernel
theorem subd19_2_983 : subd19_2 [3, 2, 4] = true := by decide +kernel
theorem subd19_2_984 : subd19_2 [3, 2, 5] = true := by decide +kernel
theorem subd19_2_985 : subd19_2 [3, 2, 6] = true := by decide +kernel
theorem subd19_2_986 : subd19_2 [3, 3] = true := by decide +kernel
theorem subd19_2_987 : subd19_2 [3, 4] = true := by decide +kernel
theorem subd19_2_988 : subd19_2 [3, 5] = true := by decide +kernel
theorem subd19_2_989 : subd19_2 [4, -8] = true := by decide +kernel
theorem subd19_2_990 : subd19_2 [4, -7] = true := by decide +kernel
theorem subd19_2_991 : subd19_2 [4, -6] = true := by decide +kernel
theorem sbd19_2_30 : ∀ q ∈ blkd19_2_30, subd19_2 q = true := by
  unfold blkd19_2_30
  exact List.forall_mem_cons.2 ⟨subd19_2_960, List.forall_mem_cons.2 ⟨subd19_2_961, List.forall_mem_cons.2 ⟨subd19_2_962, List.forall_mem_cons.2 ⟨subd19_2_963, List.forall_mem_cons.2 ⟨subd19_2_964, List.forall_mem_cons.2 ⟨subd19_2_965, List.forall_mem_cons.2 ⟨subd19_2_966, List.forall_mem_cons.2 ⟨subd19_2_967, List.forall_mem_cons.2 ⟨subd19_2_968, List.forall_mem_cons.2 ⟨subd19_2_969, List.forall_mem_cons.2 ⟨subd19_2_970, List.forall_mem_cons.2 ⟨subd19_2_971, List.forall_mem_cons.2 ⟨subd19_2_972, List.forall_mem_cons.2 ⟨subd19_2_973, List.forall_mem_cons.2 ⟨subd19_2_974, List.forall_mem_cons.2 ⟨subd19_2_975, List.forall_mem_cons.2 ⟨subd19_2_976, List.forall_mem_cons.2 ⟨subd19_2_977, List.forall_mem_cons.2 ⟨subd19_2_978, List.forall_mem_cons.2 ⟨subd19_2_979, List.forall_mem_cons.2 ⟨subd19_2_980, List.forall_mem_cons.2 ⟨subd19_2_981, List.forall_mem_cons.2 ⟨subd19_2_982, List.forall_mem_cons.2 ⟨subd19_2_983, List.forall_mem_cons.2 ⟨subd19_2_984, List.forall_mem_cons.2 ⟨subd19_2_985, List.forall_mem_cons.2 ⟨subd19_2_986, List.forall_mem_cons.2 ⟨subd19_2_987, List.forall_mem_cons.2 ⟨subd19_2_988, List.forall_mem_cons.2 ⟨subd19_2_989, List.forall_mem_cons.2 ⟨subd19_2_990, List.forall_mem_cons.2 ⟨subd19_2_991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_992 : subd19_2 [4, -5] = true := by decide +kernel
theorem subd19_2_993 : subd19_2 [4, -4] = true := by decide +kernel
theorem subd19_2_994 : subd19_2 [4, -3, -7] = true := by decide +kernel
theorem subd19_2_995 : subd19_2 [4, -3, -6] = true := by decide +kernel
theorem subd19_2_996 : subd19_2 [4, -3, -5] = true := by decide +kernel
theorem subd19_2_997 : subd19_2 [4, -3, -4] = true := by decide +kernel
theorem subd19_2_998 : subd19_2 [4, -3, -3] = true := by decide +kernel
theorem subd19_2_999 : subd19_2 [4, -3, -2] = true := by decide +kernel
theorem subd19_2_1000 : subd19_2 [4, -3, -1] = true := by decide +kernel
theorem subd19_2_1001 : subd19_2 [4, -3, 0] = true := by decide +kernel
theorem subd19_2_1002 : subd19_2 [4, -3, 1] = true := by decide +kernel
theorem subd19_2_1003 : subd19_2 [4, -3, 2] = true := by decide +kernel
theorem subd19_2_1004 : subd19_2 [4, -3, 3] = true := by decide +kernel
theorem subd19_2_1005 : subd19_2 [4, -3, 4] = true := by decide +kernel
theorem subd19_2_1006 : subd19_2 [4, -3, 5] = true := by decide +kernel
theorem subd19_2_1007 : subd19_2 [4, -3, 6] = true := by decide +kernel
theorem subd19_2_1008 : subd19_2 [4, -3, 7] = true := by decide +kernel
theorem subd19_2_1009 : subd19_2 [4, -2, -7] = true := by decide +kernel
theorem subd19_2_1010 : subd19_2 [4, -2, -6] = true := by decide +kernel
theorem subd19_2_1011 : subd19_2 [4, -2, -5] = true := by decide +kernel
theorem subd19_2_1012 : subd19_2 [4, -2, -4] = true := by decide +kernel
theorem subd19_2_1013 : subd19_2 [4, -2, -3] = true := by decide +kernel
theorem subd19_2_1014 : subd19_2 [4, -2, -2] = true := by decide +kernel
theorem subd19_2_1015 : subd19_2 [4, -2, -1] = true := by decide +kernel
theorem subd19_2_1016 : subd19_2 [4, -2, 0] = true := by decide +kernel
theorem subd19_2_1017 : subd19_2 [4, -2, 1] = true := by decide +kernel
theorem subd19_2_1018 : subd19_2 [4, -2, 2] = true := by decide +kernel
theorem subd19_2_1019 : subd19_2 [4, -2, 3] = true := by decide +kernel
theorem subd19_2_1020 : subd19_2 [4, -2, 4] = true := by decide +kernel
theorem subd19_2_1021 : subd19_2 [4, -2, 5] = true := by decide +kernel
theorem subd19_2_1022 : subd19_2 [4, -2, 6] = true := by decide +kernel
theorem subd19_2_1023 : subd19_2 [4, -2, 7] = true := by decide +kernel
theorem sbd19_2_31 : ∀ q ∈ blkd19_2_31, subd19_2 q = true := by
  unfold blkd19_2_31
  exact List.forall_mem_cons.2 ⟨subd19_2_992, List.forall_mem_cons.2 ⟨subd19_2_993, List.forall_mem_cons.2 ⟨subd19_2_994, List.forall_mem_cons.2 ⟨subd19_2_995, List.forall_mem_cons.2 ⟨subd19_2_996, List.forall_mem_cons.2 ⟨subd19_2_997, List.forall_mem_cons.2 ⟨subd19_2_998, List.forall_mem_cons.2 ⟨subd19_2_999, List.forall_mem_cons.2 ⟨subd19_2_1000, List.forall_mem_cons.2 ⟨subd19_2_1001, List.forall_mem_cons.2 ⟨subd19_2_1002, List.forall_mem_cons.2 ⟨subd19_2_1003, List.forall_mem_cons.2 ⟨subd19_2_1004, List.forall_mem_cons.2 ⟨subd19_2_1005, List.forall_mem_cons.2 ⟨subd19_2_1006, List.forall_mem_cons.2 ⟨subd19_2_1007, List.forall_mem_cons.2 ⟨subd19_2_1008, List.forall_mem_cons.2 ⟨subd19_2_1009, List.forall_mem_cons.2 ⟨subd19_2_1010, List.forall_mem_cons.2 ⟨subd19_2_1011, List.forall_mem_cons.2 ⟨subd19_2_1012, List.forall_mem_cons.2 ⟨subd19_2_1013, List.forall_mem_cons.2 ⟨subd19_2_1014, List.forall_mem_cons.2 ⟨subd19_2_1015, List.forall_mem_cons.2 ⟨subd19_2_1016, List.forall_mem_cons.2 ⟨subd19_2_1017, List.forall_mem_cons.2 ⟨subd19_2_1018, List.forall_mem_cons.2 ⟨subd19_2_1019, List.forall_mem_cons.2 ⟨subd19_2_1020, List.forall_mem_cons.2 ⟨subd19_2_1021, List.forall_mem_cons.2 ⟨subd19_2_1022, List.forall_mem_cons.2 ⟨subd19_2_1023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_1024 : subd19_2 [4, -1, -7] = true := by decide +kernel
theorem subd19_2_1025 : subd19_2 [4, -1, -6] = true := by decide +kernel
theorem subd19_2_1026 : subd19_2 [4, -1, -5] = true := by decide +kernel
theorem subd19_2_1027 : subd19_2 [4, -1, -4] = true := by decide +kernel
theorem subd19_2_1028 : subd19_2 [4, -1, -3] = true := by decide +kernel
theorem subd19_2_1029 : subd19_2 [4, -1, -2] = true := by decide +kernel
theorem subd19_2_1030 : subd19_2 [4, -1, -1] = true := by decide +kernel
theorem subd19_2_1031 : subd19_2 [4, -1, 0] = true := by decide +kernel
theorem subd19_2_1032 : subd19_2 [4, -1, 1] = true := by decide +kernel
theorem subd19_2_1033 : subd19_2 [4, -1, 2] = true := by decide +kernel
theorem subd19_2_1034 : subd19_2 [4, -1, 3] = true := by decide +kernel
theorem subd19_2_1035 : subd19_2 [4, -1, 4] = true := by decide +kernel
theorem subd19_2_1036 : subd19_2 [4, -1, 5] = true := by decide +kernel
theorem subd19_2_1037 : subd19_2 [4, -1, 6] = true := by decide +kernel
theorem subd19_2_1038 : subd19_2 [4, -1, 7] = true := by decide +kernel
theorem subd19_2_1039 : subd19_2 [4, 0, -7] = true := by decide +kernel
theorem subd19_2_1040 : subd19_2 [4, 0, -6] = true := by decide +kernel
theorem subd19_2_1041 : subd19_2 [4, 0, -5] = true := by decide +kernel
theorem subd19_2_1042 : subd19_2 [4, 0, -4] = true := by decide +kernel
theorem subd19_2_1043 : subd19_2 [4, 0, -3] = true := by decide +kernel
theorem subd19_2_1044 : subd19_2 [4, 0, -2] = true := by decide +kernel
theorem subd19_2_1045 : subd19_2 [4, 0, -1] = true := by decide +kernel
theorem subd19_2_1046 : subd19_2 [4, 0, 0] = true := by decide +kernel
theorem subd19_2_1047 : subd19_2 [4, 0, 1] = true := by decide +kernel
theorem subd19_2_1048 : subd19_2 [4, 0, 2] = true := by decide +kernel
theorem subd19_2_1049 : subd19_2 [4, 0, 3] = true := by decide +kernel
theorem subd19_2_1050 : subd19_2 [4, 0, 4] = true := by decide +kernel
theorem subd19_2_1051 : subd19_2 [4, 0, 5] = true := by decide +kernel
theorem subd19_2_1052 : subd19_2 [4, 0, 6] = true := by decide +kernel
theorem subd19_2_1053 : subd19_2 [4, 0, 7] = true := by decide +kernel
theorem subd19_2_1054 : subd19_2 [4, 1] = true := by decide +kernel
theorem subd19_2_1055 : subd19_2 [4, 2] = true := by decide +kernel
theorem sbd19_2_32 : ∀ q ∈ blkd19_2_32, subd19_2 q = true := by
  unfold blkd19_2_32
  exact List.forall_mem_cons.2 ⟨subd19_2_1024, List.forall_mem_cons.2 ⟨subd19_2_1025, List.forall_mem_cons.2 ⟨subd19_2_1026, List.forall_mem_cons.2 ⟨subd19_2_1027, List.forall_mem_cons.2 ⟨subd19_2_1028, List.forall_mem_cons.2 ⟨subd19_2_1029, List.forall_mem_cons.2 ⟨subd19_2_1030, List.forall_mem_cons.2 ⟨subd19_2_1031, List.forall_mem_cons.2 ⟨subd19_2_1032, List.forall_mem_cons.2 ⟨subd19_2_1033, List.forall_mem_cons.2 ⟨subd19_2_1034, List.forall_mem_cons.2 ⟨subd19_2_1035, List.forall_mem_cons.2 ⟨subd19_2_1036, List.forall_mem_cons.2 ⟨subd19_2_1037, List.forall_mem_cons.2 ⟨subd19_2_1038, List.forall_mem_cons.2 ⟨subd19_2_1039, List.forall_mem_cons.2 ⟨subd19_2_1040, List.forall_mem_cons.2 ⟨subd19_2_1041, List.forall_mem_cons.2 ⟨subd19_2_1042, List.forall_mem_cons.2 ⟨subd19_2_1043, List.forall_mem_cons.2 ⟨subd19_2_1044, List.forall_mem_cons.2 ⟨subd19_2_1045, List.forall_mem_cons.2 ⟨subd19_2_1046, List.forall_mem_cons.2 ⟨subd19_2_1047, List.forall_mem_cons.2 ⟨subd19_2_1048, List.forall_mem_cons.2 ⟨subd19_2_1049, List.forall_mem_cons.2 ⟨subd19_2_1050, List.forall_mem_cons.2 ⟨subd19_2_1051, List.forall_mem_cons.2 ⟨subd19_2_1052, List.forall_mem_cons.2 ⟨subd19_2_1053, List.forall_mem_cons.2 ⟨subd19_2_1054, List.forall_mem_cons.2 ⟨subd19_2_1055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd19_2_1056 : subd19_2 [4, 3] = true := by decide +kernel
theorem subd19_2_1057 : subd19_2 [4, 4] = true := by decide +kernel
theorem subd19_2_1058 : subd19_2 [5, -8] = true := by decide +kernel
theorem subd19_2_1059 : subd19_2 [5, -7] = true := by decide +kernel
theorem subd19_2_1060 : subd19_2 [5, -6] = true := by decide +kernel
theorem subd19_2_1061 : subd19_2 [5, -5] = true := by decide +kernel
theorem subd19_2_1062 : subd19_2 [5, -4] = true := by decide +kernel
theorem subd19_2_1063 : subd19_2 [5, -3] = true := by decide +kernel
theorem subd19_2_1064 : subd19_2 [5, -2] = true := by decide +kernel
theorem subd19_2_1065 : subd19_2 [5, -1] = true := by decide +kernel
theorem subd19_2_1066 : subd19_2 [5, 0] = true := by decide +kernel
theorem subd19_2_1067 : subd19_2 [5, 1] = true := by decide +kernel
theorem subd19_2_1068 : subd19_2 [5, 2] = true := by decide +kernel
theorem subd19_2_1069 : subd19_2 [5, 3] = true := by decide +kernel
theorem subd19_2_1070 : subd19_2 [6, -7] = true := by decide +kernel
theorem subd19_2_1071 : subd19_2 [6, -6] = true := by decide +kernel
theorem subd19_2_1072 : subd19_2 [6, -5] = true := by decide +kernel
theorem subd19_2_1073 : subd19_2 [6, -4] = true := by decide +kernel
theorem subd19_2_1074 : subd19_2 [6, -3] = true := by decide +kernel
theorem subd19_2_1075 : subd19_2 [6, -2] = true := by decide +kernel
theorem subd19_2_1076 : subd19_2 [6, -1] = true := by decide +kernel
theorem subd19_2_1077 : subd19_2 [6, 0] = true := by decide +kernel
theorem subd19_2_1078 : subd19_2 [6, 1] = true := by decide +kernel
theorem subd19_2_1079 : subd19_2 [6, 2] = true := by decide +kernel
theorem subd19_2_1080 : subd19_2 [7, -6] = true := by decide +kernel
theorem subd19_2_1081 : subd19_2 [7, -5] = true := by decide +kernel
theorem subd19_2_1082 : subd19_2 [7, -4] = true := by decide +kernel
theorem subd19_2_1083 : subd19_2 [7, -3] = true := by decide +kernel
theorem subd19_2_1084 : subd19_2 [7, -2] = true := by decide +kernel
theorem subd19_2_1085 : subd19_2 [7, -1] = true := by decide +kernel
theorem subd19_2_1086 : subd19_2 [7, 0] = true := by decide +kernel
theorem sbd19_2_33 : ∀ q ∈ blkd19_2_33, subd19_2 q = true := by
  unfold blkd19_2_33
  exact List.forall_mem_cons.2 ⟨subd19_2_1056, List.forall_mem_cons.2 ⟨subd19_2_1057, List.forall_mem_cons.2 ⟨subd19_2_1058, List.forall_mem_cons.2 ⟨subd19_2_1059, List.forall_mem_cons.2 ⟨subd19_2_1060, List.forall_mem_cons.2 ⟨subd19_2_1061, List.forall_mem_cons.2 ⟨subd19_2_1062, List.forall_mem_cons.2 ⟨subd19_2_1063, List.forall_mem_cons.2 ⟨subd19_2_1064, List.forall_mem_cons.2 ⟨subd19_2_1065, List.forall_mem_cons.2 ⟨subd19_2_1066, List.forall_mem_cons.2 ⟨subd19_2_1067, List.forall_mem_cons.2 ⟨subd19_2_1068, List.forall_mem_cons.2 ⟨subd19_2_1069, List.forall_mem_cons.2 ⟨subd19_2_1070, List.forall_mem_cons.2 ⟨subd19_2_1071, List.forall_mem_cons.2 ⟨subd19_2_1072, List.forall_mem_cons.2 ⟨subd19_2_1073, List.forall_mem_cons.2 ⟨subd19_2_1074, List.forall_mem_cons.2 ⟨subd19_2_1075, List.forall_mem_cons.2 ⟨subd19_2_1076, List.forall_mem_cons.2 ⟨subd19_2_1077, List.forall_mem_cons.2 ⟨subd19_2_1078, List.forall_mem_cons.2 ⟨subd19_2_1079, List.forall_mem_cons.2 ⟨subd19_2_1080, List.forall_mem_cons.2 ⟨subd19_2_1081, List.forall_mem_cons.2 ⟨subd19_2_1082, List.forall_mem_cons.2 ⟨subd19_2_1083, List.forall_mem_cons.2 ⟨subd19_2_1084, List.forall_mem_cons.2 ⟨subd19_2_1085, List.forall_mem_cons.2 ⟨subd19_2_1086, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem ld_okd19_3 : ldCheck G d19_3.U d19_3.ms ldd19_3 = true := by decide +kernel
theorem pre_okd19_3 : subPre G cell19 d19_3 = true := by decide +kernel

end ReflectZphi.Data.Cert5.C143
