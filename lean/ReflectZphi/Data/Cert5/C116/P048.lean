import ReflectZphi.Data.Cert5.C116.Base

namespace ReflectZphi.Data.Cert5.C116

open ReflectZphi ReflectZphi.Lattice ReflectZphi.PolyEnum ReflectZphi.RootNorms
  ReflectZphi.Enum ReflectZphi.Cells ReflectZphi.Check ReflectZphi.Split
  ReflectZphi.FastLeaf ReflectZphi.Sublat

theorem subd9_1_4832 : subd9_1 [7, 5, -2] = true := by decide +kernel
theorem subd9_1_4833 : subd9_1 [7, 5, -1] = true := by decide +kernel
theorem subd9_1_4834 : subd9_1 [7, 5, 0] = true := by decide +kernel
theorem subd9_1_4835 : subd9_1 [7, 5, 1] = true := by decide +kernel
theorem subd9_1_4836 : subd9_1 [7, 5, 2] = true := by decide +kernel
theorem subd9_1_4837 : subd9_1 [7, 5, 3] = true := by decide +kernel
theorem subd9_1_4838 : subd9_1 [7, 5, 4] = true := by decide +kernel
theorem subd9_1_4839 : subd9_1 [7, 5, 5] = true := by decide +kernel
theorem subd9_1_4840 : subd9_1 [7, 5, 6] = true := by decide +kernel
theorem subd9_1_4841 : subd9_1 [7, 5, 7] = true := by decide +kernel
theorem subd9_1_4842 : subd9_1 [7, 5, 8] = true := by decide +kernel
theorem subd9_1_4843 : subd9_1 [7, 5, 9] = true := by decide +kernel
theorem subd9_1_4844 : subd9_1 [7, 5, 10] = true := by decide +kernel
theorem subd9_1_4845 : subd9_1 [7, 6, -6] = true := by decide +kernel
theorem subd9_1_4846 : subd9_1 [7, 6, -5] = true := by decide +kernel
theorem subd9_1_4847 : subd9_1 [7, 6, -4] = true := by decide +kernel
theorem subd9_1_4848 : subd9_1 [7, 6, -3] = true := by decide +kernel
theorem subd9_1_4849 : subd9_1 [7, 6, -2] = true := by decide +kernel
theorem subd9_1_4850 : subd9_1 [7, 6, -1] = true := by decide +kernel
theorem subd9_1_4851 : subd9_1 [7, 6, 0] = true := by decide +kernel
theorem subd9_1_4852 : subd9_1 [7, 6, 1] = true := by decide +kernel
theorem subd9_1_4853 : subd9_1 [7, 6, 2] = true := by decide +kernel
theorem subd9_1_4854 : subd9_1 [7, 6, 3] = true := by decide +kernel
theorem subd9_1_4855 : subd9_1 [7, 6, 4] = true := by decide +kernel
theorem subd9_1_4856 : subd9_1 [7, 6, 5] = true := by decide +kernel
theorem subd9_1_4857 : subd9_1 [7, 6, 6] = true := by decide +kernel
theorem subd9_1_4858 : subd9_1 [7, 6, 7] = true := by decide +kernel
theorem subd9_1_4859 : subd9_1 [7, 6, 8] = true := by decide +kernel
theorem subd9_1_4860 : subd9_1 [7, 6, 9] = true := by decide +kernel
theorem subd9_1_4861 : subd9_1 [7, 6, 10] = true := by decide +kernel
theorem subd9_1_4862 : subd9_1 [7, 7, -5] = true := by decide +kernel
theorem subd9_1_4863 : subd9_1 [7, 7, -4] = true := by decide +kernel
theorem sbd9_1_151 : ∀ q ∈ blkd9_1_151, subd9_1 q = true := by
  unfold blkd9_1_151
  exact List.forall_mem_cons.2 ⟨subd9_1_4832, List.forall_mem_cons.2 ⟨subd9_1_4833, List.forall_mem_cons.2 ⟨subd9_1_4834, List.forall_mem_cons.2 ⟨subd9_1_4835, List.forall_mem_cons.2 ⟨subd9_1_4836, List.forall_mem_cons.2 ⟨subd9_1_4837, List.forall_mem_cons.2 ⟨subd9_1_4838, List.forall_mem_cons.2 ⟨subd9_1_4839, List.forall_mem_cons.2 ⟨subd9_1_4840, List.forall_mem_cons.2 ⟨subd9_1_4841, List.forall_mem_cons.2 ⟨subd9_1_4842, List.forall_mem_cons.2 ⟨subd9_1_4843, List.forall_mem_cons.2 ⟨subd9_1_4844, List.forall_mem_cons.2 ⟨subd9_1_4845, List.forall_mem_cons.2 ⟨subd9_1_4846, List.forall_mem_cons.2 ⟨subd9_1_4847, List.forall_mem_cons.2 ⟨subd9_1_4848, List.forall_mem_cons.2 ⟨subd9_1_4849, List.forall_mem_cons.2 ⟨subd9_1_4850, List.forall_mem_cons.2 ⟨subd9_1_4851, List.forall_mem_cons.2 ⟨subd9_1_4852, List.forall_mem_cons.2 ⟨subd9_1_4853, List.forall_mem_cons.2 ⟨subd9_1_4854, List.forall_mem_cons.2 ⟨subd9_1_4855, List.forall_mem_cons.2 ⟨subd9_1_4856, List.forall_mem_cons.2 ⟨subd9_1_4857, List.forall_mem_cons.2 ⟨subd9_1_4858, List.forall_mem_cons.2 ⟨subd9_1_4859, List.forall_mem_cons.2 ⟨subd9_1_4860, List.forall_mem_cons.2 ⟨subd9_1_4861, List.forall_mem_cons.2 ⟨subd9_1_4862, List.forall_mem_cons.2 ⟨subd9_1_4863, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4864 : subd9_1 [7, 7, -3] = true := by decide +kernel
theorem subd9_1_4865 : subd9_1 [7, 7, -2] = true := by decide +kernel
theorem subd9_1_4866 : subd9_1 [7, 7, -1] = true := by decide +kernel
theorem subd9_1_4867 : subd9_1 [7, 7, 0] = true := by decide +kernel
theorem subd9_1_4868 : subd9_1 [7, 7, 1] = true := by decide +kernel
theorem subd9_1_4869 : subd9_1 [7, 7, 2] = true := by decide +kernel
theorem subd9_1_4870 : subd9_1 [7, 7, 3] = true := by decide +kernel
theorem subd9_1_4871 : subd9_1 [7, 7, 4] = true := by decide +kernel
theorem subd9_1_4872 : subd9_1 [7, 7, 5] = true := by decide +kernel
theorem subd9_1_4873 : subd9_1 [7, 7, 6] = true := by decide +kernel
theorem subd9_1_4874 : subd9_1 [7, 7, 7] = true := by decide +kernel
theorem subd9_1_4875 : subd9_1 [7, 7, 8] = true := by decide +kernel
theorem subd9_1_4876 : subd9_1 [7, 7, 9] = true := by decide +kernel
theorem subd9_1_4877 : subd9_1 [7, 7, 10] = true := by decide +kernel
theorem subd9_1_4878 : subd9_1 [7, 8, -4] = true := by decide +kernel
theorem subd9_1_4879 : subd9_1 [7, 8, -3] = true := by decide +kernel
theorem subd9_1_4880 : subd9_1 [7, 8, -2] = true := by decide +kernel
theorem subd9_1_4881 : subd9_1 [7, 8, -1] = true := by decide +kernel
theorem subd9_1_4882 : subd9_1 [7, 8, 0] = true := by decide +kernel
theorem subd9_1_4883 : subd9_1 [7, 8, 1] = true := by decide +kernel
theorem subd9_1_4884 : subd9_1 [7, 8, 2] = true := by decide +kernel
theorem subd9_1_4885 : subd9_1 [7, 8, 3] = true := by decide +kernel
theorem subd9_1_4886 : subd9_1 [7, 8, 4] = true := by decide +kernel
theorem subd9_1_4887 : subd9_1 [7, 8, 5] = true := by decide +kernel
theorem subd9_1_4888 : subd9_1 [7, 8, 6] = true := by decide +kernel
theorem subd9_1_4889 : subd9_1 [7, 8, 7] = true := by decide +kernel
theorem subd9_1_4890 : subd9_1 [7, 8, 8] = true := by decide +kernel
theorem subd9_1_4891 : subd9_1 [7, 8, 9] = true := by decide +kernel
theorem subd9_1_4892 : subd9_1 [7, 8, 10] = true := by decide +kernel
theorem subd9_1_4893 : subd9_1 [7, 9] = true := by decide +kernel
theorem subd9_1_4894 : subd9_1 [7, 10] = true := by decide +kernel
theorem subd9_1_4895 : subd9_1 [7, 11] = true := by decide +kernel
theorem sbd9_1_152 : ∀ q ∈ blkd9_1_152, subd9_1 q = true := by
  unfold blkd9_1_152
  exact List.forall_mem_cons.2 ⟨subd9_1_4864, List.forall_mem_cons.2 ⟨subd9_1_4865, List.forall_mem_cons.2 ⟨subd9_1_4866, List.forall_mem_cons.2 ⟨subd9_1_4867, List.forall_mem_cons.2 ⟨subd9_1_4868, List.forall_mem_cons.2 ⟨subd9_1_4869, List.forall_mem_cons.2 ⟨subd9_1_4870, List.forall_mem_cons.2 ⟨subd9_1_4871, List.forall_mem_cons.2 ⟨subd9_1_4872, List.forall_mem_cons.2 ⟨subd9_1_4873, List.forall_mem_cons.2 ⟨subd9_1_4874, List.forall_mem_cons.2 ⟨subd9_1_4875, List.forall_mem_cons.2 ⟨subd9_1_4876, List.forall_mem_cons.2 ⟨subd9_1_4877, List.forall_mem_cons.2 ⟨subd9_1_4878, List.forall_mem_cons.2 ⟨subd9_1_4879, List.forall_mem_cons.2 ⟨subd9_1_4880, List.forall_mem_cons.2 ⟨subd9_1_4881, List.forall_mem_cons.2 ⟨subd9_1_4882, List.forall_mem_cons.2 ⟨subd9_1_4883, List.forall_mem_cons.2 ⟨subd9_1_4884, List.forall_mem_cons.2 ⟨subd9_1_4885, List.forall_mem_cons.2 ⟨subd9_1_4886, List.forall_mem_cons.2 ⟨subd9_1_4887, List.forall_mem_cons.2 ⟨subd9_1_4888, List.forall_mem_cons.2 ⟨subd9_1_4889, List.forall_mem_cons.2 ⟨subd9_1_4890, List.forall_mem_cons.2 ⟨subd9_1_4891, List.forall_mem_cons.2 ⟨subd9_1_4892, List.forall_mem_cons.2 ⟨subd9_1_4893, List.forall_mem_cons.2 ⟨subd9_1_4894, List.forall_mem_cons.2 ⟨subd9_1_4895, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4896 : subd9_1 [7, 12] = true := by decide +kernel
theorem subd9_1_4897 : subd9_1 [8, -7] = true := by decide +kernel
theorem subd9_1_4898 : subd9_1 [8, -6] = true := by decide +kernel
theorem subd9_1_4899 : subd9_1 [8, -5] = true := by decide +kernel
theorem subd9_1_4900 : subd9_1 [8, -4] = true := by decide +kernel
theorem subd9_1_4901 : subd9_1 [8, -3] = true := by decide +kernel
theorem subd9_1_4902 : subd9_1 [8, -2, -8] = true := by decide +kernel
theorem subd9_1_4903 : subd9_1 [8, -2, -7] = true := by decide +kernel
theorem subd9_1_4904 : subd9_1 [8, -2, -6] = true := by decide +kernel
theorem subd9_1_4905 : subd9_1 [8, -2, -5] = true := by decide +kernel
theorem subd9_1_4906 : subd9_1 [8, -2, -4] = true := by decide +kernel
theorem subd9_1_4907 : subd9_1 [8, -2, -3] = true := by decide +kernel
theorem subd9_1_4908 : subd9_1 [8, -2, -2] = true := by decide +kernel
theorem subd9_1_4909 : subd9_1 [8, -2, -1] = true := by decide +kernel
theorem subd9_1_4910 : subd9_1 [8, -2, 0] = true := by decide +kernel
theorem subd9_1_4911 : subd9_1 [8, -2, 1] = true := by decide +kernel
theorem subd9_1_4912 : subd9_1 [8, -2, 2] = true := by decide +kernel
theorem subd9_1_4913 : subd9_1 [8, -2, 3] = true := by decide +kernel
theorem subd9_1_4914 : subd9_1 [8, -2, 4] = true := by decide +kernel
theorem subd9_1_4915 : subd9_1 [8, -2, 5] = true := by decide +kernel
theorem subd9_1_4916 : subd9_1 [8, -2, 6] = true := by decide +kernel
theorem subd9_1_4917 : subd9_1 [8, -1, -8] = true := by decide +kernel
theorem subd9_1_4918 : subd9_1 [8, -1, -7] = true := by decide +kernel
theorem subd9_1_4919 : subd9_1 [8, -1, -6] = true := by decide +kernel
theorem subd9_1_4920 : subd9_1 [8, -1, -5] = true := by decide +kernel
theorem subd9_1_4921 : subd9_1 [8, -1, -4] = true := by decide +kernel
theorem subd9_1_4922 : subd9_1 [8, -1, -3] = true := by decide +kernel
theorem subd9_1_4923 : subd9_1 [8, -1, -2] = true := by decide +kernel
theorem subd9_1_4924 : subd9_1 [8, -1, -1] = true := by decide +kernel
theorem subd9_1_4925 : subd9_1 [8, -1, 0] = true := by decide +kernel
theorem subd9_1_4926 : subd9_1 [8, -1, 1] = true := by decide +kernel
theorem subd9_1_4927 : subd9_1 [8, -1, 2] = true := by decide +kernel
theorem sbd9_1_153 : ∀ q ∈ blkd9_1_153, subd9_1 q = true := by
  unfold blkd9_1_153
  exact List.forall_mem_cons.2 ⟨subd9_1_4896, List.forall_mem_cons.2 ⟨subd9_1_4897, List.forall_mem_cons.2 ⟨subd9_1_4898, List.forall_mem_cons.2 ⟨subd9_1_4899, List.forall_mem_cons.2 ⟨subd9_1_4900, List.forall_mem_cons.2 ⟨subd9_1_4901, List.forall_mem_cons.2 ⟨subd9_1_4902, List.forall_mem_cons.2 ⟨subd9_1_4903, List.forall_mem_cons.2 ⟨subd9_1_4904, List.forall_mem_cons.2 ⟨subd9_1_4905, List.forall_mem_cons.2 ⟨subd9_1_4906, List.forall_mem_cons.2 ⟨subd9_1_4907, List.forall_mem_cons.2 ⟨subd9_1_4908, List.forall_mem_cons.2 ⟨subd9_1_4909, List.forall_mem_cons.2 ⟨subd9_1_4910, List.forall_mem_cons.2 ⟨subd9_1_4911, List.forall_mem_cons.2 ⟨subd9_1_4912, List.forall_mem_cons.2 ⟨subd9_1_4913, List.forall_mem_cons.2 ⟨subd9_1_4914, List.forall_mem_cons.2 ⟨subd9_1_4915, List.forall_mem_cons.2 ⟨subd9_1_4916, List.forall_mem_cons.2 ⟨subd9_1_4917, List.forall_mem_cons.2 ⟨subd9_1_4918, List.forall_mem_cons.2 ⟨subd9_1_4919, List.forall_mem_cons.2 ⟨subd9_1_4920, List.forall_mem_cons.2 ⟨subd9_1_4921, List.forall_mem_cons.2 ⟨subd9_1_4922, List.forall_mem_cons.2 ⟨subd9_1_4923, List.forall_mem_cons.2 ⟨subd9_1_4924, List.forall_mem_cons.2 ⟨subd9_1_4925, List.forall_mem_cons.2 ⟨subd9_1_4926, List.forall_mem_cons.2 ⟨subd9_1_4927, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4928 : subd9_1 [8, -1, 3] = true := by decide +kernel
theorem subd9_1_4929 : subd9_1 [8, -1, 4] = true := by decide +kernel
theorem subd9_1_4930 : subd9_1 [8, -1, 5] = true := by decide +kernel
theorem subd9_1_4931 : subd9_1 [8, -1, 6] = true := by decide +kernel
theorem subd9_1_4932 : subd9_1 [8, 0, -8] = true := by decide +kernel
theorem subd9_1_4933 : subd9_1 [8, 0, -7] = true := by decide +kernel
theorem subd9_1_4934 : subd9_1 [8, 0, -6] = true := by decide +kernel
theorem subd9_1_4935 : subd9_1 [8, 0, -5] = true := by decide +kernel
theorem subd9_1_4936 : subd9_1 [8, 0, -4] = true := by decide +kernel
theorem subd9_1_4937 : subd9_1 [8, 0, -3] = true := by decide +kernel
theorem subd9_1_4938 : subd9_1 [8, 0, -2] = true := by decide +kernel
theorem subd9_1_4939 : subd9_1 [8, 0, -1] = true := by decide +kernel
theorem subd9_1_4940 : subd9_1 [8, 0, 0] = true := by decide +kernel
theorem subd9_1_4941 : subd9_1 [8, 0, 1] = true := by decide +kernel
theorem subd9_1_4942 : subd9_1 [8, 0, 2] = true := by decide +kernel
theorem subd9_1_4943 : subd9_1 [8, 0, 3] = true := by decide +kernel
theorem subd9_1_4944 : subd9_1 [8, 0, 4] = true := by decide +kernel
theorem subd9_1_4945 : subd9_1 [8, 0, 5] = true := by decide +kernel
theorem subd9_1_4946 : subd9_1 [8, 0, 6] = true := by decide +kernel
theorem subd9_1_4947 : subd9_1 [8, 0, 7] = true := by decide +kernel
theorem subd9_1_4948 : subd9_1 [8, 1, -8] = true := by decide +kernel
theorem subd9_1_4949 : subd9_1 [8, 1, -7] = true := by decide +kernel
theorem subd9_1_4950 : subd9_1 [8, 1, -6] = true := by decide +kernel
theorem subd9_1_4951 : subd9_1 [8, 1, -5] = true := by decide +kernel
theorem subd9_1_4952 : subd9_1 [8, 1, -4] = true := by decide +kernel
theorem subd9_1_4953 : subd9_1 [8, 1, -3] = true := by decide +kernel
theorem subd9_1_4954 : subd9_1 [8, 1, -2] = true := by decide +kernel
theorem subd9_1_4955 : subd9_1 [8, 1, -1] = true := by decide +kernel
theorem subd9_1_4956 : subd9_1 [8, 1, 0] = true := by decide +kernel
theorem subd9_1_4957 : subd9_1 [8, 1, 1] = true := by decide +kernel
theorem subd9_1_4958 : subd9_1 [8, 1, 2] = true := by decide +kernel
theorem subd9_1_4959 : subd9_1 [8, 1, 3] = true := by decide +kernel
theorem sbd9_1_154 : ∀ q ∈ blkd9_1_154, subd9_1 q = true := by
  unfold blkd9_1_154
  exact List.forall_mem_cons.2 ⟨subd9_1_4928, List.forall_mem_cons.2 ⟨subd9_1_4929, List.forall_mem_cons.2 ⟨subd9_1_4930, List.forall_mem_cons.2 ⟨subd9_1_4931, List.forall_mem_cons.2 ⟨subd9_1_4932, List.forall_mem_cons.2 ⟨subd9_1_4933, List.forall_mem_cons.2 ⟨subd9_1_4934, List.forall_mem_cons.2 ⟨subd9_1_4935, List.forall_mem_cons.2 ⟨subd9_1_4936, List.forall_mem_cons.2 ⟨subd9_1_4937, List.forall_mem_cons.2 ⟨subd9_1_4938, List.forall_mem_cons.2 ⟨subd9_1_4939, List.forall_mem_cons.2 ⟨subd9_1_4940, List.forall_mem_cons.2 ⟨subd9_1_4941, List.forall_mem_cons.2 ⟨subd9_1_4942, List.forall_mem_cons.2 ⟨subd9_1_4943, List.forall_mem_cons.2 ⟨subd9_1_4944, List.forall_mem_cons.2 ⟨subd9_1_4945, List.forall_mem_cons.2 ⟨subd9_1_4946, List.forall_mem_cons.2 ⟨subd9_1_4947, List.forall_mem_cons.2 ⟨subd9_1_4948, List.forall_mem_cons.2 ⟨subd9_1_4949, List.forall_mem_cons.2 ⟨subd9_1_4950, List.forall_mem_cons.2 ⟨subd9_1_4951, List.forall_mem_cons.2 ⟨subd9_1_4952, List.forall_mem_cons.2 ⟨subd9_1_4953, List.forall_mem_cons.2 ⟨subd9_1_4954, List.forall_mem_cons.2 ⟨subd9_1_4955, List.forall_mem_cons.2 ⟨subd9_1_4956, List.forall_mem_cons.2 ⟨subd9_1_4957, List.forall_mem_cons.2 ⟨subd9_1_4958, List.forall_mem_cons.2 ⟨subd9_1_4959, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4960 : subd9_1 [8, 1, 4] = true := by decide +kernel
theorem subd9_1_4961 : subd9_1 [8, 1, 5] = true := by decide +kernel
theorem subd9_1_4962 : subd9_1 [8, 1, 6] = true := by decide +kernel
theorem subd9_1_4963 : subd9_1 [8, 1, 7] = true := by decide +kernel
theorem subd9_1_4964 : subd9_1 [8, 1, 8] = true := by decide +kernel
theorem subd9_1_4965 : subd9_1 [8, 2, -7] = true := by decide +kernel
theorem subd9_1_4966 : subd9_1 [8, 2, -6] = true := by decide +kernel
theorem subd9_1_4967 : subd9_1 [8, 2, -5] = true := by decide +kernel
theorem subd9_1_4968 : subd9_1 [8, 2, -4] = true := by decide +kernel
theorem subd9_1_4969 : subd9_1 [8, 2, -3] = true := by decide +kernel
theorem subd9_1_4970 : subd9_1 [8, 2, -2] = true := by decide +kernel
theorem subd9_1_4971 : subd9_1 [8, 2, -1] = true := by decide +kernel
theorem subd9_1_4972 : subd9_1 [8, 2, 0] = true := by decide +kernel
theorem subd9_1_4973 : subd9_1 [8, 2, 1] = true := by decide +kernel
theorem subd9_1_4974 : subd9_1 [8, 2, 2] = true := by decide +kernel
theorem subd9_1_4975 : subd9_1 [8, 2, 3] = true := by decide +kernel
theorem subd9_1_4976 : subd9_1 [8, 2, 4] = true := by decide +kernel
theorem subd9_1_4977 : subd9_1 [8, 2, 5] = true := by decide +kernel
theorem subd9_1_4978 : subd9_1 [8, 2, 6] = true := by decide +kernel
theorem subd9_1_4979 : subd9_1 [8, 2, 7] = true := by decide +kernel
theorem subd9_1_4980 : subd9_1 [8, 2, 8] = true := by decide +kernel
theorem subd9_1_4981 : subd9_1 [8, 3, -7] = true := by decide +kernel
theorem subd9_1_4982 : subd9_1 [8, 3, -6] = true := by decide +kernel
theorem subd9_1_4983 : subd9_1 [8, 3, -5] = true := by decide +kernel
theorem subd9_1_4984 : subd9_1 [8, 3, -4] = true := by decide +kernel
theorem subd9_1_4985 : subd9_1 [8, 3, -3] = true := by decide +kernel
theorem subd9_1_4986 : subd9_1 [8, 3, -2] = true := by decide +kernel
theorem subd9_1_4987 : subd9_1 [8, 3, -1] = true := by decide +kernel
theorem subd9_1_4988 : subd9_1 [8, 3, 0] = true := by decide +kernel
theorem subd9_1_4989 : subd9_1 [8, 3, 1] = true := by decide +kernel
theorem subd9_1_4990 : subd9_1 [8, 3, 2] = true := by decide +kernel
theorem subd9_1_4991 : subd9_1 [8, 3, 3] = true := by decide +kernel
theorem sbd9_1_155 : ∀ q ∈ blkd9_1_155, subd9_1 q = true := by
  unfold blkd9_1_155
  exact List.forall_mem_cons.2 ⟨subd9_1_4960, List.forall_mem_cons.2 ⟨subd9_1_4961, List.forall_mem_cons.2 ⟨subd9_1_4962, List.forall_mem_cons.2 ⟨subd9_1_4963, List.forall_mem_cons.2 ⟨subd9_1_4964, List.forall_mem_cons.2 ⟨subd9_1_4965, List.forall_mem_cons.2 ⟨subd9_1_4966, List.forall_mem_cons.2 ⟨subd9_1_4967, List.forall_mem_cons.2 ⟨subd9_1_4968, List.forall_mem_cons.2 ⟨subd9_1_4969, List.forall_mem_cons.2 ⟨subd9_1_4970, List.forall_mem_cons.2 ⟨subd9_1_4971, List.forall_mem_cons.2 ⟨subd9_1_4972, List.forall_mem_cons.2 ⟨subd9_1_4973, List.forall_mem_cons.2 ⟨subd9_1_4974, List.forall_mem_cons.2 ⟨subd9_1_4975, List.forall_mem_cons.2 ⟨subd9_1_4976, List.forall_mem_cons.2 ⟨subd9_1_4977, List.forall_mem_cons.2 ⟨subd9_1_4978, List.forall_mem_cons.2 ⟨subd9_1_4979, List.forall_mem_cons.2 ⟨subd9_1_4980, List.forall_mem_cons.2 ⟨subd9_1_4981, List.forall_mem_cons.2 ⟨subd9_1_4982, List.forall_mem_cons.2 ⟨subd9_1_4983, List.forall_mem_cons.2 ⟨subd9_1_4984, List.forall_mem_cons.2 ⟨subd9_1_4985, List.forall_mem_cons.2 ⟨subd9_1_4986, List.forall_mem_cons.2 ⟨subd9_1_4987, List.forall_mem_cons.2 ⟨subd9_1_4988, List.forall_mem_cons.2 ⟨subd9_1_4989, List.forall_mem_cons.2 ⟨subd9_1_4990, List.forall_mem_cons.2 ⟨subd9_1_4991, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_4992 : subd9_1 [8, 3, 4] = true := by decide +kernel
theorem subd9_1_4993 : subd9_1 [8, 3, 5] = true := by decide +kernel
theorem subd9_1_4994 : subd9_1 [8, 3, 6] = true := by decide +kernel
theorem subd9_1_4995 : subd9_1 [8, 3, 7] = true := by decide +kernel
theorem subd9_1_4996 : subd9_1 [8, 3, 8] = true := by decide +kernel
theorem subd9_1_4997 : subd9_1 [8, 3, 9] = true := by decide +kernel
theorem subd9_1_4998 : subd9_1 [8, 4, -6] = true := by decide +kernel
theorem subd9_1_4999 : subd9_1 [8, 4, -5] = true := by decide +kernel
theorem subd9_1_5000 : subd9_1 [8, 4, -4] = true := by decide +kernel
theorem subd9_1_5001 : subd9_1 [8, 4, -3] = true := by decide +kernel
theorem subd9_1_5002 : subd9_1 [8, 4, -2] = true := by decide +kernel
theorem subd9_1_5003 : subd9_1 [8, 4, -1] = true := by decide +kernel
theorem subd9_1_5004 : subd9_1 [8, 4, 0] = true := by decide +kernel
theorem subd9_1_5005 : subd9_1 [8, 4, 1] = true := by decide +kernel
theorem subd9_1_5006 : subd9_1 [8, 4, 2] = true := by decide +kernel
theorem subd9_1_5007 : subd9_1 [8, 4, 3] = true := by decide +kernel
theorem subd9_1_5008 : subd9_1 [8, 4, 4] = true := by decide +kernel
theorem subd9_1_5009 : subd9_1 [8, 4, 5] = true := by decide +kernel
theorem subd9_1_5010 : subd9_1 [8, 4, 6] = true := by decide +kernel
theorem subd9_1_5011 : subd9_1 [8, 4, 7] = true := by decide +kernel
theorem subd9_1_5012 : subd9_1 [8, 4, 8] = true := by decide +kernel
theorem subd9_1_5013 : subd9_1 [8, 4, 9] = true := by decide +kernel
theorem subd9_1_5014 : subd9_1 [8, 5, -6] = true := by decide +kernel
theorem subd9_1_5015 : subd9_1 [8, 5, -5] = true := by decide +kernel
theorem subd9_1_5016 : subd9_1 [8, 5, -4] = true := by decide +kernel
theorem subd9_1_5017 : subd9_1 [8, 5, -3] = true := by decide +kernel
theorem subd9_1_5018 : subd9_1 [8, 5, -2] = true := by decide +kernel
theorem subd9_1_5019 : subd9_1 [8, 5, -1] = true := by decide +kernel
theorem subd9_1_5020 : subd9_1 [8, 5, 0] = true := by decide +kernel
theorem subd9_1_5021 : subd9_1 [8, 5, 1] = true := by decide +kernel
theorem subd9_1_5022 : subd9_1 [8, 5, 2] = true := by decide +kernel
theorem subd9_1_5023 : subd9_1 [8, 5, 3] = true := by decide +kernel
theorem sbd9_1_156 : ∀ q ∈ blkd9_1_156, subd9_1 q = true := by
  unfold blkd9_1_156
  exact List.forall_mem_cons.2 ⟨subd9_1_4992, List.forall_mem_cons.2 ⟨subd9_1_4993, List.forall_mem_cons.2 ⟨subd9_1_4994, List.forall_mem_cons.2 ⟨subd9_1_4995, List.forall_mem_cons.2 ⟨subd9_1_4996, List.forall_mem_cons.2 ⟨subd9_1_4997, List.forall_mem_cons.2 ⟨subd9_1_4998, List.forall_mem_cons.2 ⟨subd9_1_4999, List.forall_mem_cons.2 ⟨subd9_1_5000, List.forall_mem_cons.2 ⟨subd9_1_5001, List.forall_mem_cons.2 ⟨subd9_1_5002, List.forall_mem_cons.2 ⟨subd9_1_5003, List.forall_mem_cons.2 ⟨subd9_1_5004, List.forall_mem_cons.2 ⟨subd9_1_5005, List.forall_mem_cons.2 ⟨subd9_1_5006, List.forall_mem_cons.2 ⟨subd9_1_5007, List.forall_mem_cons.2 ⟨subd9_1_5008, List.forall_mem_cons.2 ⟨subd9_1_5009, List.forall_mem_cons.2 ⟨subd9_1_5010, List.forall_mem_cons.2 ⟨subd9_1_5011, List.forall_mem_cons.2 ⟨subd9_1_5012, List.forall_mem_cons.2 ⟨subd9_1_5013, List.forall_mem_cons.2 ⟨subd9_1_5014, List.forall_mem_cons.2 ⟨subd9_1_5015, List.forall_mem_cons.2 ⟨subd9_1_5016, List.forall_mem_cons.2 ⟨subd9_1_5017, List.forall_mem_cons.2 ⟨subd9_1_5018, List.forall_mem_cons.2 ⟨subd9_1_5019, List.forall_mem_cons.2 ⟨subd9_1_5020, List.forall_mem_cons.2 ⟨subd9_1_5021, List.forall_mem_cons.2 ⟨subd9_1_5022, List.forall_mem_cons.2 ⟨subd9_1_5023, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_5024 : subd9_1 [8, 5, 4] = true := by decide +kernel
theorem subd9_1_5025 : subd9_1 [8, 5, 5] = true := by decide +kernel
theorem subd9_1_5026 : subd9_1 [8, 5, 6] = true := by decide +kernel
theorem subd9_1_5027 : subd9_1 [8, 5, 7] = true := by decide +kernel
theorem subd9_1_5028 : subd9_1 [8, 5, 8] = true := by decide +kernel
theorem subd9_1_5029 : subd9_1 [8, 5, 9] = true := by decide +kernel
theorem subd9_1_5030 : subd9_1 [8, 6, -5] = true := by decide +kernel
theorem subd9_1_5031 : subd9_1 [8, 6, -4] = true := by decide +kernel
theorem subd9_1_5032 : subd9_1 [8, 6, -3] = true := by decide +kernel
theorem subd9_1_5033 : subd9_1 [8, 6, -2] = true := by decide +kernel
theorem subd9_1_5034 : subd9_1 [8, 6, -1] = true := by decide +kernel
theorem subd9_1_5035 : subd9_1 [8, 6, 0] = true := by decide +kernel
theorem subd9_1_5036 : subd9_1 [8, 6, 1] = true := by decide +kernel
theorem subd9_1_5037 : subd9_1 [8, 6, 2] = true := by decide +kernel
theorem subd9_1_5038 : subd9_1 [8, 6, 3] = true := by decide +kernel
theorem subd9_1_5039 : subd9_1 [8, 6, 4] = true := by decide +kernel
theorem subd9_1_5040 : subd9_1 [8, 6, 5] = true := by decide +kernel
theorem subd9_1_5041 : subd9_1 [8, 6, 6] = true := by decide +kernel
theorem subd9_1_5042 : subd9_1 [8, 6, 7] = true := by decide +kernel
theorem subd9_1_5043 : subd9_1 [8, 6, 8] = true := by decide +kernel
theorem subd9_1_5044 : subd9_1 [8, 6, 9] = true := by decide +kernel
theorem subd9_1_5045 : subd9_1 [8, 7] = true := by decide +kernel
theorem subd9_1_5046 : subd9_1 [8, 8] = true := by decide +kernel
theorem subd9_1_5047 : subd9_1 [8, 9] = true := by decide +kernel
theorem subd9_1_5048 : subd9_1 [8, 10] = true := by decide +kernel
theorem subd9_1_5049 : subd9_1 [8, 11] = true := by decide +kernel
theorem subd9_1_5050 : subd9_1 [9, -6] = true := by decide +kernel
theorem subd9_1_5051 : subd9_1 [9, -5] = true := by decide +kernel
theorem subd9_1_5052 : subd9_1 [9, -4] = true := by decide +kernel
theorem subd9_1_5053 : subd9_1 [9, -3] = true := by decide +kernel
theorem subd9_1_5054 : subd9_1 [9, -2] = true := by decide +kernel
theorem subd9_1_5055 : subd9_1 [9, -1] = true := by decide +kernel
theorem sbd9_1_157 : ∀ q ∈ blkd9_1_157, subd9_1 q = true := by
  unfold blkd9_1_157
  exact List.forall_mem_cons.2 ⟨subd9_1_5024, List.forall_mem_cons.2 ⟨subd9_1_5025, List.forall_mem_cons.2 ⟨subd9_1_5026, List.forall_mem_cons.2 ⟨subd9_1_5027, List.forall_mem_cons.2 ⟨subd9_1_5028, List.forall_mem_cons.2 ⟨subd9_1_5029, List.forall_mem_cons.2 ⟨subd9_1_5030, List.forall_mem_cons.2 ⟨subd9_1_5031, List.forall_mem_cons.2 ⟨subd9_1_5032, List.forall_mem_cons.2 ⟨subd9_1_5033, List.forall_mem_cons.2 ⟨subd9_1_5034, List.forall_mem_cons.2 ⟨subd9_1_5035, List.forall_mem_cons.2 ⟨subd9_1_5036, List.forall_mem_cons.2 ⟨subd9_1_5037, List.forall_mem_cons.2 ⟨subd9_1_5038, List.forall_mem_cons.2 ⟨subd9_1_5039, List.forall_mem_cons.2 ⟨subd9_1_5040, List.forall_mem_cons.2 ⟨subd9_1_5041, List.forall_mem_cons.2 ⟨subd9_1_5042, List.forall_mem_cons.2 ⟨subd9_1_5043, List.forall_mem_cons.2 ⟨subd9_1_5044, List.forall_mem_cons.2 ⟨subd9_1_5045, List.forall_mem_cons.2 ⟨subd9_1_5046, List.forall_mem_cons.2 ⟨subd9_1_5047, List.forall_mem_cons.2 ⟨subd9_1_5048, List.forall_mem_cons.2 ⟨subd9_1_5049, List.forall_mem_cons.2 ⟨subd9_1_5050, List.forall_mem_cons.2 ⟨subd9_1_5051, List.forall_mem_cons.2 ⟨subd9_1_5052, List.forall_mem_cons.2 ⟨subd9_1_5053, List.forall_mem_cons.2 ⟨subd9_1_5054, List.forall_mem_cons.2 ⟨subd9_1_5055, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_5056 : subd9_1 [9, 0] = true := by decide +kernel
theorem subd9_1_5057 : subd9_1 [9, 1, -7] = true := by decide +kernel
theorem subd9_1_5058 : subd9_1 [9, 1, -6] = true := by decide +kernel
theorem subd9_1_5059 : subd9_1 [9, 1, -5] = true := by decide +kernel
theorem subd9_1_5060 : subd9_1 [9, 1, -4] = true := by decide +kernel
theorem subd9_1_5061 : subd9_1 [9, 1, -3] = true := by decide +kernel
theorem subd9_1_5062 : subd9_1 [9, 1, -2] = true := by decide +kernel
theorem subd9_1_5063 : subd9_1 [9, 1, -1] = true := by decide +kernel
theorem subd9_1_5064 : subd9_1 [9, 1, 0] = true := by decide +kernel
theorem subd9_1_5065 : subd9_1 [9, 1, 1] = true := by decide +kernel
theorem subd9_1_5066 : subd9_1 [9, 1, 2] = true := by decide +kernel
theorem subd9_1_5067 : subd9_1 [9, 1, 3] = true := by decide +kernel
theorem subd9_1_5068 : subd9_1 [9, 1, 4] = true := by decide +kernel
theorem subd9_1_5069 : subd9_1 [9, 1, 5] = true := by decide +kernel
theorem subd9_1_5070 : subd9_1 [9, 1, 6] = true := by decide +kernel
theorem subd9_1_5071 : subd9_1 [9, 1, 7] = true := by decide +kernel
theorem subd9_1_5072 : subd9_1 [9, 2, -6] = true := by decide +kernel
theorem subd9_1_5073 : subd9_1 [9, 2, -5] = true := by decide +kernel
theorem subd9_1_5074 : subd9_1 [9, 2, -4] = true := by decide +kernel
theorem subd9_1_5075 : subd9_1 [9, 2, -3] = true := by decide +kernel
theorem subd9_1_5076 : subd9_1 [9, 2, -2] = true := by decide +kernel
theorem subd9_1_5077 : subd9_1 [9, 2, -1] = true := by decide +kernel
theorem subd9_1_5078 : subd9_1 [9, 2, 0] = true := by decide +kernel
theorem subd9_1_5079 : subd9_1 [9, 2, 1] = true := by decide +kernel
theorem subd9_1_5080 : subd9_1 [9, 2, 2] = true := by decide +kernel
theorem subd9_1_5081 : subd9_1 [9, 2, 3] = true := by decide +kernel
theorem subd9_1_5082 : subd9_1 [9, 2, 4] = true := by decide +kernel
theorem subd9_1_5083 : subd9_1 [9, 2, 5] = true := by decide +kernel
theorem subd9_1_5084 : subd9_1 [9, 2, 6] = true := by decide +kernel
theorem subd9_1_5085 : subd9_1 [9, 2, 7] = true := by decide +kernel
theorem subd9_1_5086 : subd9_1 [9, 3, -6] = true := by decide +kernel
theorem subd9_1_5087 : subd9_1 [9, 3, -5] = true := by decide +kernel
theorem sbd9_1_158 : ∀ q ∈ blkd9_1_158, subd9_1 q = true := by
  unfold blkd9_1_158
  exact List.forall_mem_cons.2 ⟨subd9_1_5056, List.forall_mem_cons.2 ⟨subd9_1_5057, List.forall_mem_cons.2 ⟨subd9_1_5058, List.forall_mem_cons.2 ⟨subd9_1_5059, List.forall_mem_cons.2 ⟨subd9_1_5060, List.forall_mem_cons.2 ⟨subd9_1_5061, List.forall_mem_cons.2 ⟨subd9_1_5062, List.forall_mem_cons.2 ⟨subd9_1_5063, List.forall_mem_cons.2 ⟨subd9_1_5064, List.forall_mem_cons.2 ⟨subd9_1_5065, List.forall_mem_cons.2 ⟨subd9_1_5066, List.forall_mem_cons.2 ⟨subd9_1_5067, List.forall_mem_cons.2 ⟨subd9_1_5068, List.forall_mem_cons.2 ⟨subd9_1_5069, List.forall_mem_cons.2 ⟨subd9_1_5070, List.forall_mem_cons.2 ⟨subd9_1_5071, List.forall_mem_cons.2 ⟨subd9_1_5072, List.forall_mem_cons.2 ⟨subd9_1_5073, List.forall_mem_cons.2 ⟨subd9_1_5074, List.forall_mem_cons.2 ⟨subd9_1_5075, List.forall_mem_cons.2 ⟨subd9_1_5076, List.forall_mem_cons.2 ⟨subd9_1_5077, List.forall_mem_cons.2 ⟨subd9_1_5078, List.forall_mem_cons.2 ⟨subd9_1_5079, List.forall_mem_cons.2 ⟨subd9_1_5080, List.forall_mem_cons.2 ⟨subd9_1_5081, List.forall_mem_cons.2 ⟨subd9_1_5082, List.forall_mem_cons.2 ⟨subd9_1_5083, List.forall_mem_cons.2 ⟨subd9_1_5084, List.forall_mem_cons.2 ⟨subd9_1_5085, List.forall_mem_cons.2 ⟨subd9_1_5086, List.forall_mem_cons.2 ⟨subd9_1_5087, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_5088 : subd9_1 [9, 3, -4] = true := by decide +kernel
theorem subd9_1_5089 : subd9_1 [9, 3, -3] = true := by decide +kernel
theorem subd9_1_5090 : subd9_1 [9, 3, -2] = true := by decide +kernel
theorem subd9_1_5091 : subd9_1 [9, 3, -1] = true := by decide +kernel
theorem subd9_1_5092 : subd9_1 [9, 3, 0] = true := by decide +kernel
theorem subd9_1_5093 : subd9_1 [9, 3, 1] = true := by decide +kernel
theorem subd9_1_5094 : subd9_1 [9, 3, 2] = true := by decide +kernel
theorem subd9_1_5095 : subd9_1 [9, 3, 3] = true := by decide +kernel
theorem subd9_1_5096 : subd9_1 [9, 3, 4] = true := by decide +kernel
theorem subd9_1_5097 : subd9_1 [9, 3, 5] = true := by decide +kernel
theorem subd9_1_5098 : subd9_1 [9, 3, 6] = true := by decide +kernel
theorem subd9_1_5099 : subd9_1 [9, 3, 7] = true := by decide +kernel
theorem subd9_1_5100 : subd9_1 [9, 3, 8] = true := by decide +kernel
theorem subd9_1_5101 : subd9_1 [9, 4, -5] = true := by decide +kernel
theorem subd9_1_5102 : subd9_1 [9, 4, -4] = true := by decide +kernel
theorem subd9_1_5103 : subd9_1 [9, 4, -3] = true := by decide +kernel
theorem subd9_1_5104 : subd9_1 [9, 4, -2] = true := by decide +kernel
theorem subd9_1_5105 : subd9_1 [9, 4, -1] = true := by decide +kernel
theorem subd9_1_5106 : subd9_1 [9, 4, 0] = true := by decide +kernel
theorem subd9_1_5107 : subd9_1 [9, 4, 1] = true := by decide +kernel
theorem subd9_1_5108 : subd9_1 [9, 4, 2] = true := by decide +kernel
theorem subd9_1_5109 : subd9_1 [9, 4, 3] = true := by decide +kernel
theorem subd9_1_5110 : subd9_1 [9, 4, 4] = true := by decide +kernel
theorem subd9_1_5111 : subd9_1 [9, 4, 5] = true := by decide +kernel
theorem subd9_1_5112 : subd9_1 [9, 4, 6] = true := by decide +kernel
theorem subd9_1_5113 : subd9_1 [9, 4, 7] = true := by decide +kernel
theorem subd9_1_5114 : subd9_1 [9, 4, 8] = true := by decide +kernel
theorem subd9_1_5115 : subd9_1 [9, 5] = true := by decide +kernel
theorem subd9_1_5116 : subd9_1 [9, 6] = true := by decide +kernel
theorem subd9_1_5117 : subd9_1 [9, 7] = true := by decide +kernel
theorem subd9_1_5118 : subd9_1 [9, 8] = true := by decide +kernel
theorem subd9_1_5119 : subd9_1 [9, 9] = true := by decide +kernel
theorem sbd9_1_159 : ∀ q ∈ blkd9_1_159, subd9_1 q = true := by
  unfold blkd9_1_159
  exact List.forall_mem_cons.2 ⟨subd9_1_5088, List.forall_mem_cons.2 ⟨subd9_1_5089, List.forall_mem_cons.2 ⟨subd9_1_5090, List.forall_mem_cons.2 ⟨subd9_1_5091, List.forall_mem_cons.2 ⟨subd9_1_5092, List.forall_mem_cons.2 ⟨subd9_1_5093, List.forall_mem_cons.2 ⟨subd9_1_5094, List.forall_mem_cons.2 ⟨subd9_1_5095, List.forall_mem_cons.2 ⟨subd9_1_5096, List.forall_mem_cons.2 ⟨subd9_1_5097, List.forall_mem_cons.2 ⟨subd9_1_5098, List.forall_mem_cons.2 ⟨subd9_1_5099, List.forall_mem_cons.2 ⟨subd9_1_5100, List.forall_mem_cons.2 ⟨subd9_1_5101, List.forall_mem_cons.2 ⟨subd9_1_5102, List.forall_mem_cons.2 ⟨subd9_1_5103, List.forall_mem_cons.2 ⟨subd9_1_5104, List.forall_mem_cons.2 ⟨subd9_1_5105, List.forall_mem_cons.2 ⟨subd9_1_5106, List.forall_mem_cons.2 ⟨subd9_1_5107, List.forall_mem_cons.2 ⟨subd9_1_5108, List.forall_mem_cons.2 ⟨subd9_1_5109, List.forall_mem_cons.2 ⟨subd9_1_5110, List.forall_mem_cons.2 ⟨subd9_1_5111, List.forall_mem_cons.2 ⟨subd9_1_5112, List.forall_mem_cons.2 ⟨subd9_1_5113, List.forall_mem_cons.2 ⟨subd9_1_5114, List.forall_mem_cons.2 ⟨subd9_1_5115, List.forall_mem_cons.2 ⟨subd9_1_5116, List.forall_mem_cons.2 ⟨subd9_1_5117, List.forall_mem_cons.2 ⟨subd9_1_5118, List.forall_mem_cons.2 ⟨subd9_1_5119, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
theorem subd9_1_5120 : subd9_1 [9, 10] = true := by decide +kernel
theorem subd9_1_5121 : subd9_1 [10, -5] = true := by decide +kernel
theorem subd9_1_5122 : subd9_1 [10, -4] = true := by decide +kernel
theorem subd9_1_5123 : subd9_1 [10, -3] = true := by decide +kernel
theorem subd9_1_5124 : subd9_1 [10, -2] = true := by decide +kernel
theorem subd9_1_5125 : subd9_1 [10, -1] = true := by decide +kernel
theorem subd9_1_5126 : subd9_1 [10, 0] = true := by decide +kernel
theorem subd9_1_5127 : subd9_1 [10, 1] = true := by decide +kernel
theorem subd9_1_5128 : subd9_1 [10, 2] = true := by decide +kernel
theorem subd9_1_5129 : subd9_1 [10, 3] = true := by decide +kernel
theorem subd9_1_5130 : subd9_1 [10, 4] = true := by decide +kernel
theorem subd9_1_5131 : subd9_1 [10, 5] = true := by decide +kernel
theorem subd9_1_5132 : subd9_1 [10, 6] = true := by decide +kernel
theorem subd9_1_5133 : subd9_1 [10, 7] = true := by decide +kernel
theorem subd9_1_5134 : subd9_1 [10, 8] = true := by decide +kernel
theorem subd9_1_5135 : subd9_1 [10, 9] = true := by decide +kernel
theorem subd9_1_5136 : subd9_1 [11, -3] = true := by decide +kernel
theorem subd9_1_5137 : subd9_1 [11, -2] = true := by decide +kernel
theorem subd9_1_5138 : subd9_1 [11, -1] = true := by decide +kernel
theorem subd9_1_5139 : subd9_1 [11, 0] = true := by decide +kernel
theorem subd9_1_5140 : subd9_1 [11, 1] = true := by decide +kernel
theorem subd9_1_5141 : subd9_1 [11, 2] = true := by decide +kernel
theorem subd9_1_5142 : subd9_1 [11, 3] = true := by decide +kernel
theorem subd9_1_5143 : subd9_1 [11, 4] = true := by decide +kernel
theorem subd9_1_5144 : subd9_1 [11, 5] = true := by decide +kernel
theorem subd9_1_5145 : subd9_1 [11, 6] = true := by decide +kernel
theorem subd9_1_5146 : subd9_1 [11, 7] = true := by decide +kernel
theorem subd9_1_5147 : subd9_1 [11, 8] = true := by decide +kernel
theorem subd9_1_5148 : subd9_1 [12] = true := by decide +kernel
theorem sbd9_1_160 : ∀ q ∈ blkd9_1_160, subd9_1 q = true := by
  unfold blkd9_1_160
  exact List.forall_mem_cons.2 ⟨subd9_1_5120, List.forall_mem_cons.2 ⟨subd9_1_5121, List.forall_mem_cons.2 ⟨subd9_1_5122, List.forall_mem_cons.2 ⟨subd9_1_5123, List.forall_mem_cons.2 ⟨subd9_1_5124, List.forall_mem_cons.2 ⟨subd9_1_5125, List.forall_mem_cons.2 ⟨subd9_1_5126, List.forall_mem_cons.2 ⟨subd9_1_5127, List.forall_mem_cons.2 ⟨subd9_1_5128, List.forall_mem_cons.2 ⟨subd9_1_5129, List.forall_mem_cons.2 ⟨subd9_1_5130, List.forall_mem_cons.2 ⟨subd9_1_5131, List.forall_mem_cons.2 ⟨subd9_1_5132, List.forall_mem_cons.2 ⟨subd9_1_5133, List.forall_mem_cons.2 ⟨subd9_1_5134, List.forall_mem_cons.2 ⟨subd9_1_5135, List.forall_mem_cons.2 ⟨subd9_1_5136, List.forall_mem_cons.2 ⟨subd9_1_5137, List.forall_mem_cons.2 ⟨subd9_1_5138, List.forall_mem_cons.2 ⟨subd9_1_5139, List.forall_mem_cons.2 ⟨subd9_1_5140, List.forall_mem_cons.2 ⟨subd9_1_5141, List.forall_mem_cons.2 ⟨subd9_1_5142, List.forall_mem_cons.2 ⟨subd9_1_5143, List.forall_mem_cons.2 ⟨subd9_1_5144, List.forall_mem_cons.2 ⟨subd9_1_5145, List.forall_mem_cons.2 ⟨subd9_1_5146, List.forall_mem_cons.2 ⟨subd9_1_5147, List.forall_mem_cons.2 ⟨subd9_1_5148, List.forall_mem_nil _⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

end ReflectZphi.Data.Cert5.C116
