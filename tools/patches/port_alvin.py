"""Build-only port of AlVin to igraph 1.0 + modern libc++ (no arithmetic changes), plus one
memory-safety fix (2026-11-20): in find*PossibleNorms2, `vector<unsigned int> pow2({1})` has
size 1 but the loop writes pow2[i] for every prime factor, a heap overflow. It made AlVin
segfault intermittently (about half the runs on <-(-15+9w),1,1,1> over Q(sqrt13)); the
vector is now sized to the factor count.
Usage: python3 port_alvin.py <AlVin source dir>"""
import pathlib, re, sys
src = pathlib.Path(sys.argv[1])
subs_ig = [
    ("igraph_adjacency(&graph, &adjMat, IGRAPH_ADJ_UNDIRECTED)",
     "igraph_adjacency(&graph, &adjMat, IGRAPH_ADJ_UNDIRECTED, IGRAPH_NO_LOOPS)"),
    ("igraph_vector_ptr_t maps;", "igraph_vector_int_list_t maps;"),
    ("igraph_vector_ptr_init(&maps, 1);", "igraph_vector_int_list_init(&maps, 0);"),
    ("igraph_vector_ptr_size(&maps)", "igraph_vector_int_list_size(&maps)"),
    ("igraph_vector_t *v((igraph_vector_t *)igraph_vector_ptr_e(&maps, is));",
     "igraph_vector_int_t *v(igraph_vector_int_list_get_ptr(&maps, is));"),
    ("igraph_vector_ptr_destroy(&maps);", "igraph_vector_int_list_destroy(&maps);"),
]
for f in src.glob("*_infinitensymetries.cpp"):
    t = f.read_text()
    for a, b in subs_ig:
        t = t.replace(a, b)
    t = re.sub(r"\n\s*igraph_vector_destroy\(v\);\s*\n\s*free\(v\);", "", t)
    t = re.sub(r"\n\s*igraph_vector_destroy\(\s*\(igraph_vector_t \*\)igraph_vector_ptr_e\(&maps, 0\)\);[^\n]*"
               r"\n\s*free\(\(igraph_vector_t \*\)igraph_vector_ptr_e\(&maps, 0\)\);[^\n]*", "", t)
    assert "igraph_vector_ptr" not in t, f
    f.write_text(t)
for f in list(src.glob("quadraticinteger*.h")) + list(src.glob("quadraticinteger*.cpp")):
    t = f.read_text()
    t2 = re.sub(r"(?<![:\w])array<long int, 2>", "std::array<long int, 2>", t)
    if t2 != t:
        f.write_text(t2)
for f in src.glob("*_alvin.cpp"):
    t = f.read_text()
    t2 = re.sub(r"vector<unsigned int> pow2\(\{1\}\);(\s*)for \(unsigned int i\(1\); i < (\w+); i\+\+\)",
                r"vector<unsigned int> pow2(\2 + 1, 1);\1for (unsigned int i(1); i < \2; i++)", t)
    if t2 != t:
        f.write_text(t2)
    assert "pow2({1})" not in t2, f
cm = src / "CMakeLists.txt"
t = cm.read_text().replace('add_definitions("-std=c++11")', 'add_definitions("-std=c++17")')
t = t.replace('add_definitions("-msse3")', '#add_definitions("-msse3")')
cm.write_text(t)
print("patched", src)
