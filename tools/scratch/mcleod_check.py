import sys, time
sys.path.insert(0, ".")
from zphi.ring import get_ring
from zphi.linalg import bil
import zphi.vinbergn as VN
R = get_ring(5)
d = R(1, 4)
n = 4
G = [[(-d if i == j == 0 else (R.one if i == j else R.zero)) for j in range(n)] for i in range(n)]
E = [[R.one if i == j else R.zero for i in range(n)] for j in range(n)]
# 1. the norm-(3+phi) walls: reflection maps every basis vector into O^4
for r in ([R(1,1), R.zero, R.zero, R(1,4)], [R(3,4), R(-4,-5), R(-4,-5), R(5,9)]):
    m = bil(G, r, r)
    imgs = [[e[i] - 2 * bil(G, e, r) / m * r[i] for i in range(n)] for e in E]
    print("norm", m, "N(norm)", m.norm_num() if hasattr(m,'norm_num') else '', "s_r(O^4) in O^4:",
          all(x.is_integral() for v in imgs for x in v))
# 2. Vinberg restricted to norms 1 and 2 (McLeod's tables)
orig = VN.LatticeN.__init__
def init(self, G, v0):
    orig(self, G, v0)
    print("all norms:", [str(x) for x in self.norms])
    self.norms = [x for x in self.norms if x in (R.one, R(2, 0))]
    print("restricted:", [str(x) for x in self.norms])
VN.LatticeN.__init__ = init
v0 = [R.one] + [R.zero] * (n - 1)
res = VN.vinberg_n(G, v0, max_roots=40, time_limit=900)
print(res["status"], res.get("reason"), len(res["roots"]))
for r in res["roots"][:12]:
    print("   ", [str(x) for x in r], bil(G, r, r))
