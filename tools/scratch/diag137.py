"""Diagnose class 137: at the first cover_sub failure, print per-norm node counts."""
import sys
sys.path.insert(0, ".")
import tools.emit_sub as ES

orig = ES.cover_sub
def cs(R, G, pts, norms, bases, cap, maxcell, depth=0):
    try:
        return orig(R, G, pts, norms, bases, cap, maxcell, depth)
    except RuntimeError:
        if len(pts) == 2 and not getattr(cs, "done", False):
            cs.done = True
            cell = ES.make_cell_sub(R, G, pts, norms, bases, 10 ** 8)
            print("FAIL depth", depth, "pts", [[str(x) for x in p] for p in pts], flush=True)
            print("mu", cell and cell["mu"], "qC", cell and cell["qC"], flush=True)
            for m, d in zip(norms, cell["subs"]):
                print(" norm", m, "nodes", d["nodes"], "K", d.get("K"), flush=True)
        raise
ES.cover_sub = cs
ES.build_sub(5, 137)
