import ReflectZphi.Ring.Euclid
import ReflectZphi.Ring.Embed
import ReflectZphi.Ring.ZPhi
import ReflectZphi.Ring.ZSqrt2
import ReflectZphi.Ring.ZSqrt13
import ReflectZphi.Geometry.Hyperbolic
import ReflectZphi.Lattice.Basic
import ReflectZphi.Imported
import ReflectZphi.Cert.Mat3
import ReflectZphi.Cert.Iso
import ReflectZphi.Geometry.Minkowski
import ReflectZphi.Geometry.Polygon
import ReflectZphi.Geometry.Chamber
import ReflectZphi.Geometry.Transfer
import ReflectZphi.Cert.Bridge
import ReflectZphi.Cert.RootNorms
import ReflectZphi.Cert.Enum
import ReflectZphi.Cert.QuadSolve
import ReflectZphi.Cert.Crossing
import ReflectZphi.Cert.PolyEnum
import ReflectZphi.Cert.Cells
import ReflectZphi.Cert.Check
import ReflectZphi.Cert.Split
import ReflectZphi.Cert.FastLeaf
import ReflectZphi.Cert.Cover
import ReflectZphi.Cert.Sublat
import ReflectZphi.Cert.WinSplit
import ReflectZphi.Audit

/-!
# ReflectZphi

The hand-written part of the Lean development for the paper *Rank 3 reflective hyperbolic
lattices over real quadratic fields*:

* `Ring`: the rings ℤ[φ], ℤ[√2] and ℤ[(1+√13)/2] (`QuadraticAlgebra ℤ a b`), their embeddings
  into ℝ, Euclidean division, units and small primes;
* `Lattice`, `Geometry`: admissible lattices, roots and reflections, the hyperboloid model,
  chambers and Coxeter polygons;
* `Imported`: the results used without proof (Allcock's thin-part theorem, Vinberg's chamber
  theorem), as `Prop`s that theorems take as hypotheses;
* `Cert`: the certificate checkers (`Bool` functions evaluated by the kernel) and their
  soundness theorems;
* `Audit`: the `#audit_axioms` command.

The generated certificates (`ReflectZphi.Data.*`) are not imported here; the entry point for
them is `ReflectZphi.Results`, which states the main theorem.
-/

