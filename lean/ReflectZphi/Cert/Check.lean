import ReflectZphi.Cert.Cells

/-!
# B9: one Boolean checker for a reflectivity certificate

Every hypothesis of `hone_of_cells` and `reflective_of_cert` other than Vinberg's
imported theorem (`VinbergChamber`) and the ring facts is decided by a kernel-computable
Boolean function:

* `polyCheck`: the `PolyCert` fields (orthogonal basis, roots with Bezout coefficients
  for primitivity, incidences, signs at `ι₁`);
* `admCheck`: `Admissible` (symmetry, `det < 0` at `ι₁`, positive definite at `ι₂` via
  the orthogonal basis);
* `winCheck`: the window data of B7 (unit with explicit inverse, `ρ < p/q`, the box);
* `chainCheck`: the chain, its vertex positions and the cosh bounds of each segment;
* `cellCheck`: one cell (centre signs, `K` bound, enumeration certificate).

`reflective_of_check` combines them.
-/

namespace ReflectZphi.Check

open Matrix QuadraticAlgebra ReflectZphi.Lattice ReflectZphi.Bridge ReflectZphi.RootNorms
  ReflectZphi.Crossing ReflectZphi.Enum ReflectZphi.QuadSolve ReflectZphi.PolyEnum
  ReflectZphi.Cells

local notation "Nm" => QuadraticAlgebra.norm

variable {a b : ℤ}

/-! ### Sign deciders -/

/-- `ι₁ z < 0`. -/
def neg1 (z : O a b) : Bool := pos1 (-z)

/-- `0 ≤ ι₁ z`. -/
def nonneg1 (z : O a b) : Bool := !pos1 (-z)

/-- `0 < ι₂ z`. -/
def pos2 (z : O a b) : Bool := pos1 (star z)

section signs

variable (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a)
include hd0

lemma neg1_iff (z : O a b) : neg1 z = true ↔ ι₁ hd0.le z < 0 := by
  rw [neg1, pos1_iff hd0, map_neg, neg_pos]

lemma nonneg1_iff (z : O a b) : nonneg1 z = true ↔ 0 ≤ ι₁ hd0.le z := by
  rw [nonneg1, Bool.not_eq_true', ← Bool.not_eq_true, pos1_iff hd0, map_neg, neg_pos, not_lt]

lemma pos2_iff (z : O a b) : pos2 z = true ↔ 0 < ι₂ hd0.le z := by
  rw [pos2, pos1_iff hd0, ← ι₂_eq_ι₁_star]

end signs

/-! ### Determinant, divisibility, roots -/

/-- `det G`, written out. -/
def detE (G : Matrix (Fin 3) (Fin 3) (O a b)) : O a b :=
  G 0 0 * (G 1 1 * G 2 2 - G 1 2 * G 2 1) - G 0 1 * (G 1 0 * G 2 2 - G 1 2 * G 2 0) +
    G 0 2 * (G 1 0 * G 2 1 - G 1 1 * G 2 0)

lemma detE_eq (G : Matrix (Fin 3) (Fin 3) (O a b)) : detE G = G.det := by
  rw [Matrix.det_fin_three, detE]; ring

lemma intCast_ne_zero_O {N : ℤ} (hN : N ≠ 0) : (N : O a b) ≠ 0 := by
  intro h
  have := congrArg QuadraticAlgebra.re h
  simp at this
  exact hN this

lemma dvd_of_dvdCode [IsDomain (O a b)] {m z : O a b} (h : dvdCode m z = true) : m ∣ z := by
  simp only [dvdCode, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
  obtain ⟨⟨hN, h1⟩, h2⟩ := h
  set N := Nm m
  set w := z * star m
  set c : O a b := ⟨w.re / N, w.im / N⟩
  have hw : w = (N : O a b) * c := by
    ext
    · simp [c, Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h1)]
    · simp [c, Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero h2)]
  have hmm : (N : O a b) = m * star m := by
    have := algebraMap_norm_eq_mul_star m
    rw [← this]; rfl
  refine ⟨c, ?_⟩
  have : (N : O a b) * z = (N : O a b) * (m * c) := by
    calc (N : O a b) * z = z * (m * star m) := by rw [hmm]; ring
      _ = m * w := by simp only [w]; ring
      _ = (N : O a b) * (m * c) := by rw [hw]; ring
  exact mul_left_cancel₀ (intCast_ne_zero_O hN) this

lemma bil_eq_gcol (G : Matrix (Fin 3) (Fin 3) (O a b)) (r x : Fin 3 → O a b) :
    bil G r x = gcol G r 0 * x 0 + gcol G r 1 * x 1 + gcol G r 2 * x 2 := by
  simp only [bil, gcol, dotProduct, mulVec, Fin.sum_univ_three]; ring

/-- `r` is a root, with Bezout coefficients `c` (`∑ cᵢ rᵢ = 1`) for primitivity. -/
def rootCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (r c : Fin 3 → O a b) : Bool :=
  decide (c 0 * r 0 + c 1 * r 1 + c 2 * r 2 = 1) && pos1 (bilE G r r) && pos2 (bilE G r r) &&
    (List.finRange 3).all fun k => dvdCode (bilE G r r) (2 * gcol G r k)

lemma rootCheck_sound [IsDomain (O a b)] (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a)
    {G : Matrix (Fin 3) (Fin 3) (O a b)} {r c : Fin 3 → O a b} (h : rootCheck G r c = true) :
    IsRoot hd0.le G r := by
  simp only [rootCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨hc, h1⟩, h2⟩, h3⟩ := h
  rw [bilE_eq] at h1 h2 h3
  refine ⟨?_, ⟨(pos1_iff hd0 _).mp h1, (pos2_iff hd0 _).mp h2⟩, ?_⟩
  · intro d hd
    apply isUnit_of_dvd_one
    rw [← hc]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_right (hd 0) _) (dvd_mul_of_dvd_right (hd 1) _))
      (dvd_mul_of_dvd_right (hd 2) _)
  · intro x
    have e := dvd_of_dvdCode (h3 0)
    have e1 := dvd_of_dvdCode (h3 1)
    have e2 := dvd_of_dvdCode (h3 2)
    rw [bil_eq_gcol G r x]
    have : 2 * (gcol G r 0 * x 0 + gcol G r 1 * x 1 + gcol G r 2 * x 2) =
        2 * gcol G r 0 * x 0 + 2 * gcol G r 1 * x 1 + 2 * gcol G r 2 * x 2 := by ring
    rw [this]
    exact dvd_add (dvd_add (dvd_mul_of_dvd_left e _) (dvd_mul_of_dvd_left e1 _))
      (dvd_mul_of_dvd_left e2 _)

/-! ### The polygon certificate -/

/-- Vectors equal, coordinatewise. -/
def vecEq (x y : Fin 3 → O a b) : Bool := (List.finRange 3).all fun k => decide (x k = y k)

lemma vecEq_iff {x y : Fin 3 → O a b} : vecEq x y = true ↔ x = y := by
  simp only [vecEq, List.all_eq_true, List.mem_finRange, decide_eq_true_eq, true_implies]
  exact ⟨fun h => funext h, fun h k => h ▸ rfl⟩

/-- The orthogonal basis `f`. -/
def basisCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (f : Fin 3 → Fin 3 → O a b) : Bool :=
  ((List.finRange 3).all fun i => (List.finRange 3).all fun j =>
    decide (i = j) || decide (bilE G (f i) (f j) = 0)) &&
  pos1 (bilE G (f 0) (f 0)) && pos1 (bilE G (f 1) (f 1)) && neg1 (bilE G (f 2) (f 2)) &&
  decide (Nm (det3O (f 0) (f 1) (f 2)) ≠ 0)

/-- The `PolyCert` conditions on the polygon. -/
def polyCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ) (f : Fin 3 → Fin 3 → O a b)
    (rs Ps : ℕ → Fin 3 → O a b) (Xs : Fin 3 → O a b) (cf : ℕ → Fin 3 → O a b) : Bool :=
  basisCheck G f && decide (3 ≤ n) &&
  ((List.range n).all fun i => rootCheck G (rs i) (cf i)) &&
  ((List.range n).all fun i => decide (n ≤ i + 1) ||
    (decide (bilE G (rs i) (Ps i) = 0) && decide (bilE G (rs (i + 1)) (Ps i) = 0))) &&
  decide (bilE G (rs (n - 1)) (Ps (n - 1)) = 0) && decide (bilE G (rs 0) (Ps (n - 1)) = 0) &&
  neg1 (bilE G (rs 1) (Ps 2)) && neg1 (bilE G (rs 0) (Ps (n - 2))) &&
  ((List.range n).all fun j => decide (j < 2) || neg1 (bilE G (rs j) (Ps 0))) &&
  ((List.range n).all fun i => decide (i < 1) || decide (n < i + 2) ||
    pos1 (det3O (f 0) (f 1) (f 2) * det3O (Ps 0) (Ps i) (Ps (i + 1)))) &&
  ((List.range n).all fun i => neg1 (bilE G (Ps i) (Ps i)) && neg1 (bilE G (Ps i) (f 2))) &&
  neg1 (bilE G Xs Xs) && neg1 (bilE G Xs (f 2)) &&
  ((List.range n).all fun i => neg1 (bilE G (rs i) Xs))

lemma ne_zero_of_norm {z : O a b} (h : Nm z ≠ 0) (ι : O a b →+* ℝ) (hι : ∀ w, ((Nm w : ℤ) : ℝ) = ι w * ι (star w)) :
    ι z ≠ 0 := by
  intro h0; apply h
  have : ((Nm z : ℤ) : ℝ) = 0 := by rw [hι, h0, zero_mul]
  exact_mod_cast this

lemma basisCheck_sound (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)}
    {f : Fin 3 → Fin 3 → O a b} (h : basisCheck G f = true) :
    (∀ i j, i ≠ j → bil G (f i) (f j) = 0) ∧ 0 < ι₁ hd0.le (bil G (f 0) (f 0)) ∧
      0 < ι₁ hd0.le (bil G (f 1) (f 1)) ∧ ι₁ hd0.le (bil G (f 2) (f 2)) < 0 ∧
      Nm (det3O (f 0) (f 1) (f 2)) ≠ 0 := by
  simp only [basisCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, decide_eq_true_eq, ne_eq] at h
  obtain ⟨⟨⟨⟨ho, h0⟩, h1⟩, h2⟩, hdet⟩ := h
  refine ⟨fun i j hij => ?_, ?_, ?_, ?_, hdet⟩
  · rcases ho i j with h | h
    · exact absurd h hij
    · rwa [bilE_eq] at h
  · rwa [pos1_iff hd0, bilE_eq] at h0
  · rwa [pos1_iff hd0, bilE_eq] at h1
  · rwa [neg1_iff hd0, bilE_eq] at h2

lemma polyCheck_sound [IsDomain (O a b)] (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a)
    {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ} {f : Fin 3 → Fin 3 → O a b}
    {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b} {cf : ℕ → Fin 3 → O a b}
    (h : polyCheck G n f rs Ps Xs cf = true) : PolyCert hd0.le G n f rs Ps Xs := by
  simp only [polyCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb, h3⟩, hroot⟩, hinc⟩, hll⟩, hlr⟩, he1⟩, he0⟩, hej⟩, hfan⟩, hP⟩,
    hXn⟩, hXs⟩, hXi⟩ := h
  obtain ⟨ho, h0, h1, h2, hdet⟩ := basisCheck_sound hd0 hb
  have hN1 : ∀ w : O a b, ((Nm w : ℤ) : ℝ) = ι₁ hd0.le w * ι₁ hd0.le (star w) := fun w => by
    rw [norm_eq_mul, ι₂_eq_ι₁_star]
  simp only [neg1_iff hd0, pos1_iff hd0, bilE_eq] at he1 he0 hej hfan hP hXn hXs hXi
  exact {
    orth := ho
    f0 := h0
    f1 := h1
    f2 := h2
    detF := ne_zero_of_norm hdet _ hN1
    three_le := h3
    roots := fun i hi => rootCheck_sound hd0 (hroot i hi)
    on_left := fun i hi => by
      rcases hinc i (by omega) with h | h
      · omega
      · rw [← bilE_eq]; exact h.1
    on_right := fun i hi => by
      rcases hinc i (by omega) with h | h
      · omega
      · rw [← bilE_eq]; exact h.2
    last_left := by rw [← bilE_eq]; exact hll
    last_right := by rw [← bilE_eq]; exact hlr
    e1_p2 := he1
    e0_pn2 := he0
    ej_p0 := fun j hj hjn => by
      rcases hej j hjn with h | h
      · omega
      · exact h
    fan_pos := fun i hi hin => by
      rcases hfan i (by omega) with (h | h) | h
      · omega
      · omega
      · exact h
    P_neg := fun i hi => (hP i hi).1
    P_side := fun i hi => (hP i hi).2
    X_neg := hXn
    X_side := hXs
    X_int := hXi }

/-! ### Admissibility -/

/-- `G` symmetric, `det G < 0` at `ι₁`, and the basis `f` positive at `ι₂`. -/
def admCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (f : Fin 3 → Fin 3 → O a b) : Bool :=
  ((List.finRange 3).all fun i => (List.finRange 3).all fun j => decide (G i j = G j i)) &&
  neg1 (detE G) && pos2 (bilE G (f 0) (f 0)) && pos2 (bilE G (f 1) (f 1)) &&
  pos2 (bilE G (f 2) (f 2))

/-- Positive definiteness from an orthogonal basis with positive norms. -/
lemma posDef_of_orth (ι : O a b →+* ℝ) {G : Matrix (Fin 3) (Fin 3) (O a b)} (hsym : Gᵀ = G)
    {f : Fin 3 → Fin 3 → O a b} (horth : ∀ i j, i ≠ j → bil G (f i) (f j) = 0)
    (hpos : ∀ j, 0 < ι (bil G (f j) (f j))) (hdet : ι (det3O (f 0) (f 1) (f 2)) ≠ 0) :
    (G.map ι).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map, hsym]
  · intro x hx
    rw [star_trivial]
    set F : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun i j => ι (f j i)
    have hF : F.det = ι (det3O (f 0) (f 1) (f 2)) := by
      simp [F, Matrix.det_fin_three, det3O, map_sub, map_mul, map_add]; ring
    set c := F⁻¹ *ᵥ x
    have hFc : F *ᵥ c = x := by
      simp only [c, mulVec_mulVec]
      rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (by rw [hF]; exact hdet)),
        one_mulVec]
    have hc : c 0 ≠ 0 ∨ c 1 ≠ 0 ∨ c 2 ≠ 0 := by
      by_contra hc'
      push Not at hc'
      apply hx
      rw [← hFc]
      have : c = 0 := by funext k; fin_cases k <;> simp [hc'.1, hc'.2.1, hc'.2.2]
      rw [this, mulVec_zero]
    have hB : ∀ j k : Fin 3, ι (bil G (f j) (f k)) =
        ∑ i : Fin 3, ∑ l : Fin 3, ι (f j i) * ι (G i l) * ι (f k l) := by
      intro j k
      simp only [bil, dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hz : ∀ j k : Fin 3, j ≠ k → ι (bil G (f j) (f k)) = 0 := fun j k h => by
      rw [horth j k h, map_zero]
    have e : x ⬝ᵥ (G.map ι *ᵥ x) =
        c 0 ^ 2 * ι (bil G (f 0) (f 0)) + c 1 ^ 2 * ι (bil G (f 1) (f 1)) +
          c 2 ^ 2 * ι (bil G (f 2) (f 2)) +
        c 0 * c 1 * (ι (bil G (f 0) (f 1)) + ι (bil G (f 1) (f 0))) +
        c 0 * c 2 * (ι (bil G (f 0) (f 2)) + ι (bil G (f 2) (f 0))) +
        c 1 * c 2 * (ι (bil G (f 1) (f 2)) + ι (bil G (f 2) (f 1))) := by
      rw [← hFc]
      simp only [hB, F, dotProduct, mulVec, Fin.sum_univ_three, Matrix.map_apply,
        Matrix.of_apply]
      ring
    rw [e, hz 0 1 (by decide), hz 1 0 (by decide), hz 0 2 (by decide), hz 2 0 (by decide),
      hz 1 2 (by decide), hz 2 1 (by decide)]
    have p0 := hpos 0; have p1 := hpos 1; have p2 := hpos 2
    have s0 := sq_nonneg (c 0); have s1 := sq_nonneg (c 1); have s2 := sq_nonneg (c 2)
    have t0 := mul_nonneg s0 p0.le; have t1 := mul_nonneg s1 p1.le
    have t2 := mul_nonneg s2 p2.le
    rcases hc with h | h | h
    · have := mul_pos (pow_pos_of_ne_zero' h) p0; linarith
    · have := mul_pos (pow_pos_of_ne_zero' h) p1; linarith
    · have := mul_pos (pow_pos_of_ne_zero' h) p2; linarith
  where
    pow_pos_of_ne_zero' {t : ℝ} (h : t ≠ 0) : 0 < t ^ 2 := by positivity

lemma admCheck_sound (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)}
    {f : Fin 3 → Fin 3 → O a b} (hb : basisCheck G f = true) (h : admCheck G f = true) :
    Admissible hd0.le G := by
  obtain ⟨ho, h0, -, -, hdet⟩ := basisCheck_sound hd0 hb
  simp only [admCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hs, hdn⟩, q0⟩, q1⟩, q2⟩ := h
  have hsym : Gᵀ = G := Matrix.ext fun i j => hs j i
  refine ⟨hsym, ?_, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← detE_eq]
    exact (neg1_iff hd0 _).mp hdn
  · exact ⟨fun k => ι₁ hd0.le (f 0 k), by rw [← map_bil]; exact h0⟩
  · refine posDef_of_orth _ hsym ho (fun j => ?_) ?_
    · fin_cases j
      · rw [← bilE_eq]; exact (pos2_iff hd0 _).mp q0
      · rw [← bilE_eq]; exact (pos2_iff hd0 _).mp q1
      · rw [← bilE_eq]; exact (pos2_iff hd0 _).mp q2
    · intro h0'
      apply hdet
      have := norm_eq_mul (hd := hd0.le) (det3O (f 0) (f 1) (f 2))
      rw [h0', mul_zero] at this
      exact_mod_cast this

/-! ### The window (B7) -/

/-- `D2 = 2 det G ≠ 0`, `u · uinv = 1`, `ι₂u² < ι₁u²`, `q ι₁u² ≤ p ι₂u²`, `0 < q`, and
the box bounds `Y`, `S'`. -/
def winCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (D2 u uinv : O a b) (p q : ℤ) (Y S' : ℕ) :
    Bool :=
  decide (2 * detE G = D2) && decide (D2 ≠ 0) && decide (u * uinv = 1) &&
  pos1 (u * u - star u * star u) && nonneg1 ((p : O a b) * (star u * star u) - (q : O a b) * (u * u)) &&
  decide (0 < q) && decide (p * |Nm D2| ≤ q * (b ^ 2 + 4 * a) * (Y : ℤ) ^ 2) &&
  decide (4 * p * |Nm D2| ≤ q * (S' : ℤ) ^ 2)

/-! ### Chain and cells -/

/-- `q (V·P)² ≤ p (V·V)(P·P)` at `ι₁`. -/
def coshCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (c : CellData a b) (P : Fin 3 → O a b) :
    Bool :=
  nonneg1 ((c.pC : O a b) * (bilE G c.V c.V * bilE G P P) -
    (c.qC : O a b) * (bilE G c.V P * bilE G c.V P))

lemma coshCheck_sound (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)}
    {c : CellData a b} {P : Fin 3 → O a b} (h : coshCheck G c P = true) :
    (c.qC : ℝ) * ι₁ hd0.le (bil G c.V P) ^ 2 ≤
      c.pC * (ι₁ hd0.le (bil G c.V c.V) * ι₁ hd0.le (bil G P P)) := by
  rw [coshCheck, nonneg1_iff hd0] at h
  simp only [bilE_eq, map_sub, map_mul, map_intCast] at h
  nlinarith

/-- The chain: vertex positions, future points, and each segment's cell and cosh bounds. -/
def chainCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (f : Fin 3 → Fin 3 → O a b) (n : ℕ)
    (Ps : ℕ → Fin 3 → O a b) (N : ℕ) (Bs : ℕ → Fin 3 → O a b) (idx : ℕ → ℕ) (nc : ℕ)
    (cells : ℕ → CellData a b) (seg : ℕ → ℕ) : Bool :=
  ((List.range n).all fun i => decide (idx i < N) && vecEq (Bs (idx i)) (Ps i)) &&
  ((List.range N).all fun j => neg1 (bilE G (Bs j) (Bs j)) && neg1 (bilE G (Bs j) (f 2))) &&
  ((List.range N).all fun j => decide (N ≤ j + 1) ||
    (decide (seg j < nc) && coshCheck G (cells (seg j)) (Bs j) &&
      coshCheck G (cells (seg j)) (Bs (j + 1))))

/-- One cell: centre future, `0 < qC`, the bound `K`, and the enumeration certificate. -/
def cellCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (f : Fin 3 → Fin 3 → O a b) (n : ℕ)
    (Ps : ℕ → Fin 3 → O a b) (norms : List (O a b)) (c : CellData a b) : Bool :=
  neg1 (bilE G c.V c.V) && neg1 (bilE G c.V (f 2)) && decide (0 < c.qC) &&
  (norms.all fun m => nonneg1 ((c.K : O a b) - bndElt G c.V c.μ c.pC c.qC m)) &&
  ((List.range 6).all fun i => decide (0 ≤ c.w i)) && decide (0 < c.S) &&
  quadCheck c.aL c.w 6 (gramU c.U (traceGram G c.V c.μ c.qC)) c.S &&
  invCheck c.U c.Uinv && colCheck (a := a) (b := b) c.U &&
  enumS c.aL c.w 6 2 (leaf2 G n Ps norms c.U) (c.S * c.K)

/-! ### The theorem -/

/-- **Reflectivity from a checked certificate** (B1–B9), assuming Vinberg's chamber
theorem. Every other hypothesis is a Boolean the kernel evaluates. -/
theorem reflective_of_check (hV : VinbergChamber) [IsDomain (O a b)]
    [IsPrincipalIdealRing (O a b)] (hns : ¬ IsSquare (b ^ 2 + 4 * a))
    (hd0 : 0 < (b : ℝ) ^ 2 + 4 * a) {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ}
    {f : Fin 3 → Fin 3 → O a b} {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b}
    {cf : ℕ → Fin 3 → O a b} (hpoly : polyCheck G n f rs Ps Xs cf = true)
    (hadm : admCheck G f = true)
    {D2 u uinv : O a b} {p q : ℤ} {Y S' : ℕ} (hwin : winCheck G D2 u uinv p q Y S' = true)
    {norms : List (O a b)} (hnorms : windowNorms a b D2 p q Y S' = norms)
    {N : ℕ} {Bs : ℕ → Fin 3 → O a b} {idx : ℕ → ℕ} {nc : ℕ} {cells : ℕ → CellData a b}
    {seg : ℕ → ℕ} (hchain : chainCheck G f n Ps N Bs idx nc cells seg = true)
    (hcells : ∀ k, k < nc → cellCheck G f n Ps norms (cells k) = true) :
    Reflective hd0.le G := by
  have hc := polyCheck_sound hd0 hpoly
  have hb : basisCheck G f = true := by
    cases hbc : basisCheck G f
    · simp [polyCheck, hbc] at hpoly
    · rfl
  have ha := admCheck_sound hd0 hb hadm
  -- the window
  simp only [winCheck, Bool.and_eq_true, decide_eq_true_eq] at hwin
  obtain ⟨⟨⟨⟨⟨⟨⟨hD, hD0⟩, hu⟩, hρ⟩, hpq⟩, hq⟩, hY⟩, hS'⟩ := hwin
  rw [detE_eq] at hD
  subst hD
  have hρ' : ι₂ hd0.le u ^ 2 < ι₁ hd0.le u ^ 2 := by
    rw [pos1_iff hd0] at hρ
    simp only [map_sub, map_mul, ← ι₂_eq_ι₁_star] at hρ
    nlinarith
  have hpq' : (q : ℝ) * ι₁ hd0.le u ^ 2 ≤ p * ι₂ hd0.le u ^ 2 := by
    rw [nonneg1_iff hd0] at hpq
    simp only [map_sub, map_mul, map_intCast, ← ι₂_eq_ι₁_star] at hpq
    nlinarith
  -- the chain
  simp only [chainCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    decide_eq_true_eq, vecEq_iff] at hchain
  obtain ⟨⟨hidx, hB⟩, hsegs⟩ := hchain
  simp only [neg1_iff hd0, bilE_eq] at hB
  have hsg : ∀ j, j + 1 < N → seg j < nc ∧ coshCheck G (cells (seg j)) (Bs j) = true ∧
      coshCheck G (cells (seg j)) (Bs (j + 1)) = true := fun j hj => by
    rcases hsegs j (by omega) with h | h
    · omega
    · exact ⟨h.1.1, h.1.2, h.2⟩
  -- the cells
  have hcl : ∀ k, k < nc → _ := fun k hk => by
    have h := hcells k hk
    simp only [cellCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq] at h
    exact h
  refine reflective_of_cert hV hns ha hc ?_
  refine hone_of_cells hd0 ha hc (by simpa using hD0) (IsUnit.of_mul_eq_one _ hu) hρ' hq
    hpq' hY hS' hnorms (N := N) (Bs := Bs) (idx := idx) hidx (fun j hj => (hB j hj).1)
    (fun j hj => (hB j hj).2) (nc := nc) (cells := cells) (seg := seg)
    (fun j hj => (hsg j hj).1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j hj P hP
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hP
    rcases hP with rfl | rfl
    · exact coshCheck_sound hd0 (hsg j hj).2.1
    · exact coshCheck_sound hd0 (hsg j hj).2.2
  · intro k hk; rw [← bilE_eq]; exact (neg1_iff hd0 _).mp (hcl k hk).1.1.1.1.1.1.1.1.1
  · intro k hk; rw [← bilE_eq]; exact (neg1_iff hd0 _).mp (hcl k hk).1.1.1.1.1.1.1.1.2
  · intro k hk; exact (hcl k hk).1.1.1.1.1.1.1.2
  · intro k hk m hm
    have := (nonneg1_iff hd0 _).mp ((hcl k hk).1.1.1.1.1.1.2 m hm)
    rw [map_sub, map_intCast] at this
    linarith
  · intro k hk; exact (hcl k hk).1.1.1.1.1.2
  · intro k hk; exact (hcl k hk).1.1.1.1.2
  · intro k hk; exact (hcl k hk).1.1.1.2
  · intro k hk; exact (hcl k hk).1.1.2
  · intro k hk; exact (hcl k hk).1.2
  · intro k hk; exact (hcl k hk).2

end ReflectZphi.Check
