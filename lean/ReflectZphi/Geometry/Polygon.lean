import ReflectZphi.Geometry.Minkowski

/-!
# B4: a polygon given by edges and vertices is the cone over its vertices

Normals `e 0, …, e (n-1)` and vertices `p 0, …, p (n-1)`, indexed by `ℕ`. The vertex
`p i` lies on the edges `e i` and `e (i+1)` for `i ≤ n-2`, and `p (n-1)` lies on
`e (n-1)` and `e 0`. If the fan determinants `det(p₀, pᵢ, pᵢ₊₁)` are positive and each
vertex is strictly inside the other half-planes, then every `x` with `e j · x ≤ 0` for
all `j < n` is a nonnegative combination of the vertices (`hull`).

The proof is a fan from `p₀`. Only Cramer's rule (`cramer`, a polynomial identity) and
sign bookkeeping are used.
-/

namespace ReflectZphi.Minkowski

open Finset

/-- The determinant of three vectors of `ℝ³`. -/
def det3 (a b c : Fin 3 → ℝ) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1) - a 1 * (b 0 * c 2 - b 2 * c 0) + a 2 * (b 0 * c 1 - b 1 * c 0)

/-- Cramer's rule, applied to the linear functional `mink h`:
`det(a,b,c) h(x) = det(x,b,c) h(a) + det(a,x,c) h(b) + det(a,b,x) h(c)`. -/
lemma cramer (h a b c x : Fin 3 → ℝ) :
    det3 a b c * mink h x =
      det3 x b c * mink h a + det3 a x c * mink h b + det3 a b x * mink h c := by
  unfold det3 mink; ring

/-- Cramer's rule for vectors: `det(a,b,c) x = det(x,b,c) a + det(a,x,c) b + det(a,b,x) c`. -/
lemma cramer_vec (a b c x : Fin 3 → ℝ) :
    det3 a b c • x = det3 x b c • a + det3 a x c • b + det3 a b x • c := by
  funext k
  fin_cases k <;> simp [det3] <;> ring

/-- Two functionals vanishing on `b, c`: if `h(b) = h(c) = 0`, then
`det(a,b,c) h(x) = det(x,b,c) h(a)`. -/
lemma cramer_two {h a b c : Fin 3 → ℝ} (x : Fin 3 → ℝ) (hb : mink h b = 0)
    (hc : mink h c = 0) : det3 a b c * mink h x = det3 x b c * mink h a := by
  rw [cramer h a b c x, hb, hc]; ring

/-- The hypotheses on a polygon with normals `e` and vertices `p`. -/
structure PolyData (n : ℕ) (e p : ℕ → Fin 3 → ℝ) : Prop where
  three_le : 3 ≤ n
  /-- `p i` is on the edges `e i` and `e (i+1)` (`i ≤ n-2`). -/
  on_left : ∀ i, i + 1 < n → mink (e i) (p i) = 0
  on_right : ∀ i, i + 1 < n → mink (e (i + 1)) (p i) = 0
  /-- `p (n-1)` is on `e (n-1)` and `e 0`. -/
  last_left : mink (e (n - 1)) (p (n - 1)) = 0
  last_right : mink (e 0) (p (n - 1)) = 0
  /-- strictly inside the other half-planes: the instances used in `hull` -/
  e1_p2 : mink (e 1) (p 2) < 0
  e0_pn2 : mink (e 0) (p (n - 2)) < 0
  ej_p0 : ∀ j, 2 ≤ j → j < n → mink (e j) (p 0) < 0
  /-- the fan from `p 0` is positively oriented -/
  fan_pos : ∀ i, 1 ≤ i → i + 2 ≤ n → 0 < det3 (p 0) (p i) (p (i + 1))

lemma PolyData.on_self {n : ℕ} {e p : ℕ → Fin 3 → ℝ} (hP : PolyData n e p) (i : ℕ)
    (hi : i < n) : mink (e i) (p i) = 0 := by
  rcases Nat.lt_or_ge (i + 1) n with h | h
  · exact hP.on_left i h
  · rw [show i = n - 1 by omega]; exact hP.last_left

/-- **B4.** A point in all the half-planes is a nonnegative combination of the vertices. -/
theorem hull {n : ℕ} {e p : ℕ → Fin 3 → ℝ} (hP : PolyData n e p) (x : Fin 3 → ℝ)
    (hx : ∀ j, j < n → mink (e j) x ≤ 0) :
    ∃ k, 1 ≤ k ∧ k + 2 ≤ n ∧ ∃ α β γ : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧
      x = α • p 0 + β • p k + γ • p (k + 1) := by
  have hn := hP.three_le
  set f : ℕ → ℝ := fun i => det3 (p 0) (p i) x with hf
  -- f 1 ≥ 0, from the edge e 1 (through p 0, p 1), tested at p 2
  have hf1 : 0 ≤ f 1 := by
    have hc := cramer_two (a := p 2) (b := p 0) (c := p 1) x
      (by simpa using hP.on_right 0 (by omega)) (hP.on_left 1 (by omega))
    -- det(p2,p0,p1) = det(p0,p1,p2) > 0 and det(x,p0,p1) = f 1
    have hD := hP.fan_pos 1 le_rfl (by omega)
    have e1 : det3 (p 2) (p 0) (p 1) = det3 (p 0) (p 1) (p 2) := by unfold det3; ring
    have e2 : det3 x (p 0) (p 1) = f 1 := by simp only [hf]; unfold det3; ring
    rw [e1, e2] at hc
    have h1 := hx 1 (by omega)
    have h2 := hP.e1_p2
    by_contra hneg; push Not at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hD.le h1, mul_pos_of_neg_of_neg hneg h2]
  -- f (n-1) ≤ 0, from the edge e 0 (through p (n-1), p 0), tested at p (n-2)
  have hfn : f (n - 1) ≤ 0 := by
    have hc := cramer_two (a := p (n - 2)) (b := p 0) (c := p (n - 1)) x
      (by simpa using hP.on_left 0 (by omega)) hP.last_right
    have hD := hP.fan_pos (n - 2) (by omega) (by omega)
    have hidx : n - 2 + 1 = n - 1 := by omega
    rw [hidx] at hD
    have e1 : det3 (p (n - 2)) (p 0) (p (n - 1)) = -det3 (p 0) (p (n - 2)) (p (n - 1)) := by
      unfold det3; ring
    have e2 : det3 x (p 0) (p (n - 1)) = f (n - 1) := by simp only [hf]; unfold det3; ring
    rw [e1, e2] at hc
    have h1 := hx 0 (by omega)
    have h2 := hP.e0_pn2
    by_contra hpos; push Not at hpos
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hD.le h1, mul_neg_of_pos_of_neg hpos h2]
  -- discrete intermediate value: the least k ≥ 1 with f (k+1) ≤ 0
  have hex : ∃ k, 1 ≤ k ∧ k + 2 ≤ n ∧ f (k + 1) ≤ 0 :=
    ⟨n - 2, by omega, by omega, by rw [show n - 2 + 1 = n - 1 by omega]; exact hfn⟩
  classical
  have hmin : ∀ m, m < Nat.find hex → ¬ (1 ≤ m ∧ m + 2 ≤ n ∧ f (m + 1) ≤ 0) :=
    fun m hm => Nat.find_min hex hm
  obtain ⟨hk1, hk2, hkf⟩ := Nat.find_spec hex
  set k := Nat.find hex with hk
  have hfk : 0 ≤ f k := by
    rcases Nat.lt_or_ge 1 k with hlt | hle
    · have := hmin (k - 1) (by omega)
      push Not at this
      have h := this (by omega) (by omega)
      rw [show k - 1 + 1 = k by omega] at h
      exact h.le
    · rw [show k = 1 by omega]; exact hf1
  -- x lies in the cone over p 0, p k, p (k+1)
  have hD := hP.fan_pos k hk1 hk2
  have hcv := cramer_vec (p 0) (p k) (p (k + 1)) x
  -- coefficient of p 0: from the edge e (k+1) through p k, p (k+1)
  have hc0 : 0 ≤ det3 x (p k) (p (k + 1)) := by
    have hc := cramer_two (a := p 0) (b := p k) (c := p (k + 1)) x
      (hP.on_right k (by omega)) (hP.on_self (k + 1) (by omega))
    have h1 := hx (k + 1) (by omega)
    have h2 := hP.ej_p0 (k + 1) (by omega) (by omega)
    by_contra hneg; push Not at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hD.le h1, mul_pos_of_neg_of_neg hneg h2]
  have hck : 0 ≤ det3 (p 0) x (p (k + 1)) := by
    have : det3 (p 0) x (p (k + 1)) = -f (k + 1) := by simp only [hf]; unfold det3; ring
    linarith
  set D := det3 (p 0) (p k) (p (k + 1))
  have hD0 : D ≠ 0 := hD.ne'
  refine ⟨k, hk1, hk2, det3 x (p k) (p (k + 1)) / D, det3 (p 0) x (p (k + 1)) / D, f k / D,
    div_nonneg hc0 hD.le, div_nonneg hck hD.le, div_nonneg hfk hD.le, ?_⟩
  calc x = (1 / D) • (D • x) := by rw [smul_smul, one_div, inv_mul_cancel₀ hD0, one_smul]
    _ = (1 / D) • (det3 x (p k) (p (k + 1)) • p 0 + det3 (p 0) x (p (k + 1)) • p k +
          det3 (p 0) (p k) x • p (k + 1)) := by rw [hcv]
    _ = _ := by simp only [hf, smul_add, smul_smul, one_div, inv_mul_eq_div]

end ReflectZphi.Minkowski

namespace ReflectZphi.Minkowski

/-- The polygon on the upper sheet of the hyperboloid `x·x = -1`. -/
def polySet (n : ℕ) (e : ℕ → Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {x | mink x x = -1 ∧ 0 ≤ x 2 ∧ ∀ j, j < n → mink (e j) x ≤ 0}

lemma isClosed_polySet (n : ℕ) (e : ℕ → Fin 3 → ℝ) : IsClosed (polySet n e) := by
  have hm : ∀ y : Fin 3 → ℝ, Continuous fun x : Fin 3 → ℝ => mink y x := by
    intro y; unfold mink; fun_prop
  have hq : Continuous fun x : Fin 3 → ℝ => mink x x := by unfold mink; fun_prop
  have : polySet n e = {x | mink x x = -1} ∩ ({x | 0 ≤ x 2} ∩
      ⋂ j ∈ Finset.range n, {x | mink (e j) x ≤ 0}) := by
    ext x; simp [polySet]
  rw [this]
  exact (isClosed_eq hq continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 2)).inter
      (isClosed_biInter fun j _ => isClosed_le (hm (e j)) continuous_const))

lemma tau_pos_of_future {x : Fin 3 → ℝ} (hx : Future x) : 0 < tau x := by
  unfold tau; exact Real.sqrt_pos.mpr (by linarith [hx.2])

/-- **B4, compactness.** If the vertices are future timelike, the polygon is compact. -/
theorem isCompact_polySet {n : ℕ} {e p : ℕ → Fin 3 → ℝ} (hP : PolyData n e p)
    (hfut : ∀ i, i < n → Future (p i)) : IsCompact (polySet n e) := by
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_polySet n e) ?_
  set M : ℝ := ∑ i ∈ Finset.range n, ‖p i‖ / tau (p i)
  have hM : ∀ i, i < n → ‖p i‖ / tau (p i) ≤ M := fun i hi =>
    Finset.single_le_sum (f := fun i => ‖p i‖ / tau (p i))
      (fun j _ => div_nonneg (norm_nonneg _) (tau_nonneg _)) (Finset.mem_range.mpr hi)
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨3 * M, fun x hx => ?_⟩
  obtain ⟨hq, -, hle⟩ := hx
  obtain ⟨k, hk1, hk2, α, β, γ, hα, hβ, hγ, rfl⟩ := hull hP _ hle
  -- τ(x) = 1 ≥ α τ(p 0) + β τ(p k) + γ τ(p (k+1))
  have h0 := hfut 0 (by omega)
  have hk := hfut k (by omega)
  have hk' := hfut (k + 1) (by omega)
  have hA := futureOrZero_smul hα (Or.inr h0)
  have hB := futureOrZero_smul hβ (Or.inr hk)
  have hC := futureOrZero_smul hγ (Or.inr hk')
  have s1 := tau_add hA hB
  have s2 := tau_add (futureOrZero_add hA hB) hC
  have htau1 : tau (α • p 0 + β • p k + γ • p (k + 1)) = 1 := by
    unfold tau; rw [hq]; simp
  rw [htau1] at s2
  rw [tau_smul hα, tau_smul hβ] at s1
  rw [tau_smul hγ] at s2
  have hT' : α * tau (p 0) + β * tau (p k) + γ * tau (p (k + 1)) ≤ 1 := by linarith
  have t0 := tau_pos_of_future h0
  have tk := tau_pos_of_future hk
  have tk' := tau_pos_of_future hk'
  have bα : α * ‖p 0‖ ≤ M := by
    have : α ≤ 1 / tau (p 0) := by
      rw [le_div_iff₀ t0]; nlinarith [mul_nonneg hβ tk.le, mul_nonneg hγ tk'.le]
    calc α * ‖p 0‖ ≤ 1 / tau (p 0) * ‖p 0‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖p 0‖ / tau (p 0) := by ring
      _ ≤ M := hM 0 (by omega)
  have bβ : β * ‖p k‖ ≤ M := by
    have : β ≤ 1 / tau (p k) := by
      rw [le_div_iff₀ tk]; nlinarith [mul_nonneg hα t0.le, mul_nonneg hγ tk'.le]
    calc β * ‖p k‖ ≤ 1 / tau (p k) * ‖p k‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖p k‖ / tau (p k) := by ring
      _ ≤ M := hM k (by omega)
  have bγ : γ * ‖p (k + 1)‖ ≤ M := by
    have : γ ≤ 1 / tau (p (k + 1)) := by
      rw [le_div_iff₀ tk']; nlinarith [mul_nonneg hα t0.le, mul_nonneg hβ tk.le]
    calc γ * ‖p (k + 1)‖ ≤ 1 / tau (p (k + 1)) * ‖p (k + 1)‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖p (k + 1)‖ / tau (p (k + 1)) := by ring
      _ ≤ M := hM (k + 1) (by omega)
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖α • p 0 + β • p k + γ • p (k + 1)‖
      ≤ ‖α • p 0‖ + ‖β • p k‖ + ‖γ • p (k + 1)‖ := norm_add₃_le
    _ = α * ‖p 0‖ + β * ‖p k‖ + γ * ‖p (k + 1)‖ := by
        rw [norm_smul, norm_smul, norm_smul, Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ,
          Real.norm_of_nonneg hγ]
    _ ≤ 3 * M := by linarith

end ReflectZphi.Minkowski

namespace ReflectZphi.Minkowski

lemma mink_add_left (a b x : Fin 3 → ℝ) : mink x (a + b) = mink x a + mink x b := by
  unfold mink; simp only [Pi.add_apply]; ring

lemma mink_smul_left (c : ℝ) (a x : Fin 3 → ℝ) : mink x (c • a) = c * mink x a := by
  unfold mink; simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- **B5 (one sign).** If `r·pᵢ ≤ 0` at every vertex, then `r·x ≤ 0` on the polygon. -/
theorem nonpos_on_polySet {n : ℕ} {e p : ℕ → Fin 3 → ℝ} (hP : PolyData n e p)
    (r : Fin 3 → ℝ) (hr : ∀ i, i < n → mink r (p i) ≤ 0) :
    ∀ x ∈ polySet n e, mink r x ≤ 0 := by
  intro x hx
  obtain ⟨k, hk1, hk2, α, β, γ, hα, hβ, hγ, rfl⟩ := hull hP x hx.2.2
  rw [mink_add_left, mink_add_left, mink_smul_left, mink_smul_left, mink_smul_left]
  have := hr 0 (by omega); have := hr k (by omega); have := hr (k + 1) (by omega)
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hα (hr 0 (by omega)),
    mul_nonpos_of_nonneg_of_nonpos hβ (hr k (by omega)),
    mul_nonpos_of_nonneg_of_nonpos hγ (hr (k + 1) (by omega))]

/-- **Crossing bound (B2 + B3 + B4).** Let the vertices be future timelike, `v` future
timelike, and `−(v·pᵢ) ≤ C τ(v) τ(pᵢ)` at every vertex. If the line `r^⊥` meets the
polygon, then `(r·v)² ≤ (r·r)·(−v·v)·(C² − 1)`. -/
theorem crossing_bound {n : ℕ} {e p : ℕ → Fin 3 → ℝ} (hP : PolyData n e p)
    (hfut : ∀ i, i < n → Future (p i)) {v : Fin 3 → ℝ} (hv : Future v) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ i, i < n → -mink v (p i) ≤ C * tau v * tau (p i))
    (r x : Fin 3 → ℝ) (hx : x ∈ polySet n e) (hrx : mink x r = 0) :
    mink r v ^ 2 ≤ mink r r * (-mink v v) * (C ^ 2 - 1) := by
  obtain ⟨hq, h2, hle⟩ := hx
  have hxx : mink x x < 0 := by rw [hq]; norm_num
  have hmaj := majorant_bound v hxx hrx
  rw [hq] at hmaj
  -- the ball bound at x
  obtain ⟨k, hk1, hk2, α, β, γ, hα, hβ, hγ, hxeq⟩ := hull hP x hle
  have hball := ball_convex (Finset.univ : Finset (Fin 3)) ![α, β, γ] ![p 0, p k, p (k + 1)]
    v C hC
    (by intro i _; fin_cases i <;> simp [hα, hβ, hγ])
    (by intro i _; fin_cases i <;> simp <;> exact Or.inr (hfut _ (by omega)))
    (by intro i _; fin_cases i <;> simp <;> exact hb _ (by omega))
  have hsum : ∑ i : Fin 3, (![α, β, γ] : Fin 3 → ℝ) i • (![p 0, p k, p (k + 1)] :
      Fin 3 → Fin 3 → ℝ) i = x := by
    simp [Fin.sum_univ_three, hxeq]
  rw [hsum] at hball
  have htau : tau x = 1 := by unfold tau; rw [hq]; simp
  rw [htau, mul_one] at hball
  -- x is future: it has x·x = -1 and x₂ ≥ 0
  have hxf : Future x := by
    refine ⟨?_, hxx⟩
    rcases eq_or_lt_of_le h2 with h | h
    · exfalso; unfold mink at hq; rw [← h] at hq; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    · exact h
  have hvx : 0 < -mink v x := by linarith [mink_neg_of_future hv hxf]
  have htv : tau v ^ 2 = -mink v v := by
    unfold tau; rw [Real.sq_sqrt (by linarith [hv.2])]
  have hsq : mink v x ^ 2 ≤ C ^ 2 * (-mink v v) := by
    have h := pow_le_pow_left₀ hvx.le hball 2
    rw [neg_sq, mul_pow, htv] at h
    linarith
  have hrr : 0 ≤ mink r r := perp_nonneg hxx hrx
  -- (r·v)² ≤ (r·r)((v·x)² + v·v) ≤ (r·r)(C² − 1)(−v·v)
  have : mink r v ^ 2 ≤ mink r r * (mink v x ^ 2 + mink v v) := by linarith
  calc mink r v ^ 2 ≤ mink r r * (mink v x ^ 2 + mink v v) := this
    _ ≤ mink r r * (C ^ 2 * (-mink v v) + mink v v) :=
        mul_le_mul_of_nonneg_left (by linarith) hrr
    _ = mink r r * (-mink v v) * (C ^ 2 - 1) := by ring

end ReflectZphi.Minkowski
