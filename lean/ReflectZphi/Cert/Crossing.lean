import ReflectZphi.Cert.Bridge
import ReflectZphi.Cert.RootNorms

/-!
# B8 (part 2): the crossing bound at the lattice level

* `crossing_lat`: if a vector `r` takes both strict signs on the vertices of a certified
  polygon, then `q (r·V)² ≤ (p − q) (r·r) (−V·V)` at `ι₁`, where `V` is a future timelike
  centre with `q (V·Pᵢ)² ≤ p (V·V)(Pᵢ·Pᵢ)` at every vertex (so `p/q ≥ cosh² d(V, Pᵢ)`).
  This is `crossing_bound` (B2–B5) transported by the coordinates of the bridge.
* `cs_ι₂`: Cauchy–Schwarz at `ι₂`, where `G` is positive definite.
-/

namespace ReflectZphi.Crossing

open Matrix Set ReflectZphi.Minkowski ReflectZphi.Geometry ReflectZphi.Lattice
  ReflectZphi.Transfer ReflectZphi.Bridge

variable {a b : ℤ} {hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a} {G : Matrix (Fin 3) (Fin 3) (O a b)}
  {n : ℕ} {f : Fin 3 → Fin 3 → O a b} {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b}

/-- **Crossing bound** for a certified polygon, at `ι₁`. -/
theorem crossing_lat (hc : PolyCert hd G n f rs Ps Xs)
    (hvert : ∀ k i, k < n → i < n → ι₁ hd (bil G (rs k) (Ps i)) ≤ 0)
    {V : Fin 3 → O a b} (hVV : ι₁ hd (bil G V V) < 0) (hVs : ι₁ hd (bil G V (f 2)) < 0)
    {pC qC : ℝ} (hq : 0 < qC)
    (hC : ∀ i, i < n → qC * ι₁ hd (bil G V (Ps i)) ^ 2 ≤
      pC * (ι₁ hd (bil G V V) * ι₁ hd (bil G (Ps i) (Ps i))))
    {r : Fin 3 → O a b} {i j : ℕ} (hi : i < n) (hj : j < n)
    (hpos : 0 < ι₁ hd (bil G r (Ps i))) (hneg : ι₁ hd (bil G r (Ps j)) < 0) :
    qC * ι₁ hd (bil G r V) ^ 2 ≤ (pC - qC) * ι₁ hd (bil G r r) * (-ι₁ hd (bil G V V)) := by
  set T := Tm (hd := hd) (G := G) f
  have hT : ∀ u w, mink (T *ᵥ realVec hd u) (T *ᵥ realVec hd w) = ι₁ hd (bil G u w) :=
    mink_T hc
  have hP := polyData_of_cert hc
  have hfut : ∀ k, k < n → Future (T *ᵥ realVec hd (Ps k)) :=
    fun k hk => future_T hc (hc.P_neg k hk) (hc.P_side k hk)
  have hv : Future (T *ᵥ realVec hd V) := future_T hc hVV hVs
  set ρ := T *ᵥ realVec hd r
  set v := T *ᵥ realVec hd V
  set pv : ℕ → Fin 3 → ℝ := fun k => T *ᵥ realVec hd (Ps k)
  set ev : ℕ → Fin 3 → ℝ := fun k => T *ᵥ realVec hd (rs k)
  set α := ι₁ hd (bil G r (Ps i))
  set β := -ι₁ hd (bil G r (Ps j))
  have hβ : 0 < β := by simp only [β]; linarith
  set y := β • pv i + α • pv j
  have hy : Future y := future_add (future_smul hβ (hfut i hi)) (future_smul hpos (hfut j hj))
  have hρy : mink ρ y = 0 := by
    simp only [y, mink_add_left, mink_smul_left, pv, ρ, hT, α, β]; ring
  set x := nrm y
  have hx : x ∈ polySet n ev := by
    have hxs := nrm_mem hy
    refine ⟨hxs.1, hxs.2.le, fun k hk => ?_⟩
    rw [mink_nrm]
    have ht := tau_pos_of_future hy
    have h1 : mink (ev k) y ≤ 0 := by
      simp only [y, mink_add_left, mink_smul_left, ev, pv, hT]
      have := hvert k i hk hi; have := hvert k j hk hj
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le) h1
  have hxρ : mink x ρ = 0 := by
    rw [mink_comm, mink_nrm, hρy, mul_zero]
  -- the cosh bound `C = √(p/q)`
  have hPP := hc.P_neg
  have hpq : 0 ≤ pC / qC := by
    have h := hC i hi
    have hprod : 0 < ι₁ hd (bil G V V) * ι₁ hd (bil G (Ps i) (Ps i)) :=
      mul_pos_of_neg_of_neg hVV (hPP i hi)
    have : 0 ≤ pC := by
      by_contra hc'; push Not at hc'
      have := mul_neg_of_neg_of_pos hc' hprod
      nlinarith [sq_nonneg (ι₁ hd (bil G V (Ps i)))]
    positivity
  set C := Real.sqrt (pC / qC)
  have hC0 : 0 ≤ C := Real.sqrt_nonneg _
  have hC2 : C ^ 2 = pC / qC := Real.sq_sqrt hpq
  have htv : tau v ^ 2 = -mink v v := by
    unfold tau; rw [Real.sq_sqrt (by linarith [hv.2])]
  have hb : ∀ k, k < n → -mink v (pv k) ≤ C * tau v * tau (pv k) := by
    intro k hk
    have hneg' : 0 < -mink v (pv k) := neg_pos.mpr (mink_neg_of_future hv (hfut k hk))
    have htp : tau (pv k) ^ 2 = -mink (pv k) (pv k) := by
      unfold tau; rw [Real.sq_sqrt (by linarith [(hfut k hk).2])]
    have hrhs : 0 ≤ C * tau v * tau (pv k) := by
      have := tau_nonneg v; have := tau_nonneg (pv k); positivity
    rw [← pow_le_pow_iff_left₀ hneg'.le hrhs (two_ne_zero)]
    rw [mul_pow, mul_pow, hC2, htv, htp, neg_sq]
    simp only [v, pv, hT]
    have h := hC k hk
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hq]
    nlinarith
  have hcross := crossing_bound hP hfut hv hC0 hb ρ x hx hxρ
  simp only [ρ, v, hT, hC2] at hcross
  have : qC * ι₁ hd (bil G r V) ^ 2 ≤
      qC * (ι₁ hd (bil G r r) * -ι₁ hd (bil G V V) * (pC / qC - 1)) :=
    mul_le_mul_of_nonneg_left hcross hq.le
  have e : qC * (ι₁ hd (bil G r r) * -ι₁ hd (bil G V V) * (pC / qC - 1)) =
      (pC - qC) * ι₁ hd (bil G r r) * (-ι₁ hd (bil G V V)) := by
    field_simp
  linarith

/-- A ring hom applied to the bilinear form. -/
lemma map_bil (ι : O a b →+* ℝ) (x y : Fin 3 → O a b) :
    ι (bil G x y) = (fun k => ι (x k)) ⬝ᵥ (G.map ι *ᵥ fun k => ι (y k)) := by
  unfold bil
  rw [RingHom.map_dotProduct]
  congr 1
  funext k
  simp only [Function.comp_apply]
  rw [RingHom.map_mulVec]
  rfl

/-- Cauchy–Schwarz for a real symmetric positive semidefinite matrix. -/
lemma cs_psd {M : Matrix (Fin 3) (Fin 3) ℝ} (hM : M.PosSemidef) (u w : Fin 3 → ℝ) :
    (u ⬝ᵥ (M *ᵥ w)) ^ 2 ≤ (u ⬝ᵥ (M *ᵥ u)) * (w ⬝ᵥ (M *ᵥ w)) := by
  have hQ : ∀ x : Fin 3 → ℝ, 0 ≤ x ⬝ᵥ (M *ᵥ x) := fun x => by
    simpa using hM.dotProduct_mulVec_nonneg x
  have hsym : Mᵀ = M := by
    have h := hM.1
    unfold IsHermitian conjTranspose at h
    ext i j
    have := congrArg (fun N : Matrix (Fin 3) (Fin 3) ℝ => N i j) h
    simpa using this
  have hB : w ⬝ᵥ (M *ᵥ u) = u ⬝ᵥ (M *ᵥ w) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym, dotProduct_comm]
  set A := u ⬝ᵥ (M *ᵥ u)
  set B := u ⬝ᵥ (M *ᵥ w)
  set W := w ⬝ᵥ (M *ᵥ w)
  have hexp : ∀ s t : ℝ, (s • u + t • w) ⬝ᵥ (M *ᵥ (s • u + t • w)) =
      s ^ 2 * A + 2 * s * t * B + t ^ 2 * W := by
    intro s t
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, A, B, W, hB]
    ring
  have h1 := hQ (W • u + (-B) • w)
  rw [hexp] at h1
  have h2 := hQ (A • w + (-B) • u)
  have hexp2 : (A • w + (-B) • u) ⬝ᵥ (M *ᵥ (A • w + (-B) • u)) =
      A ^ 2 * W + 2 * A * (-B) * B + B ^ 2 * A := by
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, A, B, W, hB]
    ring
  rw [hexp2] at h2
  have hA := hQ u
  have hW := hQ w
  rcases eq_or_lt_of_le hW with hW0 | hWp
  · rcases eq_or_lt_of_le hA with hA0 | hAp
    · -- both zero: B = 0
      have h3 := hQ (u + (-B) • w)
      have : (u + (-B) • w) ⬝ᵥ (M *ᵥ (u + (-B) • w)) = A + 2 * (-B) * B + B ^ 2 * W := by
        simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
          dotProduct_smul, smul_eq_mul, A, B, W, hB]
        ring
      rw [this] at h3
      nlinarith [sq_nonneg B]
    · nlinarith
  · nlinarith

/-- **Cauchy–Schwarz at `ι₂`** for an admissible lattice. -/
theorem cs_ι₂ (hadm : Admissible hd G) (x y : Fin 3 → O a b) :
    ι₂ hd (bil G x y) ^ 2 ≤ ι₂ hd (bil G x x) * ι₂ hd (bil G y y) := by
  rw [map_bil, map_bil, map_bil]
  exact cs_psd hadm.posDef₂.posSemidef _ _

end ReflectZphi.Crossing
