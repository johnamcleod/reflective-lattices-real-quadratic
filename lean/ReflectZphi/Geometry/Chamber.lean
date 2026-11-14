import ReflectZphi.Geometry.Polygon

/-!
# B6: a polygon whose interior no mirror crosses is a chamber (Minkowski coordinates)

Setting:
* `S = {x | x·x = -1, x₂ > 0}` is the upper sheet.
* `Rs` is any set of spacelike vectors (the roots), with mirrors `M = {x ∈ S | ∃ r ∈ Rs, r·x = 0}`.

If the edges `e i` of a polygon belong to `Rs`, every `r ∈ Rs` has one sign on the
vertices, and `xs` is an interior point, then
`polySet n e = closure (connectedComponentIn (S \ M) (nrm xs))`.
-/

namespace ReflectZphi.Minkowski

open Topology Filter Set

/-- The upper sheet. -/
def upperSheet : Set (Fin 3 → ℝ) := {x | mink x x = -1 ∧ 0 < x 2}

/-- The mirrors of `Rs` in the upper sheet. -/
def mirrorSet (Rs : Set (Fin 3 → ℝ)) : Set (Fin 3 → ℝ) :=
  {x | x ∈ upperSheet ∧ ∃ r ∈ Rs, mink r x = 0}

/-- Radial projection to the hyperboloid. -/
noncomputable def nrm (y : Fin 3 → ℝ) : Fin 3 → ℝ := (tau y)⁻¹ • y

lemma mink_smul_smul (a b : ℝ) (x y : Fin 3 → ℝ) :
    mink (a • x) (b • y) = a * b * mink x y := by
  unfold mink; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma nrm_mem {y : Fin 3 → ℝ} (hy : Future y) : nrm y ∈ upperSheet := by
  have ht := tau_pos_of_future hy
  have htt : tau y ^ 2 = -mink y y := by unfold tau; rw [Real.sq_sqrt (by linarith [hy.2])]
  refine ⟨?_, ?_⟩
  · unfold nrm; rw [mink_smul_smul]
    field_simp
    nlinarith [htt]
  · unfold nrm; simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_pos (inv_pos.mpr ht) hy.1

lemma mink_nrm (r : Fin 3 → ℝ) {y : Fin 3 → ℝ} : mink r (nrm y) = (tau y)⁻¹ * mink r y := by
  unfold nrm; exact mink_smul_left _ _ _

lemma future_of_upperSheet {x : Fin 3 → ℝ} (hx : x ∈ upperSheet) : Future x :=
  ⟨hx.2, by rw [hx.1]; norm_num⟩

lemma tau_of_upperSheet {x : Fin 3 → ℝ} (hx : x ∈ upperSheet) : tau x = 1 := by
  unfold tau; rw [hx.1]; simp

lemma nrm_of_upperSheet {x : Fin 3 → ℝ} (hx : x ∈ upperSheet) : nrm x = x := by
  unfold nrm; rw [tau_of_upperSheet hx]; simp

lemma continuous_mink (r : Fin 3 → ℝ) : Continuous fun x : Fin 3 → ℝ => mink r x := by
  unfold mink; fun_prop

lemma continuous_mink_self : Continuous fun x : Fin 3 → ℝ => mink x x := by
  unfold mink; fun_prop

lemma continuousOn_nrm : ContinuousOn nrm {y | Future y} := by
  unfold nrm tau
  have h1 : ContinuousOn (fun y : Fin 3 → ℝ => (Real.sqrt (-mink y y))⁻¹) {y | Future y} := by
    apply ContinuousOn.inv₀
    · exact (Real.continuous_sqrt.comp (continuous_mink_self.neg)).continuousOn
    · intro y hy; exact (Real.sqrt_pos.mpr (by linarith [hy.2])).ne'
  exact h1.smul continuousOn_id

lemma future_convex {x y : Fin 3 → ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hx : Future x)
    (hy : Future y) : Future ((1 - t) • x + t • y) := by
  rcases eq_or_lt_of_le ht0 with rfl | ht0
  · simpa using hx
  rcases eq_or_lt_of_le ht1 with rfl | ht1
  · simpa using hy
  exact future_add (future_smul (by linarith) hx) (future_smul ht0 hy)

/-- The open polygon in the sheet. -/
def openPoly (n : ℕ) (e : ℕ → Fin 3 → ℝ) : Set (Fin 3 → ℝ) :=
  {x | x ∈ upperSheet ∧ ∀ j, j < n → mink (e j) x < 0}

/-- The open polygon is connected: it is the radial image of a convex cone. -/
lemma isPreconnected_openPoly (n : ℕ) (e : ℕ → Fin 3 → ℝ) :
    IsPreconnected (openPoly n e) := by
  set K : Set (Fin 3 → ℝ) := {y | Future y ∧ ∀ j, j < n → mink (e j) y < 0}
  have hK : Convex ℝ K := by
    intro x hx y hy a b ha hb hab
    obtain rfl : a = 1 - b := by linarith
    refine ⟨future_convex hb (by linarith) hx.1 hy.1, fun j hj => ?_⟩
    rw [mink_add_left, mink_smul_left, mink_smul_left]
    have h1 := hx.2 j hj; have h2 := hy.2 j hj
    rcases eq_or_lt_of_le hb with rfl | hb'
    · simpa using h1
    · nlinarith
  have himg : nrm '' K = openPoly n e := by
    ext x; constructor
    · rintro ⟨y, ⟨hyf, hye⟩, rfl⟩
      refine ⟨nrm_mem hyf, fun j hj => ?_⟩
      rw [mink_nrm]
      exact mul_neg_of_pos_of_neg (inv_pos.mpr (tau_pos_of_future hyf)) (hye j hj)
    · rintro ⟨hxS, hxe⟩
      exact ⟨x, ⟨future_of_upperSheet hxS, hxe⟩, nrm_of_upperSheet hxS⟩
  rw [← himg]
  exact hK.isPreconnected.image _ (continuousOn_nrm.mono fun y hy => hy.1)

/-- The hypotheses of B6. -/
structure ChamberData (n : ℕ) (e p : ℕ → Fin 3 → ℝ) (Rs : Set (Fin 3 → ℝ))
    (xs : Fin 3 → ℝ) : Prop where
  poly : PolyData n e p
  fut : ∀ i, i < n → Future (p i)
  roots_pos : ∀ r ∈ Rs, 0 < mink r r
  edges : ∀ i, i < n → e i ∈ Rs
  one_sign : ∀ r ∈ Rs, (∀ i, i < n → mink r (p i) ≤ 0) ∨ (∀ i, i < n → 0 ≤ mink r (p i))
  xs_fut : Future xs
  xs_int : ∀ i, i < n → mink (e i) xs < 0

lemma polySet_eq {n : ℕ} {e : ℕ → Fin 3 → ℝ} :
    polySet n e = {x | x ∈ upperSheet ∧ ∀ j, j < n → mink (e j) x ≤ 0} := by
  ext x; constructor
  · rintro ⟨hq, h2, he⟩
    refine ⟨⟨hq, ?_⟩, he⟩
    rcases eq_or_lt_of_le h2 with h | h
    · exfalso; unfold mink at hq; rw [← h] at hq; nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
    · exact h
  · rintro ⟨⟨hq, h2⟩, he⟩; exact ⟨hq, h2.le, he⟩

/-- No mirror meets the open polygon. -/
lemma openPoly_disjoint {n : ℕ} {e p : ℕ → Fin 3 → ℝ} {Rs : Set (Fin 3 → ℝ)}
    {xs : Fin 3 → ℝ} (hC : ChamberData n e p Rs xs) :
    openPoly n e ⊆ upperSheet \ mirrorSet Rs := by
  rintro x ⟨hxS, hxe⟩
  refine ⟨hxS, ?_⟩
  rintro ⟨-, r, hr, hrx⟩
  have hrr := hC.roots_pos r hr
  -- move along ±r: x + t r is in the open cone for small t, and r·(x + t r) = t (r·r)
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), Future (x + t • r) ∧
      ∀ j ∈ Finset.range n, mink (e j) (x + t • r) < 0 := by
    have hc : ∀ (f : ℝ → ℝ), Continuous f → f 0 < 0 → ∀ᶠ t in 𝓝 (0 : ℝ), f t < 0 :=
      fun f hf h0 => hf.continuousAt.eventually_lt continuousAt_const h0
    have hfut := future_of_upperSheet hxS
    refine ((hc (fun t : ℝ => -(x + t • r) 2) (by fun_prop) (by simpa using hfut.1)).and
      (hc (fun t : ℝ => mink (x + t • r) (x + t • r))
        (continuous_mink_self.comp (by fun_prop)) (by simpa using hfut.2))).and
      ((Finset.eventually_all _).2 fun j hj =>
        hc (fun t : ℝ => mink (e j) (x + t • r)) ((continuous_mink _).comp (by fun_prop))
          (by simpa using hxe j (Finset.mem_range.mp hj))) |>.mono ?_
    rintro t ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨by linarith, h2⟩, h3⟩
  have hinP : ∀ t : ℝ, (Future (x + t • r) ∧ ∀ j ∈ Finset.range n, mink (e j) (x + t • r) < 0) →
      nrm (x + t • r) ∈ polySet n e := by
    rintro t ⟨hf, he⟩
    rw [polySet_eq]
    refine ⟨nrm_mem hf, fun j hj => ?_⟩
    rw [mink_nrm]
    exact (mul_neg_of_pos_of_neg (inv_pos.mpr (tau_pos_of_future hf))
      (he j (Finset.mem_range.mpr hj))).le
  have hval : ∀ t : ℝ, mink r (nrm (x + t • r)) =
      (tau (x + t • r))⁻¹ * (t * mink r r) := by
    intro t; rw [mink_nrm, mink_add_left, mink_smul_left, hrx]; ring
  rcases hC.one_sign r hr with hneg | hpos
  · obtain ⟨t, ht, ht0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin : ∀ᶠ t in 𝓝[>] (0 : ℝ), _ ∧ t ∈ Ioi 0).exists
    have h := nonpos_on_polySet hC.poly r hneg _ (hinP t ht)
    rw [hval] at h
    have := tau_pos_of_future ht.1
    have : 0 < (tau (x + t • r))⁻¹ * (t * mink r r) :=
      mul_pos (inv_pos.mpr this) (mul_pos ht0 hrr)
    linarith
  · obtain ⟨t, ht, ht0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      self_mem_nhdsWithin : ∀ᶠ t in 𝓝[<] (0 : ℝ), _ ∧ t ∈ Iio 0).exists
    have h := nonpos_on_polySet hC.poly (-r)
      (fun i hi => by unfold mink at *; have := hpos i hi; simp only [Pi.neg_apply]; linarith)
      _ (hinP t ht)
    have hneg' : mink (-r) (nrm (x + t • r)) = -mink r (nrm (x + t • r)) := by
      unfold mink; simp only [Pi.neg_apply]; ring
    rw [hneg', hval] at h
    have := tau_pos_of_future ht.1
    have : (tau (x + t • r))⁻¹ * (t * mink r r) < 0 :=
      mul_neg_of_pos_of_neg (inv_pos.mpr this) (mul_neg_of_neg_of_pos ht0 hrr)
    linarith

/-- **B6.** The polygon is the closure of the component of `S \ M` through `nrm xs`. -/
theorem polySet_eq_chamber {n : ℕ} {e p : ℕ → Fin 3 → ℝ} {Rs : Set (Fin 3 → ℝ)}
    {xs : Fin 3 → ℝ} (hC : ChamberData n e p Rs xs) :
    nrm xs ∈ upperSheet \ mirrorSet Rs ∧
      polySet n e = closure (connectedComponentIn (upperSheet \ mirrorSet Rs) (nrm xs)) := by
  have hxs : nrm xs ∈ openPoly n e := by
    refine ⟨nrm_mem hC.xs_fut, fun j hj => ?_⟩
    rw [mink_nrm]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr (tau_pos_of_future hC.xs_fut)) (hC.xs_int j hj)
  have hdisj := openPoly_disjoint hC
  refine ⟨hdisj hxs, ?_⟩
  -- the component through nrm xs is exactly the open polygon
  have hcomp : connectedComponentIn (upperSheet \ mirrorSet Rs) (nrm xs) = openPoly n e := by
    apply Set.Subset.antisymm
    · intro y hy
      have hK := isPreconnected_connectedComponentIn (F := upperSheet \ mirrorSet Rs)
        (x := nrm xs)
      have hsub := connectedComponentIn_subset (upperSheet \ mirrorSet Rs) (nrm xs)
      have hyS : y ∈ upperSheet := (hsub hy).1
      refine ⟨hyS, fun j hj => ?_⟩
      by_contra hge; push Not at hge
      -- intermediate value on the component: e j vanishes somewhere, a mirror point
      have hx0 : nrm xs ∈ connectedComponentIn (upperSheet \ mirrorSet Rs) (nrm xs) :=
        mem_connectedComponentIn (hdisj hxs)
      obtain ⟨z, hz, hz0⟩ := hK.intermediate_value₂ hx0 hy
        (continuous_mink (e j)).continuousOn continuous_const.continuousOn
        (show mink (e j) (nrm xs) ≤ 0 from (hxs.2 j hj).le) hge
      exact (hsub hz).2 ⟨(hsub hz).1, e j, hC.edges j hj, hz0⟩
    · exact (isPreconnected_openPoly n e).subset_connectedComponentIn hxs hdisj
  rw [hcomp]
  apply Set.Subset.antisymm
  · -- every point of the polygon is a limit of points of the open polygon
    intro x hx
    rw [polySet_eq] at hx
    obtain ⟨hxS, hxe⟩ := hx
    have hxf := future_of_upperSheet hxS
    set g : ℝ → Fin 3 → ℝ := fun t => nrm ((1 - t) • x + t • xs)
    have hg0 : g 0 = x := by simp [g, nrm_of_upperSheet hxS]
    have hgc : ContinuousWithinAt g (Icc 0 1) 0 := by
      apply ContinuousOn.continuousWithinAt _ (left_mem_Icc.mpr zero_le_one)
      refine continuousOn_nrm.comp (by fun_prop) fun t ht =>
        future_convex ht.1 ht.2 hxf hC.xs_fut
    have hmem : ∀ t ∈ Ioc (0 : ℝ) 1, g t ∈ openPoly n e := by
      intro t ⟨ht0, ht1⟩
      have hf := future_convex ht0.le ht1 hxf hC.xs_fut
      refine ⟨nrm_mem hf, fun j hj => ?_⟩
      simp only [g]; rw [mink_nrm, mink_add_left, mink_smul_left, mink_smul_left]
      have h1 := hxe j hj; have h2 := hC.xs_int j hj
      apply mul_neg_of_pos_of_neg (inv_pos.mpr (tau_pos_of_future hf))
      nlinarith
    rw [← hg0]
    have : NeBot (𝓝[Ioc (0:ℝ) 1] 0) := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc zero_ne_one]
      exact left_mem_Icc.mpr zero_le_one
    exact mem_closure_of_tendsto (hgc.tendsto.mono_left (nhdsWithin_mono _ Ioc_subset_Icc_self))
      (eventually_nhdsWithin_of_forall hmem)
  · rw [(isClosed_polySet n e).closure_subset_iff, polySet_eq]
    rintro x ⟨hxS, hxe⟩
    exact ⟨hxS, fun j hj => (hxe j hj).le⟩

end ReflectZphi.Minkowski
