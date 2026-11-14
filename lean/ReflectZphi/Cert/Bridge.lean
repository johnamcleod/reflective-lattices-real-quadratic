import ReflectZphi.Geometry.Transfer
import ReflectZphi.Imported

/-!
# The certificate-to-chamber bridge at the lattice level

All the data are over `O`, and every hypothesis is an exact statement in `O` or a sign of
`ι₁`:
* a `G`-orthogonal basis `f 0, f 1, f 2`, with signs `(+, +, −)` at `ι₁`, which gives the
  coordinates `T`;
* roots `rs 0, …, rs (n-1)`, vertices `Ps i` and an interior point `Xs`;
* `hone`: every root of `L` has one sign on the vertices. This is the hypothesis that the
  enumeration certificates (B7, B8) are to discharge.

From these, `isChamber_of_cert` builds a compact chamber, and `reflective_of_cert`
(assuming `VinbergChamber`) concludes that `L` is reflective.
-/

namespace ReflectZphi.Bridge

open Matrix Set ReflectZphi.Minkowski ReflectZphi.Geometry ReflectZphi.Lattice
  ReflectZphi.Transfer

variable {a b : ℤ} (hd : 0 ≤ (b : ℝ) ^ 2 + 4 * a) (G : Matrix (Fin 3) (Fin 3) (O a b))

/-- `det3` over `O`. -/
def det3O (x y z : Fin 3 → O a b) : O a b :=
  x 0 * (y 1 * z 2 - y 2 * z 1) - x 1 * (y 0 * z 2 - y 2 * z 0) + x 2 * (y 0 * z 1 - y 1 * z 0)

lemma real_bil (u w : Fin 3 → O a b) :
    form (realForm hd G) (realVec hd u) (realVec hd w) = ι₁ hd (bil G u w) := by
  unfold form bil realForm realVec
  rw [RingHom.map_dotProduct]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rw [RingHom.map_mulVec]
  rfl

lemma real_det3 (x y z : Fin 3 → O a b) :
    det3 (realVec hd x) (realVec hd y) (realVec hd z) = ι₁ hd (det3O x y z) := by
  simp [det3, det3O, realVec, map_sub, map_mul, map_add]

lemma det3_mulVec (T : Matrix (Fin 3) (Fin 3) ℝ) (x y z : Fin 3 → ℝ) :
    det3 (T *ᵥ x) (T *ᵥ y) (T *ᵥ z) = T.det * det3 x y z := by
  simp [det3, mulVec, dotProduct, Fin.sum_univ_three, Matrix.det_fin_three]; ring

/-- The exact (sign) conditions of a polygon certificate. -/
structure PolyCert (n : ℕ) (f : Fin 3 → Fin 3 → O a b) (rs Ps : ℕ → Fin 3 → O a b)
    (Xs : Fin 3 → O a b) : Prop where
  -- the orthogonal basis
  orth : ∀ i j, i ≠ j → bil G (f i) (f j) = 0
  f0 : 0 < ι₁ hd (bil G (f 0) (f 0))
  f1 : 0 < ι₁ hd (bil G (f 1) (f 1))
  f2 : ι₁ hd (bil G (f 2) (f 2)) < 0
  detF : ι₁ hd (det3O (f 0) (f 1) (f 2)) ≠ 0
  -- the polygon
  three_le : 3 ≤ n
  roots : ∀ i, i < n → IsRoot hd G (rs i)
  on_left : ∀ i, i + 1 < n → bil G (rs i) (Ps i) = 0
  on_right : ∀ i, i + 1 < n → bil G (rs (i + 1)) (Ps i) = 0
  last_left : bil G (rs (n - 1)) (Ps (n - 1)) = 0
  last_right : bil G (rs 0) (Ps (n - 1)) = 0
  e1_p2 : ι₁ hd (bil G (rs 1) (Ps 2)) < 0
  e0_pn2 : ι₁ hd (bil G (rs 0) (Ps (n - 2))) < 0
  ej_p0 : ∀ j, 2 ≤ j → j < n → ι₁ hd (bil G (rs j) (Ps 0)) < 0
  fan_pos : ∀ i, 1 ≤ i → i + 2 ≤ n →
    0 < ι₁ hd (det3O (f 0) (f 1) (f 2) * det3O (Ps 0) (Ps i) (Ps (i + 1)))
  -- vertices and the interior point are future timelike (on the side of f 2)
  P_neg : ∀ i, i < n → ι₁ hd (bil G (Ps i) (Ps i)) < 0
  P_side : ∀ i, i < n → ι₁ hd (bil G (Ps i) (f 2)) < 0
  X_neg : ι₁ hd (bil G Xs Xs) < 0
  X_side : ι₁ hd (bil G Xs (f 2)) < 0
  X_int : ∀ i, i < n → ι₁ hd (bil G (rs i) Xs) < 0

section coords

variable {hd G}
variable {n : ℕ} {f : Fin 3 → Fin 3 → O a b} {rs Ps : ℕ → Fin 3 → O a b} {Xs : Fin 3 → O a b}

/-- The real matrix whose columns are the basis vectors. -/
noncomputable def Fr (f : Fin 3 → Fin 3 → O a b) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => ι₁ hd (f j i)

/-- The norms `c j = f j · f j` at `ι₁`. -/
noncomputable def cvec (f : Fin 3 → Fin 3 → O a b) : Fin 3 → ℝ :=
  fun j => ι₁ hd (bil G (f j) (f j))

/-- The scale factors `(√c₀, √c₁, √−c₂)`. -/
noncomputable def svec (f : Fin 3 → Fin 3 → O a b) : Fin 3 → ℝ :=
  ![Real.sqrt (cvec (hd := hd) (G := G) f 0), Real.sqrt (cvec (hd := hd) (G := G) f 1),
    Real.sqrt (-cvec (hd := hd) (G := G) f 2)]

lemma Fr_det (f : Fin 3 → Fin 3 → O a b) :
    (Fr (hd := hd) f).det = ι₁ hd (det3O (f 0) (f 1) (f 2)) := by
  simp [Fr, Matrix.det_fin_three, det3O, map_sub, map_mul, map_add]; ring

lemma Fr_col (f : Fin 3 → Fin 3 → O a b) (j : Fin 3) :
    Fr (hd := hd) f *ᵥ Pi.single j 1 = realVec hd (f j) := by
  funext i; simp [Fr, realVec, mulVec_single]

lemma FrT_B_Fr (hc : PolyCert hd G n f rs Ps Xs) :
    (Fr (hd := hd) f)ᵀ * realForm hd G * Fr (hd := hd) f =
      diagonal (cvec (hd := hd) (G := G) f) := by
  ext i j
  have : ((Fr (hd := hd) f)ᵀ * realForm hd G * Fr (hd := hd) f) i j =
      form (realForm hd G) (realVec hd (f i)) (realVec hd (f j)) := by
    simp [Fr, form, realVec, Matrix.mul_apply, dotProduct, mulVec, Finset.mul_sum,
      mul_comm, mul_left_comm]
    rw [Finset.sum_comm]
  rw [this, real_bil]
  by_cases hij : i = j
  · subst hij; simp [cvec]
  · rw [hc.orth i j hij, map_zero, diagonal_apply_ne _ hij]

/-- The coordinate change `T = diag(s) F⁻¹`. -/
noncomputable def Tm (f : Fin 3 → Fin 3 → O a b) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal (svec (hd := hd) (G := G) f) * (Fr (hd := hd) f)⁻¹

/-- Its inverse `F diag(s)⁻¹`. -/
noncomputable def Tinv (f : Fin 3 → Fin 3 → O a b) : Matrix (Fin 3) (Fin 3) ℝ :=
  Fr (hd := hd) f * diagonal (fun j => (svec (hd := hd) (G := G) f j)⁻¹)

lemma svec_pos (hc : PolyCert hd G n f rs Ps Xs) (j : Fin 3) :
    0 < svec (hd := hd) (G := G) f j := by
  fin_cases j
  · exact Real.sqrt_pos.mpr hc.f0
  · exact Real.sqrt_pos.mpr hc.f1
  · exact Real.sqrt_pos.mpr (by simpa [cvec] using neg_pos.mpr hc.f2)

lemma Fr_det_ne (hc : PolyCert hd G n f rs Ps Xs) : (Fr (hd := hd) f).det ≠ 0 := by
  rw [Fr_det]; exact hc.detF

lemma diag_inv_mul (hc : PolyCert hd G n f rs Ps Xs) :
    diagonal (fun j => (svec (hd := hd) (G := G) f j)⁻¹) *
      diagonal (svec (hd := hd) (G := G) f) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext j; exact inv_mul_cancel₀ (svec_pos hc j).ne'

lemma diag_mul_inv (hc : PolyCert hd G n f rs Ps Xs) :
    diagonal (svec (hd := hd) (G := G) f) *
      diagonal (fun j => (svec (hd := hd) (G := G) f j)⁻¹) = 1 := by
  rw [diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext j; exact mul_inv_cancel₀ (svec_pos hc j).ne'

lemma Tinv_mul_Tm (hc : PolyCert hd G n f rs Ps Xs) :
    Tinv (hd := hd) (G := G) f * Tm (hd := hd) (G := G) f = 1 := by
  have hu : IsUnit (Fr (hd := hd) f).det := isUnit_iff_ne_zero.mpr (Fr_det_ne hc)
  unfold Tinv Tm
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (diagonal _), diag_inv_mul hc, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hu]

lemma Tm_mul_Tinv (hc : PolyCert hd G n f rs Ps Xs) :
    Tm (hd := hd) (G := G) f * Tinv (hd := hd) (G := G) f = 1 := by
  have hu : IsUnit (Fr (hd := hd) f).det := isUnit_iff_ne_zero.mpr (Fr_det_ne hc)
  unfold Tinv Tm
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ (Fr _), Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul, diag_mul_inv hc]

lemma B_eq (hc : PolyCert hd G n f rs Ps Xs) :
    realForm hd G = (Tm (hd := hd) (G := G) f)ᵀ * Jmat * Tm (hd := hd) (G := G) f := by
  have hu : IsUnit (Fr (hd := hd) f).det := isUnit_iff_ne_zero.mpr (Fr_det_ne hc)
  have hDJD : diagonal (svec (hd := hd) (G := G) f) * Jmat *
      diagonal (svec (hd := hd) (G := G) f) = diagonal (cvec (hd := hd) (G := G) f) := by
    unfold Jmat
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1; funext j
    have h0 := hc.f0; have h1 := hc.f1; have h2 := hc.f2
    fin_cases j <;> simp [svec, cvec]
    · rw [Real.mul_self_sqrt h0.le]
    · rw [Real.mul_self_sqrt h1.le]
    · rw [Real.mul_self_sqrt (by linarith)]; ring
  have hFF : ((Fr (hd := hd) f)⁻¹)ᵀ * (Fr (hd := hd) f)ᵀ = 1 := by
    rw [← transpose_mul, Matrix.mul_nonsing_inv _ hu, transpose_one]
  unfold Tm
  rw [transpose_mul, diagonal_transpose]
  calc realForm hd G
      = (((Fr (hd := hd) f)⁻¹)ᵀ * (Fr (hd := hd) f)ᵀ) * realForm hd G *
          ((Fr (hd := hd) f) * (Fr (hd := hd) f)⁻¹) := by
        rw [hFF, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, Matrix.mul_one]
    _ = ((Fr (hd := hd) f)⁻¹)ᵀ * ((Fr (hd := hd) f)ᵀ * realForm hd G * Fr (hd := hd) f) *
          (Fr (hd := hd) f)⁻¹ := by simp only [Matrix.mul_assoc]
    _ = ((Fr (hd := hd) f)⁻¹)ᵀ * (diagonal (svec (hd := hd) (G := G) f) * Jmat *
          diagonal (svec (hd := hd) (G := G) f)) * (Fr (hd := hd) f)⁻¹ := by
        rw [FrT_B_Fr hc, hDJD]
    _ = _ := by simp only [Matrix.mul_assoc]

lemma Tm_v0 (hc : PolyCert hd G n f rs Ps Xs) :
    Tm (hd := hd) (G := G) f *ᵥ realVec hd (f 2) = ![0, 0, svec (hd := hd) (G := G) f 2] := by
  have hu : IsUnit (Fr (hd := hd) f).det := isUnit_iff_ne_zero.mpr (Fr_det_ne hc)
  rw [← Fr_col, Tm, mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.mul_one]
  funext i; fin_cases i <;> simp [mulVec_single]

lemma mink_T (hc : PolyCert hd G n f rs Ps Xs) (u w : Fin 3 → O a b) :
    mink (Tm (hd := hd) (G := G) f *ᵥ realVec hd u) (Tm (hd := hd) (G := G) f *ᵥ realVec hd w) =
      ι₁ hd (bil G u w) := by
  rw [← form_eq_mink (B_eq hc), real_bil]

lemma det_Tm_sign (hc : PolyCert hd G n f rs Ps Xs) {X : ℝ}
    (hX : 0 < (Fr (hd := hd) f).det * X) : 0 < (Tm (hd := hd) (G := G) f).det * X := by
  have hd0 := Fr_det_ne hc
  unfold Tm
  rw [det_mul, det_diagonal, det_nonsing_inv, Ring.inverse_eq_inv']
  have hprod : 0 < ∏ j, svec (hd := hd) (G := G) f j :=
    Finset.prod_pos fun j _ => svec_pos hc j
  have : (∏ j, svec (hd := hd) (G := G) f j) * ((Fr (hd := hd) f).det)⁻¹ * X =
      (∏ j, svec (hd := hd) (G := G) f j) * (((Fr (hd := hd) f).det * X) /
        ((Fr (hd := hd) f).det) ^ 2) := by
    field_simp
  rw [this]
  exact mul_pos hprod (div_pos hX (by positivity))

lemma future_T (hc : PolyCert hd G n f rs Ps Xs) {u : Fin 3 → O a b}
    (hneg : ι₁ hd (bil G u u) < 0) (hside : ι₁ hd (bil G u (f 2)) < 0) :
    Future (Tm (hd := hd) (G := G) f *ᵥ realVec hd u) := by
  refine ⟨?_, by rw [mink_T hc]; exact hneg⟩
  have h := mink_T hc u (f 2)
  rw [Tm_v0 hc] at h
  have hs := svec_pos hc 2
  have : mink (Tm (hd := hd) (G := G) f *ᵥ realVec hd u) ![0, 0, svec (hd := hd) (G := G) f 2] =
      -(svec (hd := hd) (G := G) f 2 * (Tm (hd := hd) (G := G) f *ᵥ realVec hd u) 2) := by
    simp [mink]; ring
  rw [this] at h
  nlinarith

/-- The polygon data of a certificate, in `J` coordinates. -/
lemma polyData_of_cert (hc : PolyCert hd G n f rs Ps Xs) :
    PolyData n (fun i => Tm (hd := hd) (G := G) f *ᵥ realVec hd (rs i))
      (fun i => Tm (hd := hd) (G := G) f *ᵥ realVec hd (Ps i)) := by
  have hT := mink_T hc
  refine ⟨hc.three_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> beta_reduce
  · intro i hi; rw [hT, hc.on_left i hi, map_zero]
  · intro i hi; rw [hT, hc.on_right i hi, map_zero]
  · rw [hT, hc.last_left, map_zero]
  · rw [hT, hc.last_right, map_zero]
  · rw [hT]; exact hc.e1_p2
  · rw [hT]; exact hc.e0_pn2
  · intro j hj1 hj2; rw [hT]; exact hc.ej_p0 j hj1 hj2
  · intro i hi1 hi2
    rw [det3_mulVec, real_det3]
    apply det_Tm_sign hc
    rw [Fr_det, ← map_mul]; exact hc.fan_pos i hi1 hi2

/-- **Bridge.** A polygon certificate plus the one-sign property gives a compact chamber. -/
theorem isChamber_of_cert (hc : PolyCert hd G n f rs Ps Xs)
    (hone : ∀ r, IsRoot hd G r → (∀ i, i < n → ι₁ hd (bil G r (Ps i)) ≤ 0) ∨
      (∀ i, i < n → 0 ≤ ι₁ hd (bil G r (Ps i)))) :
    ∃ C, IsChamber hd G (realVec hd (f 2)) C ∧ IsCompact C := by
  set T := Tm (hd := hd) (G := G) f
  set RsB : Set (Fin 3 → ℝ) := {x | ∃ r, IsRoot hd G r ∧ realVec hd r = x}
  have hT : ∀ u w, mink (T *ᵥ realVec hd u) (T *ᵥ realVec hd w) = ι₁ hd (bil G u w) :=
    mink_T hc
  have hfT : ∀ {u}, ι₁ hd (bil G u u) < 0 → ι₁ hd (bil G u (f 2)) < 0 →
      Future (T *ᵥ realVec hd u) := fun h1 h2 => future_T hc h1 h2
  have hCD : ChamberData n (fun i => T *ᵥ realVec hd (rs i)) (fun i => T *ᵥ realVec hd (Ps i))
      ((T *ᵥ ·) '' RsB) (T *ᵥ realVec hd Xs) := by
    refine ⟨⟨hc.three_le, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      beta_reduce
    · intro i hi; rw [hT, hc.on_left i hi, map_zero]
    · intro i hi; rw [hT, hc.on_right i hi, map_zero]
    · rw [hT, hc.last_left, map_zero]
    · rw [hT, hc.last_right, map_zero]
    · rw [hT]; exact hc.e1_p2
    · rw [hT]; exact hc.e0_pn2
    · intro j hj1 hj2; rw [hT]; exact hc.ej_p0 j hj1 hj2
    · intro i hi1 hi2
      rw [det3_mulVec, real_det3]
      apply det_Tm_sign hc
      rw [Fr_det, ← map_mul]; exact hc.fan_pos i hi1 hi2
    · intro i hi; exact hfT (hc.P_neg i hi) (hc.P_side i hi)
    · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      rw [hT]; exact hr.totPos.1
    · intro i hi; exact ⟨_, ⟨rs i, hc.roots i hi, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
      rcases hone r hr with h | h
      · left; intro i hi; rw [hT]; exact h i hi
      · right; intro i hi; rw [hT]; exact h i hi
    · exact hfT hc.X_neg hc.X_side
    · intro i hi; rw [hT]; exact hc.X_int i hi
  obtain ⟨x, hx, hC, hK⟩ := chamber_of_J (B_eq hc) (Tinv_mul_Tm hc) (Tm_mul_Tinv hc)
    (svec_pos hc 2) (Tm_v0 hc) hCD
  have hmir : mirrors hd G (realVec hd (f 2)) = mirrorsB (realForm hd G) (realVec hd (f 2)) RsB := by
    ext y
    simp only [mirrors, mirrorsB, RsB, mem_ofPred_eq]
    constructor
    · rintro ⟨hs, r, hr, h0⟩; exact ⟨hs, _, ⟨r, hr, rfl⟩, h0⟩
    · rintro ⟨hs, _, ⟨r, hr, rfl⟩, h0⟩; exact ⟨hs, r, hr, h0⟩
  refine ⟨_, ⟨x, by rw [hmir]; exact hx, by rw [hmir]; exact hC⟩, hK⟩

/-- **Reflectivity from a certificate**, assuming Vinberg's chamber theorem. -/
theorem reflective_of_cert (hV : VinbergChamber) (hns : ¬ IsSquare (b ^ 2 + 4 * a))
    (hadm : Admissible hd G) (hc : PolyCert hd G n f rs Ps Xs)
    (hone : ∀ r, IsRoot hd G r → (∀ i, i < n → ι₁ hd (bil G r (Ps i)) ≤ 0) ∨
      (∀ i, i < n → 0 ≤ ι₁ hd (bil G r (Ps i)))) :
    Reflective hd G := by
  have hv0 : form (realForm hd G) (realVec hd (f 2)) (realVec hd (f 2)) < 0 := by
    rw [real_bil]; exact hc.f2
  obtain ⟨-, -, hiff⟩ := hV a b hd G (realVec hd (f 2)) hns hadm hv0
  exact hiff.mpr (isChamber_of_cert hc hone)

end coords

end ReflectZphi.Bridge
