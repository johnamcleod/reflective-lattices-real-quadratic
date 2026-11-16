import ReflectZphi.Cert.Split

/-!
# A faster leaf for the stopped search

`leaf2` recomputes, at every leaf, the vector `r_f = U z` and the three products
`u₀·u₀`, `u₀·r_f`, `r_f·r_f`, then solves one quadratic per window norm `m`. Here the
products are expanded once per cell: with `z₀ = z₁ = 0` (always the case at a leaf of the
search stopped at level 2), `r_f = ∑_{j=2}^{5} z_j c_j` with `c_j` column `j` of `U`, so

  `u₀·r_f = ∑ z_j (u₀·c_j)`,   `r_f·r_f = ∑_{j,l} z_j z_l (c_j·c_l)`,

and the discriminant for the norm `m` is `D₀ + A m` with `D₀ = B² − A C` (one addition per
norm, `A m` precomputed). The table `LeafData` is checked once per cell (`ldCheck`), and
`leaf3_sound` shows that `leaf3` passing implies `leaf2` passing.
-/

namespace ReflectZphi.FastLeaf

open Matrix QuadraticAlgebra ReflectZphi.Lattice ReflectZphi.Enum ReflectZphi.QuadSolve
  ReflectZphi.PolyEnum ReflectZphi.Split

variable {a b : ℤ}

local notation "Nm" => QuadraticAlgebra.norm

/-- Per-cell constants: `A = u₀·u₀`, `Bc j = u₀·c_j`, `Q j l = c_j·c_l`, `Am = [A m]`. -/
structure LeafData (a b : ℤ) where
  A : O a b
  Bc : ℕ → O a b
  Q : ℕ → ℕ → O a b
  Am : List (O a b)

/-- `c • q` for an integer `c`, componentwise. -/
def zs (c : ℤ) (q : O a b) : O a b := ⟨c * q.re, c * q.im⟩

lemma zs_eq (c : ℤ) (q : O a b) : zs c q = (c : O a b) * q := by
  ext <;> simp [zs]

/-- `∑_{j=2}^{5} z_j (u₀·c_j)`. -/
def linB (ld : LeafData a b) (z : ℕ → ℤ) : O a b :=
  zs (z 2) (ld.Bc 2) + zs (z 3) (ld.Bc 3) + zs (z 4) (ld.Bc 4) + zs (z 5) (ld.Bc 5)

/-- One row of `quadC`. -/
def qrow (ld : LeafData a b) (z : ℕ → ℤ) (j : ℕ) : O a b :=
  zs (z j * z 2) (ld.Q j 2) + zs (z j * z 3) (ld.Q j 3) + zs (z j * z 4) (ld.Q j 4) +
    zs (z j * z 5) (ld.Q j 5)

/-- `∑_{j,l=2}^{5} z_j z_l (c_j·c_l)`. -/
def quadC (ld : LeafData a b) (z : ℕ → ℤ) : O a b :=
  qrow ld z 2 + qrow ld z 3 + qrow ld z 4 + qrow ld z 5

/-- The per-norm check shared by `leaf2` and `leaf3`. -/
def body (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ) (Ps : ℕ → Fin 3 → O a b)
    (norms : List (O a b)) (A B Δ : O a b) (rf u0 : Fin 3 → O a b) : Bool :=
  let r := sqrtsO Δ
  (r.1 && decide (A ≠ 0)) &&
    (r.2.filterMap fun s => divO (s - B) A).all fun t => leafCheck G n Ps norms (rf + t • u0)

lemma leaf2_eq (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ) (Ps : ℕ → Fin 3 → O a b)
    (norms : List (O a b)) (U : ℕ → ℕ → ℤ) (z : ℕ → ℤ) :
    leaf2 G n Ps norms U z = norms.all fun m =>
      body G n Ps norms (bilE G (colVec U 0) (colVec U 0))
        (bilE G (colVec U 0) (vecOf (mv U z)))
        (bilE G (colVec U 0) (vecOf (mv U z)) * bilE G (colVec U 0) (vecOf (mv U z)) -
          bilE G (colVec U 0) (colVec U 0) * (bilE G (vecOf (mv U z)) (vecOf (mv U z)) - m))
        (vecOf (mv U z)) (colVec U 0) := by
  simp only [leaf2, solveQuad, body]

/-- The fast leaf. -/
def leaf3 (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ) (Ps : ℕ → Fin 3 → O a b)
    (norms : List (O a b)) (U : ℕ → ℕ → ℤ) (ld : LeafData a b) (z : ℕ → ℤ) : Bool :=
  decide (z 0 = 0) && decide (z 1 = 0) &&
    (let B := linB ld z
     let D0 := B * B - ld.A * quadC ld z
     (norms.zip ld.Am).all fun p => body G n Ps norms ld.A B (D0 + p.2) (vecOf (mv U z))
       (colVec U 0))

/-- The table is right. -/
def ldCheck (G : Matrix (Fin 3) (Fin 3) (O a b)) (U : ℕ → ℕ → ℤ) (norms : List (O a b))
    (ld : LeafData a b) : Bool :=
  decide (ld.A = bilE G (colVec U 0) (colVec U 0)) &&
  ([2, 3, 4, 5].all fun j => decide (ld.Bc j = bilE G (colVec U 0) (colVec U j))) &&
  ([2, 3, 4, 5].all fun j => [2, 3, 4, 5].all fun l =>
    decide (ld.Q j l = bilE G (colVec U j) (colVec U l))) &&
  decide (ld.Am = norms.map fun m => ld.A * m)

lemma all_zip_map {α β : Type*} (l : List α) (f : α → β) (g : α × β → Bool) :
    (l.zip (l.map f)).all g = l.all fun m => g (m, f m) := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [ih]

/-- `U z` with `z₀ = z₁ = 0`, as a combination of columns 2–5. -/
lemma vecOf_mv_cols (U : ℕ → ℕ → ℤ) {z : ℕ → ℤ} (h0 : z 0 = 0) (h1 : z 1 = 0) (k : Fin 3) :
    vecOf (a := a) (b := b) (mv U z) k =
      (z 2 : O a b) * colVec U 2 k + (z 3 : O a b) * colVec U 3 k +
        (z 4 : O a b) * colVec U 4 k + (z 5 : O a b) * colVec U 5 k := by
  fin_cases k <;> (ext <;> simp [vecOf, mv, lsum, colVec, h0, h1] <;> ring)

lemma bil_smul_left (G : Matrix (Fin 3) (Fin 3) (O a b)) (c : O a b) (x y : Fin 3 → O a b) :
    bil G (c • x) y = c * bil G x y := by simp [bil, smul_dotProduct]

lemma bil_smul_right (G : Matrix (Fin 3) (Fin 3) (O a b)) (c : O a b) (x y : Fin 3 → O a b) :
    bil G x (c • y) = c * bil G x y := by simp [bil, mulVec_smul, dotProduct_smul]

theorem leaf3_sound {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ} {Ps : ℕ → Fin 3 → O a b}
    {norms : List (O a b)} {U : ℕ → ℕ → ℤ} {ld : LeafData a b}
    (hld : ldCheck G U norms ld = true) (z : ℕ → ℤ) (h : leaf3 G n Ps norms U ld z = true) :
    leaf2 G n Ps norms U z = true := by
  simp only [ldCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil,
    Bool.and_true] at hld
  obtain ⟨⟨⟨hA, hB2, hB3, hB4, hB5⟩, hQ⟩, hAm⟩ := hld
  obtain ⟨⟨q22, q23, q24, q25⟩, ⟨q32, q33, q34, q35⟩, ⟨q42, q43, q44, q45⟩,
    ⟨q52, q53, q54, q55⟩⟩ := hQ
  simp only [leaf3, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h0, h1⟩, hall⟩ := h
  rw [hAm, all_zip_map] at hall
  set c2 := colVec (a := a) (b := b) U 2
  set c3 := colVec (a := a) (b := b) U 3
  set c4 := colVec (a := a) (b := b) U 4
  set c5 := colVec (a := a) (b := b) U 5
  set u0 := colVec (a := a) (b := b) U 0
  have hrf : vecOf (a := a) (b := b) (mv U z) =
      (z 2 : O a b) • c2 + (z 3 : O a b) • c3 + (z 4 : O a b) • c4 + (z 5 : O a b) • c5 :=
    funext fun k => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; exact vecOf_mv_cols U h0 h1 k
  simp only [bilE_eq] at hA hB2 hB3 hB4 hB5
  simp only [bilE_eq] at q22 q23 q24 q25 q32 q33 q34 q35
  simp only [bilE_eq] at q42 q43 q44 q45 q52 q53 q54 q55
  have eB : linB ld z = bilE G u0 (vecOf (mv U z)) := by
    rw [bilE_eq, hrf]
    simp only [bil_add_right, bil_smul_right, linB, zs_eq, hB2, hB3, hB4, hB5]
  have eC : quadC ld z = bilE G (vecOf (mv U z)) (vecOf (mv U z)) := by
    rw [bilE_eq, hrf]
    simp only [bil_add_left, bil_add_right, bil_smul_left, bil_smul_right, quadC, qrow, zs_eq,
      q22, q23, q24, q25, q32, q33, q34, q35, q42, q43, q44, q45, q52, q53, q54, q55,
      Int.cast_mul]
    ring
  rw [leaf2_eq]
  rw [List.all_eq_true] at hall ⊢
  intro m hm
  have := hall m hm
  rw [eB, eC, hA, ← bilE_eq] at this
  convert this using 2
  ring

/-- The search is monotone in its leaf. -/
theorem enumAuxS_mono {a' : ℕ → ℕ → ℤ} {w : ℕ → ℤ} {n stop : ℕ} {leaf leaf' : (ℕ → ℤ) → Bool}
    (h : ∀ z, leaf z = true → leaf' z = true) :
    ∀ k z B, enumAuxS a' w n stop leaf k z B = true → enumAuxS a' w n stop leaf' k z B = true := by
  intro k
  induction k with
  | zero => intro z B hk; exact h z hk
  | succ k ih =>
    intro z B hk
    unfold enumAuxS at hk ⊢
    by_cases hs : k + 1 ≤ stop
    · simp only [hs, ↓reduceIte] at hk ⊢; exact h z hk
    simp only [hs, ↓reduceIte] at hk ⊢
    by_cases hB : B < 0
    · simp only [hB, ↓reduceIte]
    simp only [hB, ↓reduceIte] at hk ⊢
    split at hk
    · rename_i hg
      simp only [hg, ↓reduceIte]
      exact allRange_of_forall fun t h1 h2 => ih _ _ (allRange_spec hk t h1 h2)
    · exact absurd hk (by simp)

/-- **A cell, with the fast leaf.** -/
theorem cellCheck_fast {G : Matrix (Fin 3) (Fin 3) (O a b)} {f : Fin 3 → Fin 3 → O a b}
    {n : ℕ} {Ps : ℕ → Fin 3 → O a b} {norms : List (O a b)} {c : Cells.CellData a b}
    {ld : LeafData a b} (h0 : cellPre G f n Ps norms c = true)
    (hld : ldCheck G c.U norms ld = true)
    (he : enumS c.aL c.w 6 2 (leaf3 G n Ps norms c.U ld) (c.S * c.K) = true) :
    Check.cellCheck G f n Ps norms c = true :=
  cellCheck_of h0 (enumAuxS_mono (leaf3_sound hld) 6 _ _ he)

/-! ### The all-integer leaf

Per norm, only the integer `N = Nm(D₀ + A m)` is computed; the slow path (`body`) is taken
only when `N ≥ 0` passes the residue filter, i.e. when `N` may be a square. -/

/-- `(B·B − A·C)` as an integer pair, from the table (`B = linB`, `C = quadC`). -/
def D0Z (a b : ℤ) (ld : LeafData a b) (z : ℕ → ℤ) : ℤ × ℤ :=
  let x1 := z 2 * (ld.Bc 2).re + z 3 * (ld.Bc 3).re + z 4 * (ld.Bc 4).re + z 5 * (ld.Bc 5).re
  let y1 := z 2 * (ld.Bc 2).im + z 3 * (ld.Bc 3).im + z 4 * (ld.Bc 4).im + z 5 * (ld.Bc 5).im
  let row (j : ℕ) : ℤ × ℤ :=
    (z j * z 2 * (ld.Q j 2).re + z j * z 3 * (ld.Q j 3).re + z j * z 4 * (ld.Q j 4).re +
      z j * z 5 * (ld.Q j 5).re,
     z j * z 2 * (ld.Q j 2).im + z j * z 3 * (ld.Q j 3).im + z j * z 4 * (ld.Q j 4).im +
      z j * z 5 * (ld.Q j 5).im)
  let x2 := (row 2).1 + (row 3).1 + (row 4).1 + (row 5).1
  let y2 := (row 2).2 + (row 3).2 + (row 4).2 + (row 5).2
  let ax := ld.A.re
  let ay := ld.A.im
  (x1 * x1 + a * y1 * y1 - (ax * x2 + a * ay * y2),
   x1 * y1 + y1 * x1 + b * y1 * y1 - (ax * y2 + ay * x2 + b * ay * y2))

lemma D0Z_eq (ld : LeafData a b) (z : ℕ → ℤ) :
    D0Z a b ld z = ((linB ld z * linB ld z - ld.A * quadC ld z).re,
      (linB ld z * linB ld z - ld.A * quadC ld z).im) := by
  simp only [D0Z, linB, quadC, qrow, zs, re_mul, im_mul, re_add, im_add, re_sub, im_sub]

/-- The loop over the norms (paired with `A m`). -/
def nloop (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ) (Ps : ℕ → Fin 3 → O a b)
    (norms : List (O a b)) (A B : O a b) (rf u0 : Fin 3 → O a b) (x y : ℤ) :
    List (O a b × O a b) → Bool
  | [] => true
  | p :: rest =>
    (let u := x + p.2.re
     let v := y + p.2.im
     let N := u * u + b * u * v - a * v * v
     if decide (N < 0) || !sqFilter N.toNat then true
     else body G n Ps norms A B ⟨u, v⟩ rf u0) && nloop G n Ps norms A B rf u0 x y rest

/-- The all-integer leaf. -/
def leaf4 (G : Matrix (Fin 3) (Fin 3) (O a b)) (n : ℕ) (Ps : ℕ → Fin 3 → O a b)
    (norms : List (O a b)) (U : ℕ → ℕ → ℤ) (ld : LeafData a b) (z : ℕ → ℤ) : Bool :=
  decide (z 0 = 0) && decide (z 1 = 0) && decide (ld.A ≠ 0) &&
    match D0Z a b ld z with
    | (x, y) => nloop G n Ps norms ld.A (linB ld z) (vecOf (mv U z)) (colVec U 0) x y
        (norms.zip ld.Am)

/-- No square root, no solution: `body` passes. -/
lemma body_of_nonsq {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ} {Ps : ℕ → Fin 3 → O a b}
    {norms : List (O a b)} {A B Δ : O a b} {rf u0 : Fin 3 → O a b} (hA : A ≠ 0)
    (h : (decide (Nm Δ < 0) || !sqFilter (Nm Δ).toNat) = true) :
    body G n Ps norms A B Δ rf u0 = true := by
  have hs : sqrtsZ (Nm Δ) = (true, []) := by
    unfold sqrtsZ
    by_cases hn : Nm Δ < 0
    · simp [hn]
    · have : sqFilter (Nm Δ).toNat = false := by simpa [hn] using h
      simp [hn, this]
  simp [body, sqrtsO, hs, hA]

lemma nloop_sound {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ} {Ps : ℕ → Fin 3 → O a b}
    {norms : List (O a b)} {A B D : O a b} {rf u0 : Fin 3 → O a b} (hA : A ≠ 0) :
    ∀ l : List (O a b × O a b), nloop G n Ps norms A B rf u0 D.re D.im l = true →
      l.all (fun p => body G n Ps norms A B (D + p.2) rf u0) = true := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro h
    simp only [nloop, Bool.and_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ih h.2⟩
    have hD : D + p.2 = ⟨D.re + p.2.re, D.im + p.2.im⟩ := by ext <;> simp
    have hN : Nm (D + p.2) = (D.re + p.2.re) * (D.re + p.2.re) +
        b * (D.re + p.2.re) * (D.im + p.2.im) - a * (D.im + p.2.im) * (D.im + p.2.im) := by
      rw [QuadraticAlgebra.norm_def]; simp
    have h1 := h.1
    split at h1
    · rename_i hc
      exact body_of_nonsq hA (by rw [hN]; exact hc)
    · rw [hD]; exact h1

theorem leaf4_sound {G : Matrix (Fin 3) (Fin 3) (O a b)} {n : ℕ} {Ps : ℕ → Fin 3 → O a b}
    {norms : List (O a b)} {U : ℕ → ℕ → ℤ} {ld : LeafData a b} (z : ℕ → ℤ)
    (h : leaf4 G n Ps norms U ld z = true) : leaf3 G n Ps norms U ld z = true := by
  simp only [leaf4, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, hA⟩, hl⟩ := h
  rw [D0Z_eq] at hl
  simp only [leaf3, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨h0, h1⟩, nloop_sound hA _ hl⟩

/-- **A cell, with the all-integer leaf.** -/
theorem cellCheck_fast4 {G : Matrix (Fin 3) (Fin 3) (O a b)} {f : Fin 3 → Fin 3 → O a b}
    {n : ℕ} {Ps : ℕ → Fin 3 → O a b} {norms : List (O a b)} {c : Cells.CellData a b}
    {ld : LeafData a b} (h0 : cellPre G f n Ps norms c = true)
    (hld : ldCheck G c.U norms ld = true)
    (he : enumS c.aL c.w 6 2 (leaf4 G n Ps norms c.U ld) (c.S * c.K) = true) :
    Check.cellCheck G f n Ps norms c = true :=
  cellCheck_of h0 (enumAuxS_mono (fun z hz => leaf3_sound hld z (leaf4_sound z hz)) 6 _ _ he)

end ReflectZphi.FastLeaf
