import BFB.Doublets
import BFB.S4Equiv

/-!
# The `A₄`/`S₄`-symmetric three-Higgs-doublet model: boundedness from below for `Λ₄ = 0`

The quartic part of the `A₄`-symmetric potential of three Higgs doublets `χ₁, χ₂, χ₃` is
(L. Lavoura, A. Milagre, arXiv:2611.05475, Eq. (3); the parametrisation goes back to
A. Degee, I. P. Ivanov, V. Keus, JHEP 02 (2013) 125), with `A_kl = χ_k† χ_l`,

  `V₄ = (Λ₀+Λ₃)/3 (A₁₁² + A₂₂² + A₃₃²) + (2Λ₀-Λ₃)/3 (A₁₁A₂₂ + A₂₂A₃₃ + A₃₃A₁₁)`
  `   + (Λ₁+Λ₂)/2 (|A₁₂|² + |A₂₃|² + |A₃₁|²) + (Λ₁-Λ₂)/2 Re(A₁₂² + A₂₃² + A₃₁²)`
  `   + Λ₄/2 Im(A₁₂² + A₂₃² + A₃₁²)`.

For `Λ₄ = 0` the symmetry is `S₄`.  Lavoura and Milagre conjecture that their necessary
conditions for `V₄ ≥ 0` are also sufficient.  This file proves the conjecture in the
`S₄` case, from first principles:

* `boundedBelow_iff_iv`: for `Λ₄ = 0`, `V₄ ≥ 0` on all field configurations iff the conditions
  of Ivanov–Vazão (JHEP 11 (2020) 104) hold;
* `boundedBelow_iff_lm`: for `Λ₄ = 0`, `V₄ ≥ 0` on all field configurations iff the
  conditions of Lavoura–Milagre, Section 5, hold.

The proof of sufficiency does not follow the geometric argument of Ivanov–Vazão.  It rests on
one inequality for three doublets (`gG_nonneg`): with `N = A₁₁+A₂₂+A₃₃`,
`E = Σ_{k<l} (A_kk A_ll - |A_kl|²)` and `Q = Σ (Im A_kl)²`,

  `τ² N² - 3 τ E - 3 (4τ - 3) Q ≥ 0`  for every `τ ≥ 3/4`.

After an `SU(2)` gauge rotation that makes the upper components of all three doublets real
(`exists_gauge`), twice the left-hand side is the sum of squares
`½ (2τ m₁ - (3-2τ) m₂)² + 6τ |Σ u_k d_k|² + (3/2)(4τ-3) |Σ d_k²|²`,
where `u_k` (real) and `d_k` are the upper and lower components, `m₁ = Σ u_k²`, `m₂ = Σ |d_k|²`.
-/

namespace BFB.A4

/-- The potential as a function of the norms `A_kk` and the products `A₁₂, A₂₃, A₃₁`. -/
noncomputable def V4G (p : Params) (a1 a2 a3 : ℝ) (A12 A23 A31 : ℂ) : ℝ :=
  p.L0 / 3 * (a1 + a2 + a3) ^ 2
    + p.L3 / 3 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - a1 * a2 - a2 * a3 - a3 * a1)
    + p.L1 * (A12.re ^ 2 + A23.re ^ 2 + A31.re ^ 2)
    + p.L2 * (A12.im ^ 2 + A23.im ^ 2 + A31.im ^ 2)
    + p.L4 * (A12.re * A12.im + A23.re * A23.im + A31.re * A31.im)

lemma V4_eq (p : Params) (χ₁ χ₂ χ₃ : Fin 2 → ℂ) :
    V4 p χ₁ χ₂ χ₃ = V4G p (normSq χ₁) (normSq χ₂) (normSq χ₃)
      (inner χ₁ χ₂) (inner χ₂ χ₃) (inner χ₃ χ₁) := by
  unfold V4 V4G
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, pow_two, Complex.mul_re,
    Complex.mul_im]
  ring

/-! ## The key inequality -/

lemma gG_smul (τ s a1 a2 a3 : ℝ) (A12 A23 A31 : ℂ) :
    gG τ (s * a1) (s * a2) (s * a3) ((s : ℂ) * A12) ((s : ℂ) * A23) ((s : ℂ) * A31)
      = s ^ 2 * gG τ a1 a2 a3 A12 A23 A31 := by
  unfold gG
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, Complex.im_ofReal_mul]
  ring

/-- The inequality in real coordinates (upper components `u_k` real, lower components
`x_k + i y_k`): twice the left-hand side is a sum of squares. -/
lemma key_poly {τ : ℝ} (hτ : 3 / 4 ≤ τ) (u1 u2 u3 x1 x2 x3 y1 y2 y3 : ℝ) :
    0 ≤ τ ^ 2 * ((u1 ^ 2 + x1 ^ 2 + y1 ^ 2) + (u2 ^ 2 + x2 ^ 2 + y2 ^ 2)
          + (u3 ^ 2 + x3 ^ 2 + y3 ^ 2)) ^ 2
      - 3 * τ * ((u1 ^ 2 + x1 ^ 2 + y1 ^ 2) * (u2 ^ 2 + x2 ^ 2 + y2 ^ 2)
          + (u2 ^ 2 + x2 ^ 2 + y2 ^ 2) * (u3 ^ 2 + x3 ^ 2 + y3 ^ 2)
          + (u3 ^ 2 + x3 ^ 2 + y3 ^ 2) * (u1 ^ 2 + x1 ^ 2 + y1 ^ 2)
          - ((u1 * u2 + x1 * x2 + y1 * y2) ^ 2 + (x1 * y2 - y1 * x2) ^ 2)
          - ((u2 * u3 + x2 * x3 + y2 * y3) ^ 2 + (x2 * y3 - y2 * x3) ^ 2)
          - ((u3 * u1 + x3 * x1 + y3 * y1) ^ 2 + (x3 * y1 - y3 * x1) ^ 2))
      - 3 * (4 * τ - 3) * ((x1 * y2 - y1 * x2) ^ 2 + (x2 * y3 - y2 * x3) ^ 2
          + (x3 * y1 - y3 * x1) ^ 2) := by
  have hτ0 : 0 ≤ τ := by linarith
  have h43 : 0 ≤ 4 * τ - 3 := by linarith
  have s1 := sq_nonneg (2 * τ * (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)
    - (3 - 2 * τ) * (x1 ^ 2 + y1 ^ 2 + x2 ^ 2 + y2 ^ 2 + x3 ^ 2 + y3 ^ 2))
  have s2 := mul_nonneg hτ0 (sq_nonneg (u1 * x1 + u2 * x2 + u3 * x3))
  have s3 := mul_nonneg hτ0 (sq_nonneg (u1 * y1 + u2 * y2 + u3 * y3))
  have s4 := mul_nonneg h43 (sq_nonneg (x1 ^ 2 - y1 ^ 2 + x2 ^ 2 - y2 ^ 2 + x3 ^ 2 - y3 ^ 2))
  have s5 := mul_nonneg h43 (sq_nonneg (x1 * y1 + x2 * y2 + x3 * y3))
  have id : 2 * (τ ^ 2 * ((u1 ^ 2 + x1 ^ 2 + y1 ^ 2) + (u2 ^ 2 + x2 ^ 2 + y2 ^ 2)
          + (u3 ^ 2 + x3 ^ 2 + y3 ^ 2)) ^ 2
      - 3 * τ * ((u1 ^ 2 + x1 ^ 2 + y1 ^ 2) * (u2 ^ 2 + x2 ^ 2 + y2 ^ 2)
          + (u2 ^ 2 + x2 ^ 2 + y2 ^ 2) * (u3 ^ 2 + x3 ^ 2 + y3 ^ 2)
          + (u3 ^ 2 + x3 ^ 2 + y3 ^ 2) * (u1 ^ 2 + x1 ^ 2 + y1 ^ 2)
          - ((u1 * u2 + x1 * x2 + y1 * y2) ^ 2 + (x1 * y2 - y1 * x2) ^ 2)
          - ((u2 * u3 + x2 * x3 + y2 * y3) ^ 2 + (x2 * y3 - y2 * x3) ^ 2)
          - ((u3 * u1 + x3 * x1 + y3 * y1) ^ 2 + (x3 * y1 - y3 * x1) ^ 2))
      - 3 * (4 * τ - 3) * ((x1 * y2 - y1 * x2) ^ 2 + (x2 * y3 - y2 * x3) ^ 2
          + (x3 * y1 - y3 * x1) ^ 2))
      = 1 / 2 * (2 * τ * (u1 ^ 2 + u2 ^ 2 + u3 ^ 2)
            - (3 - 2 * τ) * (x1 ^ 2 + y1 ^ 2 + x2 ^ 2 + y2 ^ 2 + x3 ^ 2 + y3 ^ 2)) ^ 2
        + 6 * (τ * (u1 * x1 + u2 * x2 + u3 * x3) ^ 2)
        + 6 * (τ * (u1 * y1 + u2 * y2 + u3 * y3) ^ 2)
        + 3 / 2 * ((4 * τ - 3) * (x1 ^ 2 - y1 ^ 2 + x2 ^ 2 - y2 ^ 2 + x3 ^ 2 - y3 ^ 2) ^ 2)
        + 6 * ((4 * τ - 3) * (x1 * y1 + x2 * y2 + x3 * y3) ^ 2) := by
    ring
  linarith

/-- The inequality for doublets whose upper components are real. -/
lemma gG_nonneg_of_real {τ : ℝ} (hτ : 3 / 4 ≤ τ) (ψ₁ ψ₂ ψ₃ : Fin 2 → ℂ)
    (h1 : (ψ₁ 0).im = 0) (h2 : (ψ₂ 0).im = 0) (h3 : (ψ₃ 0).im = 0) :
    0 ≤ gG τ (normSq ψ₁) (normSq ψ₂) (normSq ψ₃) (inner ψ₁ ψ₂) (inner ψ₂ ψ₃) (inner ψ₃ ψ₁) := by
  refine le_of_le_of_eq (key_poly hτ (ψ₁ 0).re (ψ₂ 0).re (ψ₃ 0).re (ψ₁ 1).re (ψ₂ 1).re (ψ₃ 1).re
    (ψ₁ 1).im (ψ₂ 1).im (ψ₃ 1).im) ?_
  unfold gG
  simp only [normSq, inner, Fin.sum_univ_two, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, h1, h2, h3]
  ring

/-- There is a non-zero pair `(α, β)` such that `α χ_k↑ + β χ_k↓` is real for `k = 1, 2, 3`:
three real linear equations in four real unknowns. -/
lemma exists_gauge (χ₁ χ₂ χ₃ : Fin 2 → ℂ) :
    ∃ α β : ℂ, 0 < Complex.normSq α + Complex.normSq β ∧
      (α * χ₁ 0 + β * χ₁ 1).im = 0 ∧ (α * χ₂ 0 + β * χ₂ 1).im = 0 ∧
      (α * χ₃ 0 + β * χ₃ 1).im = 0 := by
  let M : Matrix (Fin 3) (Fin 4) ℝ :=
    !![(χ₁ 0).im, (χ₁ 0).re, (χ₁ 1).im, (χ₁ 1).re;
       (χ₂ 0).im, (χ₂ 0).re, (χ₂ 1).im, (χ₂ 1).re;
       (χ₃ 0).im, (χ₃ 0).re, (χ₃ 1).im, (χ₃ 1).re]
  have hker : LinearMap.ker (Matrix.mulVecLin M) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hMv : M.mulVec v = 0 := by simpa using hv
  have e1 := congrFun hMv 0
  have e2 := congrFun hMv 1
  have e3 := congrFun hMv 2
  simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at e1 e2 e3
  refine ⟨⟨v 0, v 1⟩, ⟨v 2, v 3⟩, ?_, ?_, ?_, ?_⟩
  · simp only [Complex.normSq_mk]
    by_contra hneg
    push_neg at hneg
    have h0 : v 0 = 0 := by nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1), mul_self_nonneg (v 2), mul_self_nonneg (v 3)]
    have h1 : v 1 = 0 := by nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1), mul_self_nonneg (v 2), mul_self_nonneg (v 3)]
    have h2 : v 2 = 0 := by nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1), mul_self_nonneg (v 2), mul_self_nonneg (v 3)]
    have h3 : v 3 = 0 := by nlinarith [mul_self_nonneg (v 0), mul_self_nonneg (v 1), mul_self_nonneg (v 2), mul_self_nonneg (v 3)]
    apply hv0
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  · simp only [Complex.add_im, Complex.mul_im]
    linarith
  · simp only [Complex.add_im, Complex.mul_im]
    linarith
  · simp only [Complex.add_im, Complex.mul_im]
    linarith

/-- The gauge rotation of a doublet by the (unnormalised) `SU(2)` matrix
`[[α, β], [-β*, α*]]`. -/
noncomputable def rot (α β : ℂ) (χ : Fin 2 → ℂ) : Fin 2 → ℂ :=
  ![α * χ 0 + β * χ 1, -(starRingEnd ℂ) β * χ 0 + (starRingEnd ℂ) α * χ 1]

lemma inner_rot (α β : ℂ) (χ ψ : Fin 2 → ℂ) :
    inner (rot α β χ) (rot α β ψ)
      = ((Complex.normSq α + Complex.normSq β : ℝ) : ℂ) * inner χ ψ := by
  simp only [inner, rot, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_add, map_mul, map_neg, Complex.conj_conj, Complex.ofReal_add,
    Complex.normSq_eq_conj_mul_self]
  ring

lemma normSq_eq_inner_re (χ : Fin 2 → ℂ) : normSq χ = (inner χ χ).re := by
  simp only [normSq, inner, Fin.sum_univ_two, Complex.normSq_apply, Complex.add_re,
    Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

lemma normSq_rot (α β : ℂ) (χ : Fin 2 → ℂ) :
    normSq (rot α β χ) = (Complex.normSq α + Complex.normSq β) * normSq χ := by
  rw [normSq_eq_inner_re, inner_rot, Complex.re_ofReal_mul, ← normSq_eq_inner_re]

/-- **The key inequality** for three arbitrary doublets. -/
theorem gG_nonneg {τ : ℝ} (hτ : 3 / 4 ≤ τ) (χ₁ χ₂ χ₃ : Fin 2 → ℂ) :
    0 ≤ gG τ (normSq χ₁) (normSq χ₂) (normSq χ₃) (inner χ₁ χ₂) (inner χ₂ χ₃) (inner χ₃ χ₁) := by
  obtain ⟨α, β, hs, h1, h2, h3⟩ := exists_gauge χ₁ χ₂ χ₃
  have key := gG_nonneg_of_real hτ (rot α β χ₁) (rot α β χ₂) (rot α β χ₃)
    (by simpa [rot] using h1) (by simpa [rot] using h2) (by simpa [rot] using h3)
  rw [normSq_rot, normSq_rot, normSq_rot, inner_rot, inner_rot, inner_rot, gG_smul] at key
  exact nonneg_of_mul_nonneg_right key (by positivity)

/-! ## Sufficiency of the conditions for `Λ₄ = 0` -/

/-- Real-algebra core.  With `m = min(Λ₁, Λ₃)`, the potential is bounded below by
`(Λ₀ + m) N² - 3 m E + 3 (Λ₂ - m) Q`; this linear function of `(E, Q)` is non-negative on the
region cut out by the key inequality. -/
lemma suff_aux {L0 L2 m N2 E Q : ℝ} (hB : 0 ≤ L0 + m) (hE4 : 0 ≤ L0 + m / 4)
    (hC : 0 ≤ L0 + (m + 3 * L2) / 4)
    (harc : |L2| < m → 0 ≤ L0 * (3 * m + L2) + m * L2)
    (hN : 0 ≤ N2) (hE : 0 ≤ E) (hQ : 0 ≤ Q)
    (hg : ∀ τ : ℝ, 3 / 4 ≤ τ → 0 ≤ τ ^ 2 * N2 - 3 * τ * E - 3 * (4 * τ - 3) * Q) :
    0 ≤ (L0 + m) * N2 - 3 * m * E + 3 * (L2 - m) * Q := by
  have g34 := hg (3 / 4) le_rfl
  have hE4N : 4 * E ≤ N2 := by nlinarith
  rcases le_or_gt m L2 with h1 | h1
  · rcases le_or_gt 0 m with hm | hm
    · nlinarith [mul_nonneg (sub_nonneg.mpr h1) hQ, mul_nonneg hm (sub_nonneg.mpr hE4N),
        mul_nonneg hE4 hN]
    · nlinarith [mul_nonneg (sub_nonneg.mpr h1) hQ, mul_nonneg (neg_nonneg.mpr hm.le) hE,
        mul_nonneg hB hN]
  · rcases le_or_gt (m + L2) 0 with h2 | h2
    · -- tangent line at the end point of the arc, `τ = 3/2`
      have g32 := hg (3 / 2) (by norm_num)
      nlinarith [mul_nonneg (sub_nonneg.mpr h1.le) g32, mul_nonneg hC hN,
        mul_nonneg (neg_nonneg.mpr h2) hE]
    · -- tangent line at the point `τ = 3m / (3m + Λ₂)` of the arc
      have habs : |L2| < m := abs_lt.mpr ⟨by linarith, h1⟩
      have ha := harc habs
      obtain ⟨D, hD⟩ : ∃ D : ℝ, D = 3 * m + L2 := ⟨_, rfl⟩
      have hL2 : L2 = D - 3 * m := by linarith
      subst hL2
      have hDpos : 0 < D := by linarith
      have hm : 0 < m := by linarith
      obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = 3 * m / D := ⟨_, rfl⟩
      have hτD : τ * D = 3 * m := by rw [hτ]; field_simp
      have hτ34 : 3 / 4 ≤ τ := by
        rw [hτ, div_le_div_iff₀ (by norm_num) hDpos]
        linarith
      have g := hg τ hτ34
      have hcoef : 0 ≤ L0 + m - m * τ := by
        have h5 : (L0 + m - m * τ) * D = L0 * (3 * m + (D - 3 * m)) + m * (D - 3 * m) := by
          linear_combination (-m) * hτD
        have h6 : 0 ≤ (L0 + m - m * τ) * D := by rw [h5]; exact ha
        exact nonneg_of_mul_nonneg_left h6 hDpos
      have hid : (L0 + m) * N2 - 3 * m * E + 3 * (D - 3 * m - m) * Q
          = D / 3 * (τ ^ 2 * N2 - 3 * τ * E - 3 * (4 * τ - 3) * Q) + (L0 + m - m * τ) * N2 := by
        linear_combination (-τ * N2 / 3 + E + 4 * Q) * hτD
      rw [hid]
      have h7 : 0 ≤ D / 3 * (τ ^ 2 * N2 - 3 * τ * E - 3 * (4 * τ - 3) * Q) :=
        mul_nonneg (by linarith) g
      have h8 := mul_nonneg hcoef hN
      linarith

lemma suff_core {L0 L1 L2 L3 N2 Z P Q E : ℝ} (hc : S4.IVConditions L0 L1 L2 L3)
    (hZ : 0 ≤ Z) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hE : 0 ≤ E) (hN : 0 ≤ N2)
    (hrel : Z + 3 * P = N2 - 3 * E - 3 * Q)
    (hg : ∀ τ : ℝ, 3 / 4 ≤ τ → 0 ≤ τ ^ 2 * N2 - 3 * τ * E - 3 * (4 * τ - 3) * Q) :
    0 ≤ L0 * N2 + L3 * Z + 3 * L1 * P + 3 * L2 * Q := by
  obtain ⟨⟨i1, i2, i3, i4, i5, i6, -, -⟩, m1, m2⟩ := hc
  rcases le_total L1 L3 with h | h
  · have harc : |L2| < L1 → 0 ≤ L0 * (3 * L1 + L2) + L1 * L2 := by
      intro habs
      have h0 : 0 < L1 := lt_of_le_of_lt (abs_nonneg _) habs
      have hD : 0 < 3 * L1 + L2 := by linarith [(abs_lt.mp habs).1]
      by_contra hneg
      push_neg at hneg
      exact m1 ⟨by linarith, (S4.add_div_neg_iff hD).mpr hneg⟩
    have key := suff_aux i1 i5 i3 harc hN hE hQ hg
    have e : L0 * N2 + L3 * Z + 3 * L1 * P + 3 * L2 * Q
        = ((L0 + L1) * N2 - 3 * L1 * E + 3 * (L2 - L1) * Q) + (L3 - L1) * Z := by
      linear_combination L1 * hrel
    rw [e]
    have := mul_nonneg (sub_nonneg.mpr h) hZ
    linarith
  · have harc : |L2| < L3 → 0 ≤ L0 * (3 * L3 + L2) + L3 * L2 := by
      intro habs
      have h0 : 0 < L3 := lt_of_le_of_lt (abs_nonneg _) habs
      have hD : 0 < L2 + 3 * L3 := by linarith [(abs_lt.mp habs).1]
      by_contra hneg
      push_neg at hneg
      exact m2 ⟨by linarith, (S4.add_div_neg_iff hD).mpr (by linarith)⟩
    have key := suff_aux i2 i6 i4 harc hN hE hQ hg
    have e : L0 * N2 + L3 * Z + 3 * L1 * P + 3 * L2 * Q
        = ((L0 + L3) * N2 - 3 * L3 * E + 3 * (L2 - L3) * Q) + 3 * (L1 - L3) * P := by
      linear_combination L3 * hrel
    rw [e]
    have := mul_nonneg (sub_nonneg.mpr h) hP
    linarith

/-- For `Λ₄ = 0` the conditions of Ivanov–Vazão are sufficient for boundedness from below. -/
theorem boundedBelow_of_iv (p : Params) (h4 : p.L4 = 0)
    (hc : S4.IVConditions p.L0 p.L1 p.L2 p.L3) : BoundedBelow p := by
  intro χ₁ χ₂ χ₃
  rw [V4_eq]
  have ha1 := normSq_nonneg χ₁
  have ha2 := normSq_nonneg χ₂
  have ha3 := normSq_nonneg χ₃
  have c12 := normSq_inner_le χ₁ χ₂
  have c23 := normSq_inner_le χ₂ χ₃
  have c31 := normSq_inner_le χ₃ χ₁
  have hgG := fun (τ : ℝ) (hτ : 3 / 4 ≤ τ) => gG_nonneg hτ χ₁ χ₂ χ₃
  generalize normSq χ₁ = a1 at *
  generalize normSq χ₂ = a2 at *
  generalize normSq χ₃ = a3 at *
  generalize inner χ₁ χ₂ = A12 at *
  generalize inner χ₂ χ₃ = A23 at *
  generalize inner χ₃ χ₁ = A31 at *
  have main := suff_core hc
    (N2 := (a1 + a2 + a3) ^ 2)
    (Z := a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - a1 * a2 - a2 * a3 - a3 * a1)
    (P := A12.re ^ 2 + A23.re ^ 2 + A31.re ^ 2)
    (Q := A12.im ^ 2 + A23.im ^ 2 + A31.im ^ 2)
    (E := a1 * a2 + a2 * a3 + a3 * a1
      - Complex.normSq A12 - Complex.normSq A23 - Complex.normSq A31)
    (by nlinarith [sq_nonneg (a1 - a2), sq_nonneg (a2 - a3), sq_nonneg (a3 - a1)])
    (by positivity) (by positivity) (by linarith) (by positivity)
    (by simp only [Complex.normSq_apply]; ring)
    (fun τ hτ => by have := hgG τ hτ; unfold gG at this; linarith)
  unfold V4G
  rw [h4]
  linarith

/-! ## Necessity of the conditions for `Λ₄ = 0` -/

/-- `√3`. -/
noncomputable def r3 : ℝ := √3

lemma r3_sq : r3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- The cube root of unity `ω = e^{2πi/3}`. -/
noncomputable def ω : ℂ := ⟨-1 / 2, r3 / 2⟩

/-- The potential on the family `χ₁ = (ω s, c)`, `χ₂ = (ω* s, c)`, `χ₃ = (s, c)`
(a gauge-equivalent form of "`t`-path 1" of arXiv:2611.05475; it contains the vertices
`B`, `C`, `F` and is tangent to the arc). -/
lemma V4_tfam (p : Params) (s c : ℝ) :
    V4 p ![ω * s, c] ![(starRingEnd ℂ) ω * s, c] ![(s : ℂ), c]
      = 3 * (p.L0 * (s ^ 2 + c ^ 2) ^ 2 + p.L1 * (c ^ 2 - s ^ 2 / 2) ^ 2
          + 3 / 4 * p.L2 * (s ^ 2) ^ 2)
        + p.L4 * (3 * ((c ^ 2 - s ^ 2 / 2) * (r3 / 2 * s ^ 2))) := by
  have n1 : normSq ![ω * s, (c : ℂ)] = s ^ 2 + c ^ 2 := by
    simp [normSq, Fin.sum_univ_two, Complex.normSq_apply, ω]
    linear_combination (s ^ 2 / 4) * r3_sq
  have n2 : normSq ![(starRingEnd ℂ) ω * s, (c : ℂ)] = s ^ 2 + c ^ 2 := by
    simp [normSq, Fin.sum_univ_two, Complex.normSq_apply, ω]
    linear_combination (s ^ 2 / 4) * r3_sq
  have n3 : normSq ![(s : ℂ), (c : ℂ)] = s ^ 2 + c ^ 2 := by
    simp [normSq, Fin.sum_univ_two, Complex.normSq_apply]
    ring
  have i12 : inner ![ω * s, (c : ℂ)] ![(starRingEnd ℂ) ω * s, (c : ℂ)]
      = ⟨c ^ 2 - s ^ 2 / 2, r3 / 2 * s ^ 2⟩ := by
    apply Complex.ext
    · simp [inner, Fin.sum_univ_two, ω]
      linear_combination (-(s ^ 2) / 4) * r3_sq
    · simp [inner, Fin.sum_univ_two, ω]
      ring
  have i23 : inner ![(starRingEnd ℂ) ω * s, (c : ℂ)] ![(s : ℂ), (c : ℂ)]
      = ⟨c ^ 2 - s ^ 2 / 2, r3 / 2 * s ^ 2⟩ := by
    apply Complex.ext
    · simp [inner, Fin.sum_univ_two, ω]
      ring
    · simp [inner, Fin.sum_univ_two, ω]
      ring
  have i31 : inner ![(s : ℂ), (c : ℂ)] ![ω * s, (c : ℂ)]
      = ⟨c ^ 2 - s ^ 2 / 2, r3 / 2 * s ^ 2⟩ := by
    apply Complex.ext
    · simp [inner, Fin.sum_univ_two, ω]
      ring
    · simp [inner, Fin.sum_univ_two, ω]
      ring
  rw [V4_eq, n1, n2, n3, i12, i23, i31]
  unfold V4G
  dsimp only
  linear_combination (3 / 4 * p.L2 * s ^ 4) * r3_sq

/-- The potential on the family `χ₁ = (0, c)`, `χ₂ = (s, 0)`, `χ₃ = (i s, 0)`
("`q`-path" of arXiv:2611.05475 with `α = π/2`). -/
lemma V4_qfam (p : Params) (s c : ℝ) :
    V4 p ![0, (c : ℂ)] ![(s : ℂ), 0] ![Complex.I * s, 0]
      = (p.L0 * (c ^ 2 + 2 * s ^ 2) ^ 2 + p.L3 * (c ^ 2 - s ^ 2) ^ 2
          + 3 * p.L2 * (s ^ 2) ^ 2) / 3 := by
  rw [V4_eq]
  simp [V4G, normSq, inner, Fin.sum_univ_two, Complex.normSq_apply]
  ring

/-- The potential at the vertex `E` (a charge-breaking configuration). -/
lemma V4_E (p : Params) :
    V4 p ![2, 0] ![-1, (r3 : ℂ)] ![-1, -(r3 : ℂ)] = 48 * p.L0 + 12 * p.L1 := by
  have n1 : normSq ![(2 : ℂ), 0] = 4 := by
    simp [normSq, Fin.sum_univ_two, Complex.normSq_apply]
    norm_num
  have n2 : normSq ![(-1 : ℂ), (r3 : ℂ)] = 4 := by
    simp [normSq, Fin.sum_univ_two, Complex.normSq_apply]
    nlinarith [r3_sq]
  have n3 : normSq ![(-1 : ℂ), -(r3 : ℂ)] = 4 := by
    simp [normSq, Fin.sum_univ_two, Complex.normSq_apply]
    nlinarith [r3_sq]
  have i12 : inner ![(2 : ℂ), 0] ![(-1 : ℂ), (r3 : ℂ)] = ⟨-2, 0⟩ := by
    apply Complex.ext <;> simp [inner, Fin.sum_univ_two]
  have i23 : inner ![(-1 : ℂ), (r3 : ℂ)] ![(-1 : ℂ), -(r3 : ℂ)] = ⟨-2, 0⟩ := by
    apply Complex.ext
    · simp [inner, Fin.sum_univ_two]
      nlinarith [r3_sq]
    · simp [inner, Fin.sum_univ_two]
  have i31 : inner ![(-1 : ℂ), -(r3 : ℂ)] ![(2 : ℂ), 0] = ⟨-2, 0⟩ := by
    apply Complex.ext <;> simp [inner, Fin.sum_univ_two]
  rw [V4_eq, n1, n2, n3, i12, i23, i31]
  unfold V4G
  dsimp only
  ring

/-- The potential at the vertex `E'` (the counterpart of `E` with `Λ₁ → Λ₃`). -/
lemma V4_E' (p : Params) :
    V4 p ![0, 1] ![1, 0] 0 = (4 * p.L0 + p.L3) / 3 := by
  rw [V4_eq]
  simp [V4G, normSq, inner, Fin.sum_univ_two]
  ring

/-- For `Λ₄ = 0` the conditions of Ivanov–Vazão are necessary for boundedness from below. -/
theorem iv_of_boundedBelow (p : Params) (h4 : p.L4 = 0) (h : BoundedBelow p) :
    S4.IVConditions p.L0 p.L1 p.L2 p.L3 := by
  have t : ∀ S C : ℝ, 0 ≤ S → 0 ≤ C →
      0 ≤ p.L0 * (S + C) ^ 2 + p.L1 * (C - S / 2) ^ 2 + 3 / 4 * p.L2 * S ^ 2 := by
    intro S C hS hC
    have h1 := h ![ω * (√S : ℝ), ((√C : ℝ) : ℂ)] ![(starRingEnd ℂ) ω * (√S : ℝ), ((√C : ℝ) : ℂ)]
      ![((√S : ℝ) : ℂ), ((√C : ℝ) : ℂ)]
    rw [V4_tfam, h4, Real.sq_sqrt hS, Real.sq_sqrt hC] at h1
    linarith
  have q : ∀ S C : ℝ, 0 ≤ S → 0 ≤ C →
      0 ≤ p.L0 * (C + 2 * S) ^ 2 + p.L3 * (C - S) ^ 2 + 3 * p.L2 * S ^ 2 := by
    intro S C hS hC
    have h1 := h ![0, ((√C : ℝ) : ℂ)] ![((√S : ℝ) : ℂ), 0] ![Complex.I * (√S : ℝ), 0]
    rw [V4_qfam, Real.sq_sqrt hS, Real.sq_sqrt hC] at h1
    linarith
  have hE := h ![2, 0] ![-1, (r3 : ℂ)] ![-1, -(r3 : ℂ)]
  rw [V4_E] at hE
  have hE' := h ![0, 1] ![1, 0] 0
  rw [V4_E'] at hE'
  have tB := t 0 1 le_rfl zero_le_one
  have tC := t 1 0 zero_le_one le_rfl
  have tF := t 1 1 zero_le_one zero_le_one
  have qA := q 0 1 le_rfl zero_le_one
  have qD := q 1 0 zero_le_one le_rfl
  have qF := q 1 2 zero_le_one (by norm_num)
  refine ⟨⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith⟩, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    have habs := abs_lt.mp (show |p.L2| < p.L1 by linarith)
    have hD : 0 < 3 * p.L1 + p.L2 := by linarith
    have h3 := (S4.add_div_neg_iff hD).mp h2
    have tt := t (2 * p.L1) (p.L1 + p.L2) (by linarith) (by linarith)
    nlinarith [mul_pos hD (neg_pos.mpr h3)]
  · rintro ⟨h1, h2⟩
    have habs := abs_lt.mp (show |p.L2| < p.L3 by linarith)
    have hD : 0 < p.L2 + 3 * p.L3 := by linarith
    have h3 := (S4.add_div_neg_iff hD).mp h2
    have qq := q p.L3 (p.L3 + p.L2) (by linarith) (by linarith)
    nlinarith [mul_pos hD (neg_pos.mpr h3)]

/-! ## Main results -/

/-- **Boundedness from below of the `S₄`-symmetric three-Higgs-doublet potential.**
For `Λ₄ = 0`, the quartic part is non-negative on all field configurations if and only if the
conditions of Ivanov–Vazão hold. -/
theorem boundedBelow_iff_iv (p : Params) (h4 : p.L4 = 0) :
    BoundedBelow p ↔ S4.IVConditions p.L0 p.L1 p.L2 p.L3 :=
  ⟨iv_of_boundedBelow p h4, boundedBelow_of_iv p h4⟩

/-- **The conjecture of Lavoura–Milagre holds in the `S₄` case**: for `Λ₄ = 0` their
conditions (arXiv:2611.05475, Section 5) are necessary and sufficient for boundedness from
below. -/
theorem boundedBelow_iff_lm (p : Params) (h4 : p.L4 = 0) :
    BoundedBelow p ↔ S4.LMConditions p.L0 p.L1 p.L2 p.L3 := by
  rw [boundedBelow_iff_iv p h4, S4.lmS4_iff_iv]

/-! ## The general conditions of Lavoura–Milagre at `Λ₄ = 0` -/

section specialisation

variable {L0 L1 L2 L3 L4 : ℝ}

private lemma sqrt_R (a b : ℝ) : √((a - b) ^ 2 + (0 : ℝ) ^ 2) = |a - b| := by
  rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]

private lemma aux_f (h4 : L4 = 0) :
    (0 ≤ L0 + L3 ∧ 0 ≤ L0 + L1 ∧ 0 ≤ L0 + (L1 + 3 * L2 - √3 * |L4|) / 4 ∧
      0 ≤ L0 + L3 / 4 + 3 * (L1 + L2 - √((L1 - L2) ^ 2 + L4 ^ 2)) / 8 ∧ 0 ≤ L0 + L3 / 4) ↔
    (0 ≤ L0 + L3 ∧ 0 ≤ L0 + L1 ∧ 0 ≤ L0 + (L1 + 3 * L2) / 4 ∧
      0 ≤ L0 + L3 / 4 + 3 * min L1 L2 / 4 ∧ 0 ≤ L0 + L3 / 4) := by
  subst h4
  have hmin : 3 * (L1 + L2 - |L1 - L2|) / 8 = 3 * min L1 L2 / 4 := by
    rcases le_total L1 L2 with h | h
    · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
  rw [sqrt_R, abs_zero, mul_zero, sub_zero]
  constructor <;> rintro ⟨a, b, c, d, e⟩ <;> exact ⟨a, b, c, by linarith, e⟩

private lemma aux44 (h4 : L4 = 0) :
    (|L4| - 2 * √3 * L2 < 0 ∧ L0 + (4 * L1 * L2 - L4 ^ 2) / (16 * L2) < 0) ↔
    (0 < L2 ∧ L0 + L1 / 4 < 0) := by
  subst h4
  have hs3 : 0 < √(3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have e : 0 < L2 → (4 * L1 * L2 - (0 : ℝ) ^ 2) / (16 * L2) = L1 / 4 := by
    intro h
    field_simp
    ring
  rw [abs_zero]
  constructor
  · rintro ⟨a, b⟩
    have hL2 : 0 < L2 := by
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_nonneg hs3.le (neg_nonneg.mpr hneg)]
    exact ⟨hL2, by rw [e hL2] at b; exact b⟩
  · rintro ⟨a, b⟩
    exact ⟨by nlinarith [mul_pos hs3 a], by rw [e a]; exact b⟩

private lemma aux45 (h4 : L4 = 0) :
    (|3 * (L2 - L1) - √3 * L4| - 3 * (3 * L1 + L2 - √3 * L4) < 0 ∧
      L0 + (4 * L1 * L2 - L4 ^ 2) / (4 * (3 * L1 + L2 - √3 * L4)) < 0) ↔
    (|L2 - L1| - 3 * L1 - L2 < 0 ∧ L0 + L1 * L2 / (3 * L1 + L2) < 0) := by
  subst h4
  have e1 : |3 * (L2 - L1) - √3 * 0| = 3 * |L2 - L1| := by
    rw [mul_zero, sub_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have e2 : (4 * L1 * L2 - (0 : ℝ) ^ 2) / (4 * (3 * L1 + L2 - √3 * 0))
      = L1 * L2 / (3 * L1 + L2) := by
    rw [mul_zero, sub_zero, zero_pow two_ne_zero, sub_zero, mul_assoc,
      mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]
  rw [e1, e2, mul_zero, sub_zero]
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, b⟩

private lemma aux46 (h4 : L4 = 0) :
    (|3 * (L2 - L1) + √3 * L4| - 3 * (3 * L1 + L2 + √3 * L4) < 0 ∧
      L0 + (4 * L1 * L2 - L4 ^ 2) / (4 * (3 * L1 + L2 + √3 * L4)) < 0) ↔
    (|L2 - L1| - 3 * L1 - L2 < 0 ∧ L0 + L1 * L2 / (3 * L1 + L2) < 0) := by
  subst h4
  have e1 : |3 * (L2 - L1) + √3 * 0| = 3 * |L2 - L1| := by
    rw [mul_zero, add_zero, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
  have e2 : (4 * L1 * L2 - (0 : ℝ) ^ 2) / (4 * (3 * L1 + L2 + √3 * 0))
      = L1 * L2 / (3 * L1 + L2) := by
    rw [mul_zero, add_zero, zero_pow two_ne_zero, sub_zero, mul_assoc,
      mul_div_mul_left _ _ (by norm_num : (4 : ℝ) ≠ 0)]
  rw [e1, e2, mul_zero, add_zero]
  constructor <;> rintro ⟨a, b⟩ <;> exact ⟨by linarith, b⟩

private lemma aux47 (h4 : L4 = 0) :
    (max 0 (2 * L0) - L3 < 0 ∧
      max (-L1 - L2 - 2 * L3) (L1 + L2 + 6 * L0 * L3 / (L0 + L3))
        - √((L1 - L2) ^ 2 + L4 ^ 2) < 0) ↔
    (max 0 (2 * L0) - L3 < 0 ∧
      max (-L1 - L2 - 2 * L3) (L1 + L2 + 6 * L0 * L3 / (L0 + L3)) - |L1 - L2| < 0) := by
  subst h4
  rw [sqrt_R]

/-- For `Λ₄ = 0` the general conditions of Lavoura–Milagre (Section 4) reduce to the ones
they list in Section 5. -/
theorem lm_iff_lmS4 (p : Params) (h4 : p.L4 = 0) :
    LMConditions p ↔ S4.LMConditions p.L0 p.L1 p.L2 p.L3 := by
  unfold LMConditions S4.LMConditions
  rw [aux_f h4, aux44 h4, aux45 h4, aux46 h4, aux47 h4]
  constructor
  · rintro ⟨a, b, c, -, e⟩
    exact ⟨a, b, c, e⟩
  · rintro ⟨a, b, c, e⟩
    exact ⟨a, b, c, c, e⟩

end specialisation

/-- **The conjecture of Lavoura and Milagre is true for `Λ₄ = 0`** (symmetry `S₄`): the
conditions of arXiv:2611.05475, Section 4, are necessary and sufficient for the quartic part of
the potential to be non-negative on all field configurations. -/
theorem lm_conjecture_S4 (p : Params) (h4 : p.L4 = 0) : BoundedBelow p ↔ LMConditions p := by
  rw [boundedBelow_iff_lm p h4, lm_iff_lmS4 p h4]

end BFB.A4
