import Mathlib

/-!
# A binary quadratic form on the boundary of a triangle

Real-algebra lemmas for `BFB/NegL0.lean`.  Let `m(x, y) = a x² + b x y + c y²` and let `r = √3`.
The three linear forms

  `h₀ = x`,  `h₁ = -x/2 + r y/2`,  `h₂ = -x/2 - r y/2`

sum to zero; the triangle `max(h₀, h₁, h₂) ≤ 1/2` has its vertices at the three points
`-1`, `-ω`, `-ω²` of the unit circle.  Conditions (43b), (43c), (44), (45), (46) of
arXiv:2611.05475 say that `m ≥ μ/4` on the boundary of that triangle (`μ = -4Λ₀`): at the
vertices, and at the minimum of `m` on each side if that minimum lies inside the side.
From this we derive that `m ≥ μ h_k²` on the whole plane for `k = 0, 1, 2`
(`tri_all`), and from that the inequalities between the coefficients that are needed
for the duality theorem (`tri_coeff`).
-/

namespace BFB.Tri

/-- A quadratic polynomial on an interval `[-r, r]` is bounded below by `μ` if it is at the two
end points and at its interior minimum, should there be one. -/
lemma quad_on_interval {A B C r μ : ℝ} (hr : 0 < r) (hp : μ ≤ A + B * r + C * r ^ 2)
    (hm : μ ≤ A - B * r + C * r ^ 2) (hint : ¬ (|B| < 2 * C * r ∧ A - B ^ 2 / (4 * C) < μ))
    {s : ℝ} (hs : |s| ≤ r) : μ ≤ A + B * s + C * s ^ 2 := by
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs
  by_cases hB : |B| < 2 * C * r
  · have hCr : 0 < 2 * C * r := lt_of_le_of_lt (abs_nonneg B) hB
    have hC : 0 < C := by
      by_contra hneg
      push_neg at hneg
      nlinarith
    have hval : μ ≤ A - B ^ 2 / (4 * C) := not_lt.mp (fun h => hint ⟨hB, h⟩)
    have e : A + B * s + C * s ^ 2 = C * (s + B / (2 * C)) ^ 2 + (A - B ^ 2 / (4 * C)) := by
      field_simp
      ring
    rw [e]
    nlinarith [mul_nonneg hC.le (sq_nonneg (s + B / (2 * C)))]
  · push_neg at hB
    have hrs : 0 ≤ r ^ 2 - s ^ 2 := by nlinarith
    rcases le_or_gt C 0 with hC | hC
    · -- concave case: compare with the chord
      have h1 := mul_nonneg (by linarith : (0 : ℝ) ≤ r + s) (sub_nonneg.mpr hp)
      have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ r - s) (sub_nonneg.mpr hm)
      have h3 := mul_nonneg (mul_nonneg (neg_nonneg.mpr hC) hr.le) hrs
      have h4 : 0 ≤ r * (A + B * s + C * s ^ 2 - μ) := by nlinarith
      have := nonneg_of_mul_nonneg_right h4 hr
      linarith
    · -- convex case, minimum outside the interval: monotone on the interval
      rcases le_abs.mp hB with h | h
      · have h1 : 0 ≤ B + C * (s - r) := by nlinarith [mul_nonneg hC.le (by linarith : (0:ℝ) ≤ s + r)]
        have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ s + r) h1
        nlinarith
      · have h1 : 0 ≤ -B - C * (s + r) := by nlinarith [mul_nonneg hC.le (by linarith : (0:ℝ) ≤ r - s)]
        have h2 := mul_nonneg (by linarith : (0 : ℝ) ≤ r - s) h1
        nlinarith

/-- Homogeneous form of `quad_on_interval`: a binary quadratic form on the sector
`|y| ≤ r x`. -/
lemma sector {A B C r μ : ℝ} (hr : 0 < r) (hp : μ ≤ A + B * r + C * r ^ 2)
    (hm : μ ≤ A - B * r + C * r ^ 2) (hint : ¬ (|B| < 2 * C * r ∧ A - B ^ 2 / (4 * C) < μ))
    {x y : ℝ} (hy : |y| ≤ r * x) : μ * x ^ 2 ≤ A * x ^ 2 + B * x * y + C * y ^ 2 := by
  have hx0 : 0 ≤ x := by
    have := le_trans (abs_nonneg y) hy
    exact nonneg_of_mul_nonneg_right this hr
  rcases hx0.eq_or_lt with hx | hx
  · have hy0 : y = 0 := by
      rw [← hx, mul_zero] at hy
      exact abs_nonpos_iff.mp hy
    rw [← hx, hy0]
    simp
  · have hs : |y / x| ≤ r := by
      rw [abs_div, abs_of_pos hx, div_le_iff₀ hx]
      exact hy
    have h := quad_on_interval hr hp hm hint hs
    have e : A + B * (y / x) + C * (y / x) ^ 2 = (A * x ^ 2 + B * x * y + C * y ^ 2) / x ^ 2 := by
      field_simp
    rw [e, le_div_iff₀ (by positivity)] at h
    exact h

section triangle

variable {a b c μ r : ℝ}

/-- For every point of the plane there is a height `H ≥ max(h₀, h₁, h₂)`, `H ≥ 0`, with
`μ H² ≤ m`. -/
lemma tri_max (hr0 : 0 < r) (hr : r ^ 2 = 3)
    (hV1 : μ ≤ 4 * a) (hV2 : μ ≤ a + 3 * c + r * b) (hV3 : μ ≤ a + 3 * c - r * b)
    (hP0 : ¬ (|b| < 2 * c * r ∧ a - b ^ 2 / (4 * c) < μ))
    (hP1 : ¬ (|-(r / 2) * (c - a) - b / 2| < 2 * ((3 * a + c + r * b) / 4) * r ∧
      (a + 3 * c - r * b) / 4
        - (-(r / 2) * (c - a) - b / 2) ^ 2 / (4 * ((3 * a + c + r * b) / 4)) < μ))
    (hP2 : ¬ (|r / 2 * (c - a) - b / 2| < 2 * ((3 * a + c - r * b) / 4) * r ∧
      (a + 3 * c + r * b) / 4
        - (r / 2 * (c - a) - b / 2) ^ 2 / (4 * ((3 * a + c - r * b) / 4)) < μ))
    (x y : ℝ) :
    ∃ H : ℝ, 0 ≤ H ∧ x ≤ H ∧ -x / 2 + r * y / 2 ≤ H ∧ -x / 2 - r * y / 2 ≤ H ∧
      μ * H ^ 2 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  -- the three sectors
  have s0 : |y| ≤ r * x → μ * x ^ 2 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
    intro hy
    have e1 : a + b * r + c * r ^ 2 = a + 3 * c + r * b := by linear_combination c * hr
    have e2 : a - b * r + c * r ^ 2 = a + 3 * c - r * b := by linear_combination c * hr
    exact sector hr0 (by rw [e1]; exact hV2) (by rw [e2]; exact hV3) hP0 hy
  have s1 : |-(r / 2) * x - y / 2| ≤ r * (-x / 2 + r * y / 2) →
      μ * (-x / 2 + r * y / 2) ^ 2 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
    intro hy
    have e1 : (a + 3 * c - r * b) / 4 + (-(r / 2) * (c - a) - b / 2) * r
        + (3 * a + c + r * b) / 4 * r ^ 2 = 4 * a := by
      linear_combination (5 * a / 4 + b * r / 4 - c / 4) * hr
    have e2 : (a + 3 * c - r * b) / 4 - (-(r / 2) * (c - a) - b / 2) * r
        + (3 * a + c + r * b) / 4 * r ^ 2 = a + 3 * c + r * b := by
      linear_combination (a / 4 + b * r / 4 + 3 * c / 4) * hr
    have h := sector (A := (a + 3 * c - r * b) / 4) (B := -(r / 2) * (c - a) - b / 2)
      (C := (3 * a + c + r * b) / 4) hr0 (by rw [e1]; exact hV1) (by rw [e2]; exact hV2) hP1 hy
    have e : (a + 3 * c - r * b) / 4 * (-x / 2 + r * y / 2) ^ 2
        + (-(r / 2) * (c - a) - b / 2) * (-x / 2 + r * y / 2) * (-(r / 2) * x - y / 2)
        + (3 * a + c + r * b) / 4 * (-(r / 2) * x - y / 2) ^ 2
        = a * x ^ 2 + b * x * y + c * y ^ 2 := by
      linear_combination ((-2 * a * r * x * y + 5 * a * x ^ 2 - a * y ^ 2 + b * r * x ^ 2
        - b * r * y ^ 2 + 6 * b * x * y + 2 * c * r * x * y - c * x ^ 2 + 5 * c * y ^ 2) / 16) * hr
    rw [e] at h
    exact h
  have s2 : |r / 2 * x - y / 2| ≤ r * (-x / 2 - r * y / 2) →
      μ * (-x / 2 - r * y / 2) ^ 2 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
    intro hy
    have e1 : (a + 3 * c + r * b) / 4 + (r / 2 * (c - a) - b / 2) * r
        + (3 * a + c - r * b) / 4 * r ^ 2 = a + 3 * c - r * b := by
      linear_combination (a / 4 - b * r / 4 + 3 * c / 4) * hr
    have e2 : (a + 3 * c + r * b) / 4 - (r / 2 * (c - a) - b / 2) * r
        + (3 * a + c - r * b) / 4 * r ^ 2 = 4 * a := by
      linear_combination (5 * a / 4 - b * r / 4 - c / 4) * hr
    have h := sector (A := (a + 3 * c + r * b) / 4) (B := r / 2 * (c - a) - b / 2)
      (C := (3 * a + c - r * b) / 4) hr0 (by rw [e1]; exact hV3) (by rw [e2]; exact hV1) hP2 hy
    have e : (a + 3 * c + r * b) / 4 * (-x / 2 - r * y / 2) ^ 2
        + (r / 2 * (c - a) - b / 2) * (-x / 2 - r * y / 2) * (r / 2 * x - y / 2)
        + (3 * a + c - r * b) / 4 * (r / 2 * x - y / 2) ^ 2
        = a * x ^ 2 + b * x * y + c * y ^ 2 := by
      linear_combination (-(-2 * a * r * x * y - 5 * a * x ^ 2 + a * y ^ 2 + b * r * x ^ 2
        - b * r * y ^ 2 - 6 * b * x * y + 2 * c * r * x * y + c * x ^ 2 - 5 * c * y ^ 2) / 16) * hr
    rw [e] at h
    exact h
  -- which of the three heights is the largest?
  by_cases c0 : -x / 2 + r * y / 2 ≤ x ∧ -x / 2 - r * y / 2 ≤ x
  · refine ⟨x, by linarith [c0.1, c0.2], le_rfl, c0.1, c0.2, s0 ?_⟩
    rw [abs_le]
    constructor <;> nlinarith [c0.1, c0.2]
  · by_cases c1 : -x / 2 - r * y / 2 ≤ -x / 2 + r * y / 2
    · have hx : x ≤ -x / 2 + r * y / 2 := by
        by_contra hneg
        push_neg at hneg
        exact c0 ⟨hneg.le, by linarith⟩
      refine ⟨-x / 2 + r * y / 2, by linarith, hx, le_rfl, c1, s1 ?_⟩
      rw [abs_le]
      constructor <;> nlinarith
    · push_neg at c1
      have hx : x ≤ -x / 2 - r * y / 2 := by
        by_contra hneg
        push_neg at hneg
        exact c0 ⟨by linarith, hneg.le⟩
      refine ⟨-x / 2 - r * y / 2, by linarith, hx, c1.le, le_rfl, s2 ?_⟩
      rw [abs_le]
      constructor <;> nlinarith

private lemma sq_le_aux {h H H' m μ : ℝ} (hμ : 0 ≤ μ) (hH : 0 ≤ H) (hH' : 0 ≤ H') (h1 : h ≤ H)
    (h2 : -h ≤ H') (m1 : μ * H ^ 2 ≤ m) (m2 : μ * H' ^ 2 ≤ m) : μ * h ^ 2 ≤ m := by
  rcases le_total 0 h with hh | hh
  · have : h ^ 2 ≤ H ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hμ]
  · have : h ^ 2 ≤ H' ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hμ]

/-- On the whole plane, `m ≥ μ h_k²` for each of the three heights. -/
lemma tri_all (hr0 : 0 < r) (hr : r ^ 2 = 3) (hμ : 0 ≤ μ)
    (hV1 : μ ≤ 4 * a) (hV2 : μ ≤ a + 3 * c + r * b) (hV3 : μ ≤ a + 3 * c - r * b)
    (hP0 : ¬ (|b| < 2 * c * r ∧ a - b ^ 2 / (4 * c) < μ))
    (hP1 : ¬ (|-(r / 2) * (c - a) - b / 2| < 2 * ((3 * a + c + r * b) / 4) * r ∧
      (a + 3 * c - r * b) / 4
        - (-(r / 2) * (c - a) - b / 2) ^ 2 / (4 * ((3 * a + c + r * b) / 4)) < μ))
    (hP2 : ¬ (|r / 2 * (c - a) - b / 2| < 2 * ((3 * a + c - r * b) / 4) * r ∧
      (a + 3 * c + r * b) / 4
        - (r / 2 * (c - a) - b / 2) ^ 2 / (4 * ((3 * a + c - r * b) / 4)) < μ))
    (x y : ℝ) :
    μ * x ^ 2 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 ∧
    μ * (-x / 2 + r * y / 2) ^ 2 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 ∧
    μ * (-x / 2 - r * y / 2) ^ 2 ≤ a * x ^ 2 + b * x * y + c * y ^ 2 := by
  obtain ⟨H, hH, h0, h1, h2, hm⟩ := tri_max hr0 hr hV1 hV2 hV3 hP0 hP1 hP2 x y
  obtain ⟨H', hH', g0, g1, g2, gm⟩ := tri_max hr0 hr hV1 hV2 hV3 hP0 hP1 hP2 (-x) (-y)
  have e : a * (-x) ^ 2 + b * (-x) * (-y) + c * (-y) ^ 2 = a * x ^ 2 + b * x * y + c * y ^ 2 := by
    ring
  rw [e] at gm
  exact ⟨sq_le_aux hμ hH hH' h0 g0 hm gm,
    sq_le_aux hμ hH hH' h1 (by linarith) hm gm,
    sq_le_aux hμ hH hH' h2 (by linarith) hm gm⟩

/-- The inequalities between the coefficients that follow from `tri_all`. -/
lemma tri_coeff (hr0 : 0 < r) (hr : r ^ 2 = 3) (hμ : 0 < μ)
    (hV1 : μ ≤ 4 * a) (hV2 : μ ≤ a + 3 * c + r * b) (hV3 : μ ≤ a + 3 * c - r * b)
    (hP0 : ¬ (|b| < 2 * c * r ∧ a - b ^ 2 / (4 * c) < μ))
    (hP1 : ¬ (|-(r / 2) * (c - a) - b / 2| < 2 * ((3 * a + c + r * b) / 4) * r ∧
      (a + 3 * c - r * b) / 4
        - (-(r / 2) * (c - a) - b / 2) ^ 2 / (4 * ((3 * a + c + r * b) / 4)) < μ))
    (hP2 : ¬ (|r / 2 * (c - a) - b / 2| < 2 * ((3 * a + c - r * b) / 4) * r ∧
      (a + 3 * c + r * b) / 4
        - (r / 2 * (c - a) - b / 2) ^ 2 / (4 * ((3 * a + c - r * b) / 4)) < μ)) :
    0 < a ∧ 0 < c ∧ 4 * μ * c ≤ 4 * a * c - b ^ 2 ∧
      μ * (3 * a + c + r * b) ≤ 4 * a * c - b ^ 2 ∧
      μ * (3 * a + c - r * b) ≤ 4 * a * c - b ^ 2 := by
  have all := tri_all hr0 hr hμ.le hV1 hV2 hV3 hP0 hP1 hP2
  -- `a > 0`
  have ha : 0 < a := by
    have := (all 1 0).1
    nlinarith
  -- `c > 0`
  have hc : 0 < c := by
    have := (all 0 1).2.1
    nlinarith
  -- the minimum on the line `h₀ = const`
  have t0 : 4 * μ * c ≤ 4 * a * c - b ^ 2 := by
    have h := (all (2 * c) (-b)).1
    have e : a * (2 * c) ^ 2 + b * (2 * c) * (-b) + c * (-b) ^ 2 = c * (4 * a * c - b ^ 2) := by
      ring
    rw [e] at h
    have h' : c * (4 * μ * c) ≤ c * (4 * a * c - b ^ 2) := by nlinarith
    exact le_of_mul_le_mul_left h' hc
  -- the minimum on the line `h₁ = const`
  have τ1 : 0 < (3 * a + c + r * b) / 4 := by
    have h := (all (-(r / 2)) (-(1 / 2))).1
    nlinarith
  have t1 : μ * (3 * a + c + r * b) ≤ 4 * a * c - b ^ 2 := by
    have h := (all (-c / 2 - r * b / 4) (b / 4 + r * a / 2)).2.1
    have e1 : -(-c / 2 - r * b / 4) / 2 + r * (b / 4 + r * a / 2) / 2
        = (3 * a + c + r * b) / 4 := by
      linear_combination (a / 4) * hr
    have e2 : a * (-c / 2 - r * b / 4) ^ 2 + b * (-c / 2 - r * b / 4) * (b / 4 + r * a / 2)
        + c * (b / 4 + r * a / 2) ^ 2
        = (a * c - b ^ 2 / 4) * ((3 * a + c + r * b) / 4) := by
      linear_combination ((4 * a * c - b ^ 2) * a / 16) * hr
    rw [e1, e2] at h
    have h' : (3 * a + c + r * b) / 4 * (μ * ((3 * a + c + r * b) / 4))
        ≤ (3 * a + c + r * b) / 4 * (a * c - b ^ 2 / 4) := by nlinarith
    have := le_of_mul_le_mul_left h' τ1
    linarith
  -- the minimum on the line `h₂ = const`
  have τ2 : 0 < (3 * a + c - r * b) / 4 := by
    have h := (all (r / 2) (-(1 / 2))).1
    nlinarith
  have t2 : μ * (3 * a + c - r * b) ≤ 4 * a * c - b ^ 2 := by
    have h := (all (-c / 2 + r * b / 4) (b / 4 - r * a / 2)).2.2
    have e1 : -(-c / 2 + r * b / 4) / 2 - r * (b / 4 - r * a / 2) / 2
        = (3 * a + c - r * b) / 4 := by
      linear_combination (a / 4) * hr
    have e2 : a * (-c / 2 + r * b / 4) ^ 2 + b * (-c / 2 + r * b / 4) * (b / 4 - r * a / 2)
        + c * (b / 4 - r * a / 2) ^ 2
        = (a * c - b ^ 2 / 4) * ((3 * a + c - r * b) / 4) := by
      linear_combination ((4 * a * c - b ^ 2) * a / 16) * hr
    rw [e1, e2] at h
    have h' : (3 * a + c - r * b) / 4 * (μ * ((3 * a + c - r * b) / 4))
        ≤ (3 * a + c - r * b) / 4 * (a * c - b ^ 2 / 4) := by nlinarith
    have := le_of_mul_le_mul_left h' τ2
    linarith
  exact ⟨ha, hc, t0, t1, t2⟩

end triangle

end BFB.Tri
