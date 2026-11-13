import BFB.Defs

/-!
# `S₄`-symmetric three-Higgs-doublet model: two forms of the boundedness conditions agree

L. Lavoura, A. Milagre, "Complete set of bounded-from-below conditions for the `A₄`-symmetric
three-Higgs-doublet model", arXiv:2611.05475, derive necessary conditions for the quartic part of
the `A₄`-symmetric potential to be non-negative and conjecture that they are also sufficient.
In their Section 5 they specialise the conditions to `Λ₄ = 0` (symmetry `S₄`) and compare them
with the necessary and sufficient conditions of

I. P. Ivanov, F. Vazão, "Yet another lesson on the stability conditions in multi-Higgs
potentials", JHEP 11 (2020) 104, arXiv:2006.00036 (final list at the end of Section 4.2),

stating: "We have numerically checked that the two methods for guaranteeing BnessFB are in
practice equivalent."

This file proves that the two sets of conditions are *exactly* equivalent, for all real values
of the four couplings (`lmS4_iff_iv`).  It is a statement about real inequalities only; the
potential itself does not enter.
-/

namespace BFB.S4

/-- Clearing a positive denominator. -/
lemma add_div_neg_iff {a n d : ℝ} (hd : 0 < d) : a + n / d < 0 ↔ a * d + n < 0 := by
  have h : a + n / d = (a * d + n) / d := by field_simp
  rw [h, div_neg_iff]
  constructor
  · rintro (⟨_, h2⟩ | ⟨h1, _⟩)
    · exact absurd hd (not_lt.mpr h2.le)
    · exact h1
  · intro h1
    exact Or.inr ⟨h1, hd⟩

theorem lm_imp_iv {a b c d : ℝ} (h : LMConditions a b c d) : IVConditions a b c d := by
  obtain ⟨⟨f1, f2, f3, f4, f5⟩, n1, n2, n3⟩ := h
  have hminc : min b c ≤ c := min_le_right _ _
  have hminb : min b c ≤ b := min_le_left _ _
  -- point E
  have i5 : 0 ≤ a + b / 4 := by
    by_contra hneg
    push_neg at hneg
    have hc : ¬ 0 < c := fun hc => n1 ⟨hc, hneg⟩
    push_neg at hc
    linarith
  -- point F
  have i7 : 0 ≤ a + (b + 3 * c) / 16 := by
    rcases le_or_gt 0 a with ha | ha
    · linarith
    · have hb : 0 < b := by linarith
      have hbc : 0 < b + c := by
        rcases le_or_gt 0 c with hc | hc <;> linarith
      have hd : 0 < 3 * b + c := by linarith
      have habs : |c - b| - 3 * b - c < 0 := by
        have : |c - b| < 3 * b + c := abs_lt.mpr ⟨by linarith, by linarith⟩
        linarith
      have key : 0 ≤ a * (3 * b + c) + b * c := by
        by_contra hk
        push_neg at hk
        exact n2 ⟨habs, (add_div_neg_iff hd).mpr hk⟩
      by_contra hneg
      push_neg at hneg
      have h16 : 16 * a + b + 3 * c < 0 := by linarith
      nlinarith [sq_nonneg (b - c), mul_pos hd (neg_pos.mpr h16)]
  -- the situation `Λ₃ > max (0, 2Λ₀)`: what the q-path condition gives
  have q : max 0 (2 * a) < d → -d < c → 0 ≤ c * (a + d) + 3 * a * d := by
    intro hd hc
    have hd0 : 0 < d := lt_of_le_of_lt (le_max_left _ _) hd
    have had : 0 < a + d := by
      rcases le_or_gt 0 a with ha | ha <;> linarith
    have h3 : ¬ (max (-b - c - 2 * d) (b + c + 6 * a * d / (a + d)) - |b - c| < 0) :=
      fun h3 => n3 ⟨by linarith, h3⟩
    push_neg at h3
    have h4 : |b - c| ≤ max (-b - c - 2 * d) (b + c + 6 * a * d / (a + d)) := by linarith
    rcases le_max_iff.mp h4 with h5 | h5
    · -- impossible: it would give `max b c ≤ -d`
      have : c - b ≤ |b - c| := by rw [abs_sub_comm]; exact le_abs_self _
      linarith
    · have h6 : b - c ≤ |b - c| := le_abs_self _
      have h7 : 0 ≤ 2 * c + 6 * a * d / (a + d) := by linarith
      have h8 : 2 * c + 6 * a * d / (a + d) = (2 * (c * (a + d) + 3 * a * d)) / (a + d) := by
        field_simp
        ring
      rw [h8] at h7
      have h9 := (div_nonneg_iff.mp h7)
      rcases h9 with ⟨h9, _⟩ | ⟨_, h9⟩
      · linarith
      · linarith
  -- counterpart of point F
  have i8 : 0 ≤ a + (d + 3 * c) / 16 := by
    rcases le_or_gt 0 a with ha | ha
    · linarith
    · have hd0 : 0 < d := by linarith
      have had : 0 < a + d := by linarith
      have hmax : max 0 (2 * a) < d := by
        rw [max_eq_left (by linarith)]; exact hd0
      rcases le_or_gt c (-d) with hc | hc
      · -- then `min b c ≤ c ≤ -d`, contradicting (f4) together with `a < 0`... use (f4)
        linarith
      · have key := q hmax hc
        by_contra hneg
        push_neg at hneg
        have h16 : 16 * a + d + 3 * c < 0 := by linarith
        nlinarith [sq_nonneg (4 * a + d), mul_pos had (neg_pos.mpr h16)]
  refine ⟨⟨f2, f1, f3, by linarith, i5, f5, i7, i8⟩, ?_, ?_⟩
  · -- arc condition in `Λ₁`
    rintro ⟨h1, h2⟩
    have hb : 0 < b := lt_of_le_of_lt (abs_nonneg c) (by linarith)
    have hc := abs_lt.mp (show |c| < b by linarith)
    refine n2 ⟨?_, h2⟩
    have : |c - b| < 3 * b + c := abs_lt.mpr ⟨by linarith [hc.1], by linarith [hc.1]⟩
    linarith
  · -- arc condition in `Λ₃`
    rintro ⟨h1, h2⟩
    have hd0 : 0 < d := lt_of_le_of_lt (abs_nonneg c) (by linarith)
    have hc := abs_lt.mp (show |c| < d by linarith)
    have hden : 0 < c + 3 * d := by linarith [hc.1]
    have h3 : a * (c + 3 * d) + c * d < 0 := (add_div_neg_iff hden).mp h2
    rcases lt_or_ge (max 0 (2 * a)) d with hmax | hmax
    · have key := q hmax hc.1
      nlinarith
    · have h2a : d ≤ 2 * a := by
        rcases le_max_iff.mp hmax with h | h
        · linarith
        · exact h
      nlinarith [mul_nonneg hd0.le (sub_nonneg.mpr h2a), mul_pos hd0 (show 0 < c + d by linarith [hc.1]),
        mul_nonneg (show (0:ℝ) ≤ a by linarith) hd0.le]

theorem iv_imp_lm {a b c d : ℝ} (h : IVConditions a b c d) : LMConditions a b c d := by
  obtain ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8⟩, m1, m2⟩ := h
  refine ⟨⟨i2, i1, i3, ?_, i6⟩, ?_, ?_, ?_⟩
  · rcases le_total b c with hbc | hbc
    · rw [min_eq_left hbc]; linarith
    · rw [min_eq_right hbc]; linarith
  · rintro ⟨_, h2⟩
    linarith
  · rintro ⟨h1, h2⟩
    have habs := abs_lt.mp (show |c - b| < 3 * b + c by linarith)
    have hb : 0 < b := by linarith [habs.1]
    have hbc : 0 < b + c := by linarith [habs.2]
    have hden : 0 < 3 * b + c := by linarith
    have h3 : a * (3 * b + c) + b * c < 0 := (add_div_neg_iff hden).mp h2
    rcases lt_or_ge c b with hcb | hcb
    · exact m1 ⟨by
        have : |c| < b := abs_lt.mpr ⟨by linarith, hcb⟩
        linarith, h2⟩
    · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hcb), mul_nonneg (show (0:ℝ) ≤ 4 * a + b by linarith) hden.le]
  · rintro ⟨h1, h2⟩
    have hmax : max 0 (2 * a) < d := by linarith
    have hd0 : 0 < d := lt_of_le_of_lt (le_max_left _ _) hmax
    have h2a : 2 * a < d := lt_of_le_of_lt (le_max_right _ _) hmax
    have had : 0 < a + d := by
      rcases le_or_gt 0 a with ha | ha <;> linarith
    have h3 : max (-b - c - 2 * d) (b + c + 6 * a * d / (a + d)) < |b - c| := by linarith
    have h4 : b + c + 6 * a * d / (a + d) < |b - c| := lt_of_le_of_lt (le_max_right _ _) h3
    have h5 : -b - c - 2 * d < |b - c| := lt_of_le_of_lt (le_max_left _ _) h3
    -- clear the denominator
    have h6 : ∀ m : ℝ, 2 * m + 6 * a * d / (a + d) < 0 → m * (a + d) + 3 * a * d < 0 := by
      intro m hm
      have h8 : 2 * m + 6 * a * d / (a + d) = (2 * (m * (a + d) + 3 * a * d)) / (a + d) := by
        field_simp
        ring
      rw [h8, div_neg_iff] at hm
      rcases hm with ⟨_, hm⟩ | ⟨hm, _⟩
      · linarith
      · linarith
    rcases le_total b c with hbc | hbc
    · -- `min = Λ₁`
      have habs : |b - c| = c - b := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
      have h7 := h6 b (by rw [habs] at h4; linarith)
      rcases le_or_gt 0 a with ha | ha
      · nlinarith [mul_nonneg ha (show (0:ℝ) ≤ 2 * d - a by linarith), mul_nonneg (show (0:ℝ) ≤ a + b by linarith) had.le]
      · nlinarith [mul_nonneg (show (0:ℝ) ≤ -a by linarith) (show (0:ℝ) ≤ 4 * a + d by linarith),
          mul_nonneg (show (0:ℝ) ≤ 4 * a + b by linarith) had.le]
    · -- `min = Λ₂`
      have habs : |b - c| = b - c := abs_of_nonneg (by linarith)
      have h7 := h6 c (by rw [habs] at h4; linarith)
      rw [habs] at h5
      rcases lt_or_ge |c| d with hcd | hcd
      · have hc := abs_lt.mp hcd
        have hden : 0 < c + 3 * d := by linarith [hc.1]
        exact m2 ⟨by linarith, (add_div_neg_iff hden).mpr (by nlinarith)⟩
      · rcases le_or_gt 0 c with hc | hc
        · rw [abs_of_nonneg hc] at hcd
          nlinarith [mul_nonneg hd0.le (show (0:ℝ) ≤ 4 * a + d by linarith), mul_nonneg (sub_nonneg.mpr hcd) had.le]
        · rw [abs_of_neg hc] at hcd
          linarith

/-- **The two sets of boundedness-from-below conditions for the `S₄`-symmetric
three-Higgs-doublet model are equivalent**: the conditions of Lavoura–Milagre (arXiv:2611.05475,
Section 5) hold if and only if the necessary and sufficient conditions of Ivanov–Vazão
(JHEP 11 (2020) 104) hold. -/
theorem lmS4_iff_iv (L0 L1 L2 L3 : ℝ) : LMConditions L0 L1 L2 L3 ↔ IVConditions L0 L1 L2 L3 :=
  ⟨lm_imp_iv, iv_imp_lm⟩

end BFB.S4
