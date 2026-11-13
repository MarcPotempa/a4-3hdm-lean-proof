import BFB.Duality
import BFB.Triangle

/-!
# The conditions of Lavoura–Milagre are sufficient for `Λ₀ < 0`, given the neutral theorem

`NeutralConditions` are the inequalities (43a)–(43d) of arXiv:2611.05475.  By the theorem of
Buskin and Ivanov (J. Phys. A 54 (2021) 325401) they are necessary and sufficient for the
potential to be non-negative on the neutral configurations; that theorem is *not* formalized
here.  It enters as a hypothesis (`BFB/Neutral.lean`).

This file proves the algebraic link: if `Λ₀ < 0` and the conditions (43)–(47) of
Lavoura–Milagre hold, then `Λ₃ > 0`, the matrix `[[Λ₁, Λ₄/2], [Λ₄/2, Λ₂]]` is positive definite
and the dual couplings satisfy `NeutralConditions` (`lm_dual_neutralConditions`).
With the duality theorem this gives `boundedBelow_of_lm_of_neg`.
-/

namespace BFB.A4

/-- The inequalities (43a)–(43d) of arXiv:2611.05475: the conditions that are necessary and
sufficient for non-negativity on neutral configurations (Buskin–Ivanov). -/
def NeutralConditions (p : Params) : Prop :=
  0 ≤ p.L0 + p.L3 ∧ 0 ≤ p.L0 + p.L1 ∧ 0 ≤ p.L0 + (p.L1 + 3 * p.L2 - √3 * |p.L4|) / 4 ∧
    0 ≤ p.L0 + p.L3 / 4 + 3 * (p.L1 + p.L2 - √((p.L1 - p.L2) ^ 2 + p.L4 ^ 2)) / 8

section link

variable {L0 L1 L2 L3 L4 : ℝ}

private lemma r3pos : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)

private lemma r3sq : (√3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)

/-- (44) gives the interior condition on the side `h₀ = 1/2`. -/
private lemma side0 (h44 : ¬ (|L4| - 2 * √3 * L2 < 0 ∧
    L0 + (4 * L1 * L2 - L4 ^ 2) / (16 * L2) < 0)) :
    ¬ (|L4| < 2 * L2 * √3 ∧ L1 - L4 ^ 2 / (4 * L2) < -4 * L0) := by
  rintro ⟨h1, h2⟩
  have hL2 : 0 < L2 := by
    have := lt_of_le_of_lt (abs_nonneg L4) h1
    by_contra hneg
    push_neg at hneg
    nlinarith [r3pos]
  refine h44 ⟨by linarith, ?_⟩
  have e : (4 * L1 * L2 - L4 ^ 2) / (16 * L2) = (L1 - L4 ^ 2 / (4 * L2)) / 4 := by
    field_simp
    ring
  rw [e]
  linarith

/-- (46) gives the interior condition on the side `h₁ = 1/2`. -/
private lemma side1 (h46 : ¬ (|3 * (L2 - L1) + √3 * L4| - 3 * (3 * L1 + L2 + √3 * L4) < 0 ∧
    L0 + (4 * L1 * L2 - L4 ^ 2) / (4 * (3 * L1 + L2 + √3 * L4)) < 0)) :
    ¬ (|-(√3 / 2) * (L2 - L1) - L4 / 2| < 2 * ((3 * L1 + L2 + √3 * L4) / 4) * √3 ∧
      (L1 + 3 * L2 - √3 * L4) / 4
        - (-(√3 / 2) * (L2 - L1) - L4 / 2) ^ 2 / (4 * ((3 * L1 + L2 + √3 * L4) / 4)) < -4 * L0) := by
  rintro ⟨h1, h2⟩
  have hC : 0 < 3 * L1 + L2 + √3 * L4 := by
    have := lt_of_le_of_lt (abs_nonneg _) h1
    by_contra hneg
    push_neg at hneg
    nlinarith [r3pos]
  refine h46 ⟨?_, ?_⟩
  · have e : 3 * (L2 - L1) + √3 * L4 = -(2 * √3) * (-(√3 / 2) * (L2 - L1) - L4 / 2) := by
      linear_combination (-(L2 - L1)) * r3sq
    rw [e, abs_mul, abs_neg, abs_of_pos (by linarith [r3pos] : (0 : ℝ) < 2 * √3)]
    have := mul_lt_mul_of_pos_left h1 (by linarith [r3pos] : (0 : ℝ) < 2 * √3)
    have e2 : 2 * √3 * (2 * ((3 * L1 + L2 + √3 * L4) / 4) * √3)
        = 3 * (3 * L1 + L2 + √3 * L4) := by
      linear_combination (3 * L1 + L2 + √3 * L4) * r3sq
    linarith
  · have hC' : 3 * L1 + L2 + √3 * L4 ≠ 0 := hC.ne'
    have hid : (L1 + 3 * L2 - √3 * L4) / 4 * (3 * L1 + L2 + √3 * L4)
        - (-(√3 / 2) * (L2 - L1) - L4 / 2) ^ 2 = 4 * L1 * L2 - L4 ^ 2 := by
      linear_combination (-(L1 ^ 2 - 2 * L1 * L2 + L2 ^ 2 + L4 ^ 2) / 4) * r3sq
    have e1 : (L1 + 3 * L2 - √3 * L4) / 4
        - (-(√3 / 2) * (L2 - L1) - L4 / 2) ^ 2 / (4 * ((3 * L1 + L2 + √3 * L4) / 4))
        = ((L1 + 3 * L2 - √3 * L4) / 4 * (3 * L1 + L2 + √3 * L4)
          - (-(√3 / 2) * (L2 - L1) - L4 / 2) ^ 2) / (3 * L1 + L2 + √3 * L4) := by
      rw [eq_div_iff hC', sub_mul, show (4 : ℝ) * ((3 * L1 + L2 + √3 * L4) / 4) = 3 * L1 + L2 + √3 * L4 by ring,
        div_mul_cancel₀ _ hC']
    rw [e1, hid] at h2
    have e2 : (4 * L1 * L2 - L4 ^ 2) / (4 * (3 * L1 + L2 + √3 * L4))
        = (4 * L1 * L2 - L4 ^ 2) / (3 * L1 + L2 + √3 * L4) / 4 := by
      field_simp
    rw [e2]
    linarith

/-- (45) gives the interior condition on the side `h₂ = 1/2`. -/
private lemma side2 (h45 : ¬ (|3 * (L2 - L1) - √3 * L4| - 3 * (3 * L1 + L2 - √3 * L4) < 0 ∧
    L0 + (4 * L1 * L2 - L4 ^ 2) / (4 * (3 * L1 + L2 - √3 * L4)) < 0)) :
    ¬ (|√3 / 2 * (L2 - L1) - L4 / 2| < 2 * ((3 * L1 + L2 - √3 * L4) / 4) * √3 ∧
      (L1 + 3 * L2 + √3 * L4) / 4
        - (√3 / 2 * (L2 - L1) - L4 / 2) ^ 2 / (4 * ((3 * L1 + L2 - √3 * L4) / 4)) < -4 * L0) := by
  rintro ⟨h1, h2⟩
  have hC : 0 < 3 * L1 + L2 - √3 * L4 := by
    have := lt_of_le_of_lt (abs_nonneg _) h1
    by_contra hneg
    push_neg at hneg
    nlinarith [r3pos]
  refine h45 ⟨?_, ?_⟩
  · have e : 3 * (L2 - L1) - √3 * L4 = (2 * √3) * (√3 / 2 * (L2 - L1) - L4 / 2) := by
      linear_combination (-(L2 - L1)) * r3sq
    rw [e, abs_mul, abs_of_pos (by linarith [r3pos] : (0 : ℝ) < 2 * √3)]
    have := mul_lt_mul_of_pos_left h1 (by linarith [r3pos] : (0 : ℝ) < 2 * √3)
    have e2 : 2 * √3 * (2 * ((3 * L1 + L2 - √3 * L4) / 4) * √3)
        = 3 * (3 * L1 + L2 - √3 * L4) := by
      linear_combination (3 * L1 + L2 - √3 * L4) * r3sq
    linarith
  · have hC' : 3 * L1 + L2 - √3 * L4 ≠ 0 := hC.ne'
    have hid : (L1 + 3 * L2 + √3 * L4) / 4 * (3 * L1 + L2 - √3 * L4)
        - (√3 / 2 * (L2 - L1) - L4 / 2) ^ 2 = 4 * L1 * L2 - L4 ^ 2 := by
      linear_combination (-(L1 ^ 2 - 2 * L1 * L2 + L2 ^ 2 + L4 ^ 2) / 4) * r3sq
    have e1 : (L1 + 3 * L2 + √3 * L4) / 4
        - (√3 / 2 * (L2 - L1) - L4 / 2) ^ 2 / (4 * ((3 * L1 + L2 - √3 * L4) / 4))
        = ((L1 + 3 * L2 + √3 * L4) / 4 * (3 * L1 + L2 - √3 * L4)
          - (√3 / 2 * (L2 - L1) - L4 / 2) ^ 2) / (3 * L1 + L2 - √3 * L4) := by
      rw [eq_div_iff hC', sub_mul, show (4 : ℝ) * ((3 * L1 + L2 - √3 * L4) / 4) = 3 * L1 + L2 - √3 * L4 by ring,
        div_mul_cancel₀ _ hC']
    rw [e1, hid] at h2
    have e2 : (4 * L1 * L2 - L4 ^ 2) / (4 * (3 * L1 + L2 - √3 * L4))
        = (4 * L1 * L2 - L4 ^ 2) / (3 * L1 + L2 - √3 * L4) / 4 := by
      field_simp
    rw [e2]
    linarith

/-! ### The four neutral conditions for the dual couplings -/

private lemma dual_a (h0 : L0 < 0) (h3 : 0 < L3) (f5 : 0 ≤ L0 + L3 / 4) :
    0 ≤ -1 / L0 + -4 / L3 := by
  have hl : 0 < -L0 := by linarith
  have e0 : -1 / L0 = 1 / (-L0) := by rw [div_neg, neg_div]
  have : 4 / L3 ≤ 1 / (-L0) := by
    rw [div_le_div_iff₀ h3 hl]
    linarith
  rw [e0, neg_div]
  linarith

private lemma dual_b {δ : ℝ} (h0 : L0 < 0) (hδ : 0 < δ) (t0 : 4 * (-L0) * L2 ≤ δ) :
    0 ≤ -1 / L0 + -4 * L2 / δ := by
  have hl : 0 < -L0 := by linarith
  have e0 : -1 / L0 = 1 / (-L0) := by rw [div_neg, neg_div]
  have : 4 * L2 / δ ≤ 1 / (-L0) := by
    rw [div_le_div_iff₀ hδ hl]
    linarith
  rw [e0, neg_mul, neg_div]
  linarith

private lemma dual_c {δ : ℝ} (h0 : L0 < 0) (hδ : 0 < δ)
    (t1 : (-L0) * (3 * L1 + L2 + √3 * L4) ≤ δ) (t2 : (-L0) * (3 * L1 + L2 - √3 * L4) ≤ δ) :
    0 ≤ -1 / L0 + (-4 * L2 / δ + 3 * (-4 * L1 / δ) - √3 * |4 * L4 / δ|) / 4 := by
  have hl : 0 < -L0 := by linarith
  have e0 : -1 / L0 = 1 / (-L0) := by rw [div_neg, neg_div]
  have habs : |4 * L4 / δ| = 4 * |L4| / δ := by
    rw [abs_div, abs_mul, abs_of_pos hδ, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have e : (-4 * L2 / δ + 3 * (-4 * L1 / δ) - √3 * (4 * |L4| / δ)) / 4
      = -((3 * L1 + L2 + √3 * |L4|) / δ) := by
    field_simp
    ring
  have key : (3 * L1 + L2 + √3 * |L4|) / δ ≤ 1 / (-L0) := by
    rw [div_le_div_iff₀ hδ hl]
    rcases abs_cases L4 with ⟨hab, -⟩ | ⟨hab, -⟩ <;> rw [hab] <;> linarith
  rw [habs, e, e0]
  linarith

private lemma sqrt_dual {δ : ℝ} (hδ : 0 < δ) :
    √((-4 * L2 / δ - -4 * L1 / δ) ^ 2 + (4 * L4 / δ) ^ 2)
      = 4 / δ * √((L1 - L2) ^ 2 + L4 ^ 2) := by
  have e : (-4 * L2 / δ - -4 * L1 / δ) ^ 2 + (4 * L4 / δ) ^ 2
      = (4 / δ) ^ 2 * ((L1 - L2) ^ 2 + L4 ^ 2) := by
    field_simp
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

private lemma dual_d_core {S R δ : ℝ} (h0 : L0 < 0) (h3 : 0 < L3) (hs : 0 < S - R)
    (ht : 0 < S + R) (hδ : δ = (S - R) * (S + R) / 4)
    (hkey : 6 * (-L0) * L3 ≤ (S - R) * (L3 - (-L0))) :
    0 ≤ -1 / L0 + -4 / L3 / 4 + 3 * (-4 * S / δ - 4 / δ * R) / 8 := by
  subst hδ
  have hL0 : L0 ≠ 0 := ne_of_lt h0
  have hL3 : L3 ≠ 0 := h3.ne'
  have hs' : S - R ≠ 0 := hs.ne'
  have ht' : S + R ≠ 0 := ht.ne'
  have e : -1 / L0 + -4 / L3 / 4 + 3 * (-4 * S / ((S - R) * (S + R) / 4)
      - 4 / ((S - R) * (S + R) / 4) * R) / 8
      = ((S - R) * (L3 - (-L0)) - 6 * (-L0) * L3) / ((-L0) * L3 * (S - R)) := by
    field_simp
    ring
  rw [e]
  have hl : 0 < -L0 := by linarith
  exact div_nonneg (by linarith) (by positivity)

private lemma dual_d {δ : ℝ} (h0 : L0 < 0) (h3 : 0 < L3) (f5 : 0 ≤ L0 + L3 / 4)
    (h1 : 0 < L1) (h2 : 0 < L2) (hδ : 0 < δ) (hδdef : δ = L1 * L2 - L4 ^ 2 / 4)
    (h47 : ¬ (max 0 (2 * L0) - L3 < 0 ∧
      max (-L1 - L2 - 2 * L3) (L1 + L2 + 6 * L0 * L3 / (L0 + L3))
        - √((L1 - L2) ^ 2 + L4 ^ 2) < 0)) :
    0 ≤ -1 / L0 + -4 / L3 / 4
      + 3 * (-4 * L2 / δ + -4 * L1 / δ
        - √((-4 * L2 / δ - -4 * L1 / δ) ^ 2 + (4 * L4 / δ) ^ 2)) / 8 := by
  rw [sqrt_dual hδ]
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = √((L1 - L2) ^ 2 + L4 ^ 2) := ⟨_, rfl⟩
  rw [← hRdef] at h47 ⊢
  have hR0 : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
  have hR2 : R ^ 2 = (L1 - L2) ^ 2 + L4 ^ 2 := by
    rw [hRdef]; exact Real.sq_sqrt (by positivity)
  have hsum : 0 < L0 + L3 := by linarith
  have h47' : ¬ (max (-L1 - L2 - 2 * L3) (L1 + L2 + 6 * L0 * L3 / (L0 + L3)) - R < 0) :=
    fun hh => h47 ⟨by
      have : max 0 (2 * L0) = 0 := max_eq_left (by linarith)
      rw [this]; linarith, hh⟩
  push_neg at h47'
  have hle : R ≤ max (-L1 - L2 - 2 * L3) (L1 + L2 + 6 * L0 * L3 / (L0 + L3)) := by linarith
  have hkey : 6 * (-L0) * L3 ≤ (L1 + L2 - R) * (L3 - (-L0)) := by
    rcases le_max_iff.mp hle with h | h
    · linarith
    · have h' : R - (L1 + L2) ≤ 6 * L0 * L3 / (L0 + L3) := by linarith
      rw [le_div_iff₀ hsum] at h'
      linarith
  have hst : (L1 + L2 - R) * (L1 + L2 + R) = 4 * δ := by
    rw [hδdef]
    linear_combination -hR2
  have ht : 0 < L1 + L2 + R := by linarith
  have hs : 0 < L1 + L2 - R := by
    have : 0 < (L1 + L2 - R) * (L1 + L2 + R) := by rw [hst]; linarith
    exact pos_of_mul_pos_left this ht.le
  have core := dual_d_core (S := L1 + L2) (R := R) (δ := δ) h0 h3 hs ht (by linarith) hkey
  have e : -4 * L2 / δ + -4 * L1 / δ - 4 / δ * R = -4 * (L1 + L2) / δ - 4 / δ * R := by ring
  rw [e]
  exact core

end link

/-- **Algebraic link.**  If `Λ₀ < 0` and the conditions (43)–(47) of Lavoura–Milagre hold,
then `Λ₃ > 0`, `Λ₁ > 0`, `Λ₁ Λ₂ - Λ₄²/4 > 0`, and the dual couplings satisfy the neutral
conditions (43a)–(43d). -/
theorem lm_dual_neutralConditions (p : Params) (h0 : p.L0 < 0) (h : LMConditions p) :
    0 < p.L3 ∧ 0 < p.L1 ∧ 0 < p.L1 * p.L2 - p.L4 ^ 2 / 4 ∧ NeutralConditions (dual p) := by
  obtain ⟨⟨f1, f2, f3, -, f5⟩, h44, h45, h46, h47⟩ := h
  have hr0 := r3pos
  have hμ : 0 < -4 * p.L0 := by linarith
  have habs1 : √3 * p.L4 ≤ √3 * |p.L4| := mul_le_mul_of_nonneg_left (le_abs_self _) hr0.le
  have habs2 : -(√3 * p.L4) ≤ √3 * |p.L4| := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le p.L4) hr0.le
    linarith
  obtain ⟨ha, hc, t0, t1, t2⟩ := Tri.tri_coeff (a := p.L1) (b := p.L4) (c := p.L2)
    (μ := -4 * p.L0) hr0 r3sq hμ (by linarith) (by linarith) (by linarith)
    (side0 h44) (side1 h46) (side2 h45)
  have h3 : 0 < p.L3 := by linarith
  have hδ : 0 < p.L1 * p.L2 - p.L4 ^ 2 / 4 := by nlinarith
  exact ⟨h3, ha, hδ, dual_a h0 h3 f5, dual_b h0 hδ (by linarith),
    dual_c h0 hδ (by linarith) (by linarith), dual_d h0 h3 f5 ha hc hδ rfl h47⟩

/-- For `Λ₀ < 0`, the conditions of Lavoura–Milagre imply boundedness from below, provided the
neutral conditions (43a)–(43d) are sufficient on neutral configurations. -/
theorem boundedBelow_of_lm_of_neg (hN : ∀ q : Params, NeutralConditions q → NeutralBoundedBelow q)
    (p : Params) (h0 : p.L0 < 0) (h : LMConditions p) : BoundedBelow p := by
  obtain ⟨h3, h1, hδ, hq⟩ := lm_dual_neutralConditions p h0 h
  exact boundedBelow_of_dual_neutral p h0 h3 h1 hδ (hN _ hq)

end BFB.A4
