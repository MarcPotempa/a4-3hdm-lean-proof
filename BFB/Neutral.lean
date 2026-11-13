import BFB.NegL0

/-!
# The neutral theorem of Buskin and Ivanov as a hypothesis

N. Buskin, I. P. Ivanov, "Bounded-from-below conditions for `A₄`-symmetric 3HDM",
J. Phys. A 54 (2021) 325401, arXiv:2104.11428, Theorem 1:

  the potential `V₄ = a (z̄₁z₁ + z̄₂z₂ + z̄₃z₃) + 2b (|z₁z₂| + |z₂z₃| + |z₃z₁|)`
  `   + d (z̄₁z₂ + z̄₂z₃ + z̄₃z₁) + d̄ (z̄₂z₁ + z̄₃z₂ + z̄₁z₃)`   (their Eq. (1); `a, b` real,
  `d = |d| e^{iγ}` complex) is non-negative on all of `ℂ³` if and only if

  `a ≥ 0`, `a + b - |d| ≥ 0`   (their Eq. (3)) and
  `a + 2b + 2|d| cos(γ + 2πk/3) ≥ 0` for `k = 1, 2, 3`   (their Eq. (4)).

**This theorem is not formalized here.**  `BuskinIvanovTheorem` states its "if" direction, and
the results below are conditional on it.  This file only translates the statement into the
notation of arXiv:2611.05475: with `z_k = v_k²`, their potential is the `A₄` potential on the
neutral configuration `χ_k = (v_k, 0)`, and their conditions are (43a)–(43d).
-/

namespace BFB.A4

/-- The parameters of Buskin–Ivanov that correspond to the couplings `Λ₀, …, Λ₄`. -/
noncomputable def biD (p : Params) : ℂ := ⟨(p.L1 - p.L2) / 4, -p.L4 / 4⟩

private lemma norm_sq_mul_sq (u w : ℂ) : ‖u ^ 2 * w ^ 2‖ = Complex.normSq u * Complex.normSq w := by
  rw [norm_mul, norm_pow, norm_pow, Complex.sq_norm, Complex.sq_norm]

/-- On neutral configurations the `A₄` potential is the potential of Buskin–Ivanov in the
variables `z_k = v_k²`. -/
lemma V4_neutral_eq (p : Params) (v₁ v₂ v₃ : ℂ) :
    V4 p ![v₁, 0] ![v₂, 0] ![v₃, 0]
      = BIPotential ((p.L0 + p.L3) / 3) ((2 * p.L0 - p.L3) / 6 + (p.L1 + p.L2) / 4) (biD p)
          (v₁ ^ 2) (v₂ ^ 2) (v₃ ^ 2) := by
  unfold V4 BIPotential biD
  rw [norm_sq_mul_sq, norm_sq_mul_sq, norm_sq_mul_sq]
  simp only [normSq, inner, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_zero, mul_zero, add_zero, Complex.normSq_apply, pow_two, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, map_mul,
    Complex.zero_re, Complex.zero_im]
  ring

private lemma norm_biD (p : Params) : ‖biD p‖ = √((p.L1 - p.L2) ^ 2 + p.L4 ^ 2) / 4 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  have e : (biD p).re ^ 2 + (biD p).im ^ 2
      = (1 / 4) ^ 2 * ((p.L1 - p.L2) ^ 2 + p.L4 ^ 2) := by
    simp only [biD]
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num)]
  ring

private lemma norm_cos (d : ℂ) (θ : ℝ) :
    ‖d‖ * Real.cos (Complex.arg d + θ) = d.re * Real.cos θ - d.im * Real.sin θ := by
  rw [Real.cos_add, ← Complex.norm_mul_cos_arg d, ← Complex.norm_mul_sin_arg d]
  ring

private lemma cos_two_pi_div_three : Real.cos (2 * Real.pi / 3) = -1 / 2 := by
  have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]
  ring

private lemma sin_two_pi_div_three : Real.sin (2 * Real.pi / 3) = √3 / 2 := by
  have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
  rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]

private lemma cos_four_pi_div_three : Real.cos (4 * Real.pi / 3) = -1 / 2 := by
  have : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
  rw [this, Real.cos_add_pi, Real.cos_pi_div_three]
  ring

private lemma sin_four_pi_div_three : Real.sin (4 * Real.pi / 3) = -(√3 / 2) := by
  have : 4 * Real.pi / 3 = Real.pi / 3 + Real.pi := by ring
  rw [this, Real.sin_add_pi, Real.sin_pi_div_three]

/-- The neutral conditions (43a)–(43d) are the conditions of Buskin–Ivanov. -/
lemma biConditions_of_neutralConditions (p : Params) (h : NeutralConditions p) :
    BIConditions ((p.L0 + p.L3) / 3) ((2 * p.L0 - p.L3) / 6 + (p.L1 + p.L2) / 4) (biD p) := by
  obtain ⟨f1, f2, f3, f4⟩ := h
  have hr0 : (0 : ℝ) < √3 := Real.sqrt_pos.mpr (by norm_num)
  have habs1 : √3 * p.L4 ≤ √3 * |p.L4| := mul_le_mul_of_nonneg_left (le_abs_self _) hr0.le
  have habs2 : -(√3 * p.L4) ≤ √3 * |p.L4| := by
    have := mul_le_mul_of_nonneg_left (neg_abs_le p.L4) hr0.le
    linarith
  refine ⟨by linarith, ?_, ?_⟩
  · rw [norm_biD]
    linarith
  · intro k hk
    have e : ∀ θ : ℝ, 2 * ‖biD p‖ * Real.cos (Complex.arg (biD p) + θ)
        = 2 * ((p.L1 - p.L2) / 4 * Real.cos θ - -p.L4 / 4 * Real.sin θ) := by
      intro θ
      rw [mul_assoc, norm_cos]
      rfl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · have : 2 * Real.pi * ((1 : ℕ) : ℝ) / 3 = 2 * Real.pi / 3 := by norm_num
      rw [this, add_assoc, e, cos_two_pi_div_three, sin_two_pi_div_three]
      linarith
    · have : 2 * Real.pi * ((2 : ℕ) : ℝ) / 3 = 4 * Real.pi / 3 := by push_cast; ring
      rw [this, add_assoc, e, cos_four_pi_div_three, sin_four_pi_div_three]
      linarith
    · have : 2 * Real.pi * ((3 : ℕ) : ℝ) / 3 = 2 * Real.pi := by push_cast; ring
      rw [this, add_assoc, e, Real.cos_two_pi, Real.sin_two_pi]
      linarith

/-- Given the theorem of Buskin–Ivanov, the neutral conditions (43a)–(43d) imply
non-negativity on all neutral configurations. -/
theorem neutralBoundedBelow_of_BI (hBI : BuskinIvanovTheorem) (p : Params)
    (h : NeutralConditions p) : NeutralBoundedBelow p := by
  intro v₁ v₂ v₃
  rw [V4_neutral_eq]
  exact hBI _ _ _ (biConditions_of_neutralConditions p h) _ _ _

/-- **The conjecture of Lavoura and Milagre for `Λ₀ < 0`, sufficiency, conditional on the
neutral theorem of Buskin–Ivanov.**  If `Λ₀ < 0` and the conditions of arXiv:2611.05475,
Section 4, hold, then the quartic part of the potential is non-negative on all field
configurations.  (That the conditions are necessary is shown in arXiv:2611.05475.) -/
theorem lm_sufficient_of_L0_neg (hBI : BuskinIvanovTheorem) (p : Params) (h0 : p.L0 < 0)
    (h : LMConditions p) : BoundedBelow p :=
  boundedBelow_of_lm_of_neg (neutralBoundedBelow_of_BI hBI) p h0 h

end BFB.A4
