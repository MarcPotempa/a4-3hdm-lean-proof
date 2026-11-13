import BFB.S4ThreeHDM

/-!
# A duality for the `A₄`-symmetric three-Higgs-doublet potential with `Λ₀ < 0`

For `Λ₀ < 0`, `Λ₃ > 0` and a positive definite matrix `[[Λ₁, Λ₄/2], [Λ₄/2, Λ₂]]`, the quartic part
`V₄` is non-negative on *all* field configurations as soon as the potential with the "dual"
couplings

  `Λ₀' = -1/Λ₀`,  `Λ₃' = -4/Λ₃`,  `[[Λ₁', Λ₄'/2], [Λ₄'/2, Λ₂']] = -4 [[Λ₁, Λ₄/2], [Λ₄/2, Λ₂]]⁻¹`

is non-negative on the *neutral* configurations `χ_k = (v_k, 0)` (`boundedBelow_of_dual_neutral`).

Idea of the proof.  Three doublets are linearly dependent: there is `v ≠ 0` in `ℂ³` with
`v₁ χ₁ + v₂ χ₂ + v₃ χ₃ = 0`.  Taking the norm gives a linear relation between the Gram data
`A_kl = χ_k† χ_l` whose coefficients are the Gram data of the neutral configuration `v`.
The Cauchy–Schwarz inequality, applied separately to the diagonal part and to the three
off-diagonal entries with the weights `Λ₃` and `[[Λ₁, Λ₄/2], [Λ₄/2, Λ₂]]`, turns the relation
into `Λ₃ Z + 3 Σ m(A_kl) ≥ -Λ₀ N²`, which is `V₄ ≥ 0`.
-/

namespace BFB.A4

/-! ## Real-algebra core -/

/-- Cauchy–Schwarz for two pairs. -/
lemma cs_add {B1 B2 D1 D2 Q1 Q2 : ℝ} (hD1 : 0 ≤ D1) (hD2 : 0 ≤ D2) (hQ1 : 0 ≤ Q1)
    (hQ2 : 0 ≤ Q2) (h1 : B1 ^ 2 ≤ D1 * Q1) (h2 : B2 ^ 2 ≤ D2 * Q2) :
    (B1 + B2) ^ 2 ≤ (D1 + D2) * (Q1 + Q2) := by
  have hrhs : 0 ≤ D1 * Q2 + D2 * Q1 := by positivity
  have hsq : (2 * B1 * B2) ^ 2 ≤ (D1 * Q2 + D2 * Q1) ^ 2 := by
    have h12 : B1 ^ 2 * B2 ^ 2 ≤ (D1 * Q1) * (D2 * Q2) :=
      mul_le_mul h1 h2 (sq_nonneg _) (by positivity)
    nlinarith [sq_nonneg (D1 * Q2 - D2 * Q1)]
  have h := abs_le_of_sq_le_sq' hsq hrhs
  nlinarith [h.2]

/-- The quadratic form `m(c) = Λ₁ (Re c)² + Λ₂ (Im c)² + Λ₄ Re c Im c`. -/
def mform (L1 L2 L4 cr ci : ℝ) : ℝ := L1 * cr ^ 2 + L2 * ci ^ 2 + L4 * cr * ci

/-- `δ` times the dual quadratic form, evaluated at the conjugate:
`Λ₂ (Re w)² + Λ₁ (Im w)² + Λ₄ Re w Im w`. -/
def mstar (L1 L2 L4 wr wi : ℝ) : ℝ := L2 * wr ^ 2 + L1 * wi ^ 2 + L4 * wr * wi

lemma mform_nonneg {L1 L2 L4 : ℝ} (h1 : 0 < L1) (hδ : 0 < L1 * L2 - L4 ^ 2 / 4) (cr ci : ℝ) :
    0 ≤ mform L1 L2 L4 cr ci := by
  have h : L1 * mform L1 L2 L4 cr ci
      = (L1 * cr + L4 * ci / 2) ^ 2 + (L1 * L2 - L4 ^ 2 / 4) * ci ^ 2 := by
    unfold mform; ring
  have h2 : 0 ≤ L1 * mform L1 L2 L4 cr ci := by rw [h]; positivity
  exact nonneg_of_mul_nonneg_right h2 h1

lemma mstar_nonneg {L1 L2 L4 : ℝ} (h1 : 0 < L1) (hδ : 0 < L1 * L2 - L4 ^ 2 / 4) (wr wi : ℝ) :
    0 ≤ mstar L1 L2 L4 wr wi := by
  have h : L1 * mstar L1 L2 L4 wr wi
      = (L1 * wi + L4 * wr / 2) ^ 2 + (L1 * L2 - L4 ^ 2 / 4) * wr ^ 2 := by
    unfold mstar; ring
  have h2 : 0 ≤ L1 * mstar L1 L2 L4 wr wi := by rw [h]; positivity
  exact nonneg_of_mul_nonneg_right h2 h1

/-- Cauchy–Schwarz for one off-diagonal entry: `Re(w c)² ≤ m*(w) m(c) / δ`. -/
lemma cs_offdiag {L1 L2 L4 : ℝ} (hδ : 0 < L1 * L2 - L4 ^ 2 / 4) (wr wi cr ci : ℝ) :
    (2 * (wr * cr - wi * ci)) ^ 2
      ≤ (4 / 3 * mstar L1 L2 L4 wr wi / (L1 * L2 - L4 ^ 2 / 4)) * (3 * mform L1 L2 L4 cr ci) := by
  have key : (L1 * L2 - L4 ^ 2 / 4) * (wr * cr - wi * ci) ^ 2
      ≤ mstar L1 L2 L4 wr wi * mform L1 L2 L4 cr ci := by
    have h : mstar L1 L2 L4 wr wi * mform L1 L2 L4 cr ci
        - (L1 * L2 - L4 ^ 2 / 4) * (wr * cr - wi * ci) ^ 2
        = ((L1 * cr + L4 * ci / 2) * wi + (L4 * cr / 2 + L2 * ci) * wr) ^ 2 := by
      unfold mstar mform; ring
    nlinarith [sq_nonneg ((L1 * cr + L4 * ci / 2) * wi + (L4 * cr / 2 + L2 * ci) * wr)]
  have e : (4 / 3 * mstar L1 L2 L4 wr wi / (L1 * L2 - L4 ^ 2 / 4)) * (3 * mform L1 L2 L4 cr ci)
      = 4 * (mstar L1 L2 L4 wr wi * mform L1 L2 L4 cr ci) / (L1 * L2 - L4 ^ 2 / 4) := by
    field_simp
  rw [e, le_div_iff₀ hδ]
  nlinarith [key]

/-- Cauchy–Schwarz for the diagonal part. -/
lemma cs_diag {L3 : ℝ} (h3 : 0 < L3) (p1 p2 p3 a1 a2 a3 : ℝ) :
    (p1 * a1 + p2 * a2 + p3 * a3 - (p1 + p2 + p3) * (a1 + a2 + a3) / 3) ^ 2
      ≤ (4 * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 - p1 * p2 - p2 * p3 - p3 * p1) / (9 * L3))
        * (L3 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - a1 * a2 - a2 * a3 - a3 * a1)) := by
  have e : (4 * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 - p1 * p2 - p2 * p3 - p3 * p1) / (9 * L3))
        * (L3 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - a1 * a2 - a2 * a3 - a3 * a1))
      = 4 * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 - p1 * p2 - p2 * p3 - p3 * p1)
        * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - a1 * a2 - a2 * a3 - a3 * a1) / 9 := by
    field_simp
  rw [e, le_div_iff₀ (by norm_num)]
  nlinarith [sq_nonneg (-a1 * p2 + a1 * p3 + a2 * p1 - a2 * p3 - a3 * p1 + a3 * p2)]

/-- Final step of the duality argument. -/
lemma dual_final {L0 n N D Q : ℝ} (h0 : L0 < 0) (hn : 0 < n) (hQ : 0 ≤ Q)
    (hH : n ^ 2 / (3 * L0) + 3 * D ≤ 0) (h5 : (n * N / 3) ^ 2 ≤ D * Q) : 0 ≤ L0 * N ^ 2 + Q := by
  have hL0 : 0 ≤ 9 * (-L0) := by linarith
  have ht : n ^ 2 / (3 * L0) * (3 * L0) = n ^ 2 := div_mul_cancel₀ _ (by linarith)
  have hDle : 9 * (-L0) * D ≤ n ^ 2 := by
    have := mul_nonneg_of_nonpos_of_nonpos hH (by linarith : 3 * L0 ≤ 0)
    linarith
  have a1 : 9 * (-L0) * D * Q ≤ n ^ 2 * Q := mul_le_mul_of_nonneg_right hDle hQ
  have a2 : 9 * (-L0) * ((n * N / 3) ^ 2) ≤ 9 * (-L0) * (D * Q) :=
    mul_le_mul_of_nonneg_left h5 hL0
  have e : 9 * (-L0) * ((n * N / 3) ^ 2) = n ^ 2 * ((-L0) * N ^ 2) := by ring
  have e' : 9 * (-L0) * (D * Q) = 9 * (-L0) * D * Q := by ring
  have h6 : n ^ 2 * ((-L0) * N ^ 2) ≤ n ^ 2 * Q := by linarith
  have h7 : (-L0) * N ^ 2 ≤ Q := le_of_mul_le_mul_left h6 (by positivity)
  linarith

/-- The real-algebra core of the duality: a linear relation between the Gram data of the three
doublets (`a_k`, `c_k`) with coefficients (`p_k`, `w_k`) for which the dual form is small enough
forces `3 V₄ ≥ 0`. -/
lemma dual_core {L0 L1 L2 L3 L4 : ℝ} (h0 : L0 < 0) (h3 : 0 < L3) (h1 : 0 < L1)
    (hδ : 0 < L1 * L2 - L4 ^ 2 / 4)
    (p1 p2 p3 a1 a2 a3 w1r w1i w2r w2i w3r w3i c1r c1i c2r c2i c3r c3i : ℝ)
    (hn : 0 < p1 + p2 + p3)
    (hrel : p1 * a1 + p2 * a2 + p3 * a3
      + 2 * ((w1r * c1r - w1i * c1i) + (w2r * c2r - w2i * c2i) + (w3r * c3r - w3i * c3i)) = 0)
    (hH : (p1 + p2 + p3) ^ 2 / (3 * L0)
      + 4 * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 - p1 * p2 - p2 * p3 - p3 * p1) / (3 * L3)
      + 4 / (L1 * L2 - L4 ^ 2 / 4)
        * (mstar L1 L2 L4 w1r w1i + mstar L1 L2 L4 w2r w2i + mstar L1 L2 L4 w3r w3i) ≤ 0) :
    0 ≤ L0 * (a1 + a2 + a3) ^ 2 + L3 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - a1 * a2 - a2 * a3 - a3 * a1)
      + 3 * (mform L1 L2 L4 c1r c1i + mform L1 L2 L4 c2r c2i + mform L1 L2 L4 c3r c3i) := by
  have hζ : 0 ≤ p1 ^ 2 + p2 ^ 2 + p3 ^ 2 - p1 * p2 - p2 * p3 - p3 * p1 := by
    nlinarith [sq_nonneg (p1 - p2), sq_nonneg (p2 - p3), sq_nonneg (p3 - p1)]
  have hZ : 0 ≤ a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - a1 * a2 - a2 * a3 - a3 * a1 := by
    nlinarith [sq_nonneg (a1 - a2), sq_nonneg (a2 - a3), sq_nonneg (a3 - a1)]
  have hs1 := mstar_nonneg h1 hδ w1r w1i
  have hs2 := mstar_nonneg h1 hδ w2r w2i
  have hs3 := mstar_nonneg h1 hδ w3r w3i
  have hm1 := mform_nonneg h1 hδ c1r c1i
  have hm2 := mform_nonneg h1 hδ c2r c2i
  have hm3 := mform_nonneg h1 hδ c3r c3i
  -- the four Cauchy–Schwarz inequalities and their sum
  have hD0 : 0 ≤ 4 * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 - p1 * p2 - p2 * p3 - p3 * p1) / (9 * L3) :=
    div_nonneg (by linarith) (by linarith)
  have hQ0 : 0 ≤ L3 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 - a1 * a2 - a2 * a3 - a3 * a1) :=
    mul_nonneg h3.le hZ
  have hD : ∀ {x : ℝ}, 0 ≤ x → 0 ≤ 4 / 3 * x / (L1 * L2 - L4 ^ 2 / 4) :=
    fun hx => div_nonneg (by linarith) hδ.le
  have hQ : ∀ {x : ℝ}, 0 ≤ x → 0 ≤ 3 * x := fun hx => by linarith
  have s01 := cs_add hD0 (hD hs1) hQ0 (hQ hm1) (cs_diag h3 p1 p2 p3 a1 a2 a3)
    (cs_offdiag hδ w1r w1i c1r c1i)
  have s012 := cs_add (add_nonneg hD0 (hD hs1)) (hD hs2) (add_nonneg hQ0 (hQ hm1)) (hQ hm2) s01
    (cs_offdiag hδ w2r w2i c2r c2i)
  have s0123 := cs_add (add_nonneg (add_nonneg hD0 (hD hs1)) (hD hs2)) (hD hs3)
    (add_nonneg (add_nonneg hQ0 (hQ hm1)) (hQ hm2)) (hQ hm3) s012 (cs_offdiag hδ w3r w3i c3r c3i)
  -- the sum of the four pairings is `-n N / 3`
  have hsum : (p1 * a1 + p2 * a2 + p3 * a3 - (p1 + p2 + p3) * (a1 + a2 + a3) / 3)
      + 2 * (w1r * c1r - w1i * c1i) + 2 * (w2r * c2r - w2i * c2i) + 2 * (w3r * c3r - w3i * c3i)
      = -((p1 + p2 + p3) * (a1 + a2 + a3) / 3) := by
    linarith only [hrel]
  rw [hsum, neg_sq] at s0123
  have hH' : (p1 + p2 + p3) ^ 2 / (3 * L0)
      + 3 * (4 * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 - p1 * p2 - p2 * p3 - p3 * p1) / (9 * L3)
        + 4 / 3 * mstar L1 L2 L4 w1r w1i / (L1 * L2 - L4 ^ 2 / 4)
        + 4 / 3 * mstar L1 L2 L4 w2r w2i / (L1 * L2 - L4 ^ 2 / 4)
        + 4 / 3 * mstar L1 L2 L4 w3r w3i / (L1 * L2 - L4 ^ 2 / 4)) ≤ 0 := by
    have e : 3 * (4 * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 - p1 * p2 - p2 * p3 - p3 * p1) / (9 * L3)
        + 4 / 3 * mstar L1 L2 L4 w1r w1i / (L1 * L2 - L4 ^ 2 / 4)
        + 4 / 3 * mstar L1 L2 L4 w2r w2i / (L1 * L2 - L4 ^ 2 / 4)
        + 4 / 3 * mstar L1 L2 L4 w3r w3i / (L1 * L2 - L4 ^ 2 / 4))
        = 4 * (p1 ^ 2 + p2 ^ 2 + p3 ^ 2 - p1 * p2 - p2 * p3 - p3 * p1) / (3 * L3)
          + 4 / (L1 * L2 - L4 ^ 2 / 4)
            * (mstar L1 L2 L4 w1r w1i + mstar L1 L2 L4 w2r w2i + mstar L1 L2 L4 w3r w3i) := by
      have hL3 : L3 ≠ 0 := h3.ne'
      have hδ' : L1 * L2 - L4 ^ 2 / 4 ≠ 0 := hδ.ne'
      field_simp
      ring
    rw [e]
    linarith only [hH]
  have fin := dual_final h0 hn
    (add_nonneg (add_nonneg (add_nonneg hQ0 (hQ hm1)) (hQ hm2)) (hQ hm3)) hH' s0123
  linarith only [fin]

/-! ## From doublets to the core -/

/-- Three doublets are linearly dependent. -/
lemma exists_null (χ₁ χ₂ χ₃ : Fin 2 → ℂ) :
    ∃ v₁ v₂ v₃ : ℂ, 0 < Complex.normSq v₁ + Complex.normSq v₂ + Complex.normSq v₃ ∧
      v₁ * χ₁ 0 + v₂ * χ₂ 0 + v₃ * χ₃ 0 = 0 ∧ v₁ * χ₁ 1 + v₂ * χ₂ 1 + v₃ * χ₃ 1 = 0 := by
  let M : Matrix (Fin 2) (Fin 3) ℂ := !![χ₁ 0, χ₂ 0, χ₃ 0; χ₁ 1, χ₂ 1, χ₃ 1]
  have hker : LinearMap.ker (Matrix.mulVecLin M) ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hMv : M.mulVec v = 0 := by simpa using hv
  have e1 := congrFun hMv 0
  have e2 := congrFun hMv 1
  simp [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e1 e2
  refine ⟨v 0, v 1, v 2, ?_, ?_, ?_⟩
  · by_contra hneg
    push_neg at hneg
    have n0 := Complex.normSq_nonneg (v 0)
    have n1 := Complex.normSq_nonneg (v 1)
    have n2 := Complex.normSq_nonneg (v 2)
    have z0 : v 0 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    have z1 : v 1 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    have z2 : v 2 = 0 := Complex.normSq_eq_zero.mp (by linarith)
    apply hv0
    funext i
    fin_cases i <;> simp [z0, z1, z2]
  · linear_combination e1
  · linear_combination e2

/-- The norm of a linear combination of three doublets in terms of the Gram data. -/
lemma normSq_comb (χ₁ χ₂ χ₃ : Fin 2 → ℂ) (v₁ v₂ v₃ : ℂ) :
    Complex.normSq (v₁ * χ₁ 0 + v₂ * χ₂ 0 + v₃ * χ₃ 0)
      + Complex.normSq (v₁ * χ₁ 1 + v₂ * χ₂ 1 + v₃ * χ₃ 1)
    = Complex.normSq v₁ * normSq χ₁ + Complex.normSq v₂ * normSq χ₂
      + Complex.normSq v₃ * normSq χ₃
      + 2 * ((((starRingEnd ℂ) v₁ * v₂).re * (inner χ₁ χ₂).re
              - ((starRingEnd ℂ) v₁ * v₂).im * (inner χ₁ χ₂).im)
          + (((starRingEnd ℂ) v₂ * v₃).re * (inner χ₂ χ₃).re
              - ((starRingEnd ℂ) v₂ * v₃).im * (inner χ₂ χ₃).im)
          + (((starRingEnd ℂ) v₃ * v₁).re * (inner χ₃ χ₁).re
              - ((starRingEnd ℂ) v₃ * v₁).im * (inner χ₃ χ₁).im)) := by
  simp only [normSq, inner, Fin.sum_univ_two, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The dual potential on the neutral configuration `(conj v₁, conj v₂, conj v₃)`. -/
lemma V4_dual_neutral (p : Params) (v₁ v₂ v₃ : ℂ) :
    3 * V4 (dual p) ![(starRingEnd ℂ) v₁, 0] ![(starRingEnd ℂ) v₂, 0] ![(starRingEnd ℂ) v₃, 0]
    = -((Complex.normSq v₁ + Complex.normSq v₂ + Complex.normSq v₃) ^ 2 / p.L0)
      - 4 * (Complex.normSq v₁ ^ 2 + Complex.normSq v₂ ^ 2 + Complex.normSq v₃ ^ 2
          - Complex.normSq v₁ * Complex.normSq v₂ - Complex.normSq v₂ * Complex.normSq v₃
          - Complex.normSq v₃ * Complex.normSq v₁) / p.L3
      - 12 / (p.L1 * p.L2 - p.L4 ^ 2 / 4)
        * (mstar p.L1 p.L2 p.L4 ((starRingEnd ℂ) v₁ * v₂).re ((starRingEnd ℂ) v₁ * v₂).im
          + mstar p.L1 p.L2 p.L4 ((starRingEnd ℂ) v₂ * v₃).re ((starRingEnd ℂ) v₂ * v₃).im
          + mstar p.L1 p.L2 p.L4 ((starRingEnd ℂ) v₃ * v₁).re ((starRingEnd ℂ) v₃ * v₁).im) := by
  rw [V4_eq]
  simp only [V4G, dual, mstar, normSq, inner, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Complex.normSq_apply, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.conj_conj, map_zero, mul_zero,
    Complex.zero_re, Complex.zero_im, add_zero]
  ring

/-- **Duality.**  Let `Λ₀ < 0`, `Λ₃ > 0` and let `[[Λ₁, Λ₄/2], [Λ₄/2, Λ₂]]` be positive definite.
If the potential with the dual couplings is non-negative on all neutral configurations, then
`V₄ ≥ 0` on all field configurations. -/
theorem boundedBelow_of_dual_neutral (p : Params) (h0 : p.L0 < 0) (h3 : 0 < p.L3)
    (h1 : 0 < p.L1) (hδ : 0 < p.L1 * p.L2 - p.L4 ^ 2 / 4) (hd : NeutralBoundedBelow (dual p)) :
    BoundedBelow p := by
  intro χ₁ χ₂ χ₃
  obtain ⟨v₁, v₂, v₃, hn, e0, e1⟩ := exists_null χ₁ χ₂ χ₃
  have hrel := normSq_comb χ₁ χ₂ χ₃ v₁ v₂ v₃
  rw [e0, e1, map_zero, add_zero] at hrel
  have hneutral := hd ((starRingEnd ℂ) v₁) ((starRingEnd ℂ) v₂) ((starRingEnd ℂ) v₃)
  have h3V := V4_dual_neutral p v₁ v₂ v₃
  have core := dual_core h0 h3 h1 hδ (Complex.normSq v₁) (Complex.normSq v₂) (Complex.normSq v₃)
    (normSq χ₁) (normSq χ₂) (normSq χ₃)
    ((starRingEnd ℂ) v₁ * v₂).re ((starRingEnd ℂ) v₁ * v₂).im
    ((starRingEnd ℂ) v₂ * v₃).re ((starRingEnd ℂ) v₂ * v₃).im
    ((starRingEnd ℂ) v₃ * v₁).re ((starRingEnd ℂ) v₃ * v₁).im
    (inner χ₁ χ₂).re (inner χ₁ χ₂).im (inner χ₂ χ₃).re (inner χ₂ χ₃).im
    (inner χ₃ χ₁).re (inner χ₃ χ₁).im hn hrel.symm
    (by
      have e : (Complex.normSq v₁ + Complex.normSq v₂ + Complex.normSq v₃) ^ 2 / (3 * p.L0)
          + 4 * (Complex.normSq v₁ ^ 2 + Complex.normSq v₂ ^ 2 + Complex.normSq v₃ ^ 2
            - Complex.normSq v₁ * Complex.normSq v₂ - Complex.normSq v₂ * Complex.normSq v₃
            - Complex.normSq v₃ * Complex.normSq v₁) / (3 * p.L3)
          + 4 / (p.L1 * p.L2 - p.L4 ^ 2 / 4)
            * (mstar p.L1 p.L2 p.L4 ((starRingEnd ℂ) v₁ * v₂).re ((starRingEnd ℂ) v₁ * v₂).im
              + mstar p.L1 p.L2 p.L4 ((starRingEnd ℂ) v₂ * v₃).re ((starRingEnd ℂ) v₂ * v₃).im
              + mstar p.L1 p.L2 p.L4 ((starRingEnd ℂ) v₃ * v₁).re ((starRingEnd ℂ) v₃ * v₁).im)
          = -(3 * V4 (dual p) ![(starRingEnd ℂ) v₁, 0] ![(starRingEnd ℂ) v₂, 0]
              ![(starRingEnd ℂ) v₃, 0]) / 3 := by
        rw [h3V]
        have hL0 : p.L0 ≠ 0 := ne_of_lt h0
        have hL3 : p.L3 ≠ 0 := ne_of_gt h3
        field_simp
        ring
      rw [e]
      linarith)
  rw [V4_eq]
  unfold V4G
  unfold mform at core
  nlinarith [core]

end BFB.A4
