import Mathlib

/-!
# Boundedness from below of the `A₄`-symmetric three-Higgs-doublet potential for `Λ₄ = 0`

Definitions and statements only (the proofs are replaced by `sorry`); this file is the input
for Comparator.  The definitions are a verbatim copy of `BFB/Defs.lean`; the proofs are in
`BFB/S4Equiv.lean` and `BFB/S4ThreeHDM.lean`.

Source of the potential and of the conditions:
L. Lavoura, A. Milagre, "Complete set of bounded-from-below conditions for the `A₄`-symmetric
three-Higgs-doublet model", arXiv:2611.05475v1 (3 Nov 2026).
-/

namespace BFB

/-- `H† H`. -/
noncomputable def normSq (H : Fin 2 → ℂ) : ℝ := ∑ i, Complex.normSq (H i)

/-- `A† B`. -/
noncomputable def inner (A B : Fin 2 → ℂ) : ℂ := ∑ i, (starRingEnd ℂ) (A i) * B i

namespace S4

/-- The conditions of Lavoura–Milagre, Section 5 (case `Λ₄ = 0`), Eqs. (50)–(53) of
arXiv:2611.05475v1, transcribed literally: "enforce" the five inequalities (50), and
"impede / forbid / discard" the three situations (51), (52), (53). -/
def LMConditions (L0 L1 L2 L3 : ℝ) : Prop :=
  (0 ≤ L0 + L3 ∧ 0 ≤ L0 + L1 ∧ 0 ≤ L0 + (L1 + 3 * L2) / 4 ∧
    0 ≤ L0 + L3 / 4 + 3 * min L1 L2 / 4 ∧ 0 ≤ L0 + L3 / 4) ∧
  ¬ (0 < L2 ∧ L0 + L1 / 4 < 0) ∧
  ¬ (|L2 - L1| - 3 * L1 - L2 < 0 ∧ L0 + L1 * L2 / (3 * L1 + L2) < 0) ∧
  ¬ (max 0 (2 * L0) - L3 < 0 ∧
      max (-L1 - L2 - 2 * L3) (L1 + L2 + 6 * L0 * L3 / (L0 + L3)) - |L1 - L2| < 0)

/-- The necessary and sufficient conditions of Ivanov–Vazão for the `S₄`-symmetric model
(vertices A, B, C, D, E, F and their counterparts `Λ₁ → Λ₃`, and the two arc conditions),
as quoted in Lavoura–Milagre, Section 5, Eqs. (54a)–(54h), (55), (56); in JHEP 11 (2020) 104
they are Eqs. (4.5), (4.8), (4.9). -/
def IVConditions (L0 L1 L2 L3 : ℝ) : Prop :=
  (0 ≤ L0 + L1 ∧ 0 ≤ L0 + L3 ∧ 0 ≤ L0 + (L1 + 3 * L2) / 4 ∧ 0 ≤ L0 + (L3 + 3 * L2) / 4 ∧
    0 ≤ L0 + L1 / 4 ∧ 0 ≤ L0 + L3 / 4 ∧
    0 ≤ L0 + (L1 + 3 * L2) / 16 ∧ 0 ≤ L0 + (L3 + 3 * L2) / 16) ∧
  ¬ (0 < L1 - |L2| ∧ L0 + L1 * L2 / (3 * L1 + L2) < 0) ∧
  ¬ (0 < L3 - |L2| ∧ L0 + L2 * L3 / (L2 + 3 * L3) < 0)

end S4

namespace A4

/-- The quartic couplings `Λ₀, …, Λ₄`. -/
structure Params where
  L0 : ℝ
  L1 : ℝ
  L2 : ℝ
  L3 : ℝ
  L4 : ℝ

/-- Quartic part of the `A₄`-symmetric potential, Eq. (3) of arXiv:2611.05475. -/
noncomputable def V4 (p : Params) (χ₁ χ₂ χ₃ : Fin 2 → ℂ) : ℝ :=
  (p.L0 + p.L3) / 3 * (normSq χ₁ ^ 2 + normSq χ₂ ^ 2 + normSq χ₃ ^ 2)
    + (2 * p.L0 - p.L3) / 3
        * (normSq χ₁ * normSq χ₂ + normSq χ₂ * normSq χ₃ + normSq χ₃ * normSq χ₁)
    + (p.L1 + p.L2) / 2
        * (Complex.normSq (inner χ₁ χ₂) + Complex.normSq (inner χ₂ χ₃)
            + Complex.normSq (inner χ₃ χ₁))
    + (p.L1 - p.L2) / 2 * (inner χ₁ χ₂ ^ 2 + inner χ₂ χ₃ ^ 2 + inner χ₃ χ₁ ^ 2).re
    + p.L4 / 2 * (inner χ₁ χ₂ ^ 2 + inner χ₂ χ₃ ^ 2 + inner χ₃ χ₁ ^ 2).im

/-- Boundedness from below: the quartic part is non-negative on every field configuration
(the definition used in arXiv:2611.05475 and in JHEP 11 (2020) 104). -/
def BoundedBelow (p : Params) : Prop := ∀ χ₁ χ₂ χ₃ : Fin 2 → ℂ, 0 ≤ V4 p χ₁ χ₂ χ₃

/-- `τ² N² - 3 τ E - 3 (4τ - 3) Q` as a function of the Gram data. -/
def gG (τ a1 a2 a3 : ℝ) (A12 A23 A31 : ℂ) : ℝ :=
  τ ^ 2 * (a1 + a2 + a3) ^ 2
    - 3 * τ * (a1 * a2 + a2 * a3 + a3 * a1
        - Complex.normSq A12 - Complex.normSq A23 - Complex.normSq A31)
    - 3 * (4 * τ - 3) * (A12.im ^ 2 + A23.im ^ 2 + A31.im ^ 2)

/-- The conditions of arXiv:2611.05475v1, Section 4 ("Conclusions and hypothesis"), for the
general `A₄`-symmetric potential, transcribed literally: the five inequalities (43a)–(43e) that
must be enforced and the four situations (44), (45), (46), (47) that must not occur.  The
authors show that the conditions are necessary and conjecture that they are sufficient. -/
def LMConditions (p : Params) : Prop :=
  (0 ≤ p.L0 + p.L3 ∧ 0 ≤ p.L0 + p.L1 ∧ 0 ≤ p.L0 + (p.L1 + 3 * p.L2 - √3 * |p.L4|) / 4 ∧
    0 ≤ p.L0 + p.L3 / 4 + 3 * (p.L1 + p.L2 - √((p.L1 - p.L2) ^ 2 + p.L4 ^ 2)) / 8 ∧
    0 ≤ p.L0 + p.L3 / 4) ∧
  ¬ (|p.L4| - 2 * √3 * p.L2 < 0 ∧
      p.L0 + (4 * p.L1 * p.L2 - p.L4 ^ 2) / (16 * p.L2) < 0) ∧
  ¬ (|3 * (p.L2 - p.L1) - √3 * p.L4| - 3 * (3 * p.L1 + p.L2 - √3 * p.L4) < 0 ∧
      p.L0 + (4 * p.L1 * p.L2 - p.L4 ^ 2) / (4 * (3 * p.L1 + p.L2 - √3 * p.L4)) < 0) ∧
  ¬ (|3 * (p.L2 - p.L1) + √3 * p.L4| - 3 * (3 * p.L1 + p.L2 + √3 * p.L4) < 0 ∧
      p.L0 + (4 * p.L1 * p.L2 - p.L4 ^ 2) / (4 * (3 * p.L1 + p.L2 + √3 * p.L4)) < 0) ∧
  ¬ (max 0 (2 * p.L0) - p.L3 < 0 ∧
      max (-p.L1 - p.L2 - 2 * p.L3) (p.L1 + p.L2 + 6 * p.L0 * p.L3 / (p.L0 + p.L3))
        - √((p.L1 - p.L2) ^ 2 + p.L4 ^ 2) < 0)

end A4

end BFB

/-! ## Statements -/

namespace BFB

/-- **The two sets of boundedness-from-below conditions for the `S₄`-symmetric
three-Higgs-doublet model are equivalent**: the conditions of Lavoura–Milagre (arXiv:2611.05475,
Section 5) hold if and only if the conditions of Ivanov–Vazão (JHEP 11 (2020) 104) hold. -/
theorem S4.lmS4_iff_iv (L0 L1 L2 L3 : ℝ) :
    S4.LMConditions L0 L1 L2 L3 ↔ S4.IVConditions L0 L1 L2 L3 := by
  sorry

namespace A4

/-- **The key inequality** for three arbitrary doublets. -/
theorem gG_nonneg {τ : ℝ} (hτ : 3 / 4 ≤ τ) (χ₁ χ₂ χ₃ : Fin 2 → ℂ) :
    0 ≤ gG τ (normSq χ₁) (normSq χ₂) (normSq χ₃) (inner χ₁ χ₂) (inner χ₂ χ₃) (inner χ₃ χ₁) := by
  sorry

/-- **Boundedness from below of the `S₄`-symmetric three-Higgs-doublet potential.**
For `Λ₄ = 0`, the quartic part is non-negative on all field configurations if and only if the
conditions of Ivanov–Vazão hold. -/
theorem boundedBelow_iff_iv (p : Params) (h4 : p.L4 = 0) :
    BoundedBelow p ↔ S4.IVConditions p.L0 p.L1 p.L2 p.L3 := by
  sorry

/-- **The conjecture of Lavoura and Milagre is true for `Λ₄ = 0`** (symmetry `S₄`): the
conditions of arXiv:2611.05475, Section 4, are necessary and sufficient for the quartic part of
the potential to be non-negative on all field configurations. -/
theorem lm_conjecture_S4 (p : Params) (h4 : p.L4 = 0) : BoundedBelow p ↔ LMConditions p := by
  sorry

end A4

end BFB
