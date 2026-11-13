import BFB.Defs

/-!
# Complex doublets: norms, inner products and the Cauchy–Schwarz inequality

Elementary facts about `SU(2)` doublets `H : Fin 2 → ℂ`.
-/

namespace BFB

lemma normSq_nonneg (H : Fin 2 → ℂ) : 0 ≤ normSq H :=
  Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (H i)

/-- Lagrange's identity for two doublets. -/
lemma lagrange (A B : Fin 2 → ℂ) :
    normSq A * normSq B - Complex.normSq (inner A B)
      = Complex.normSq (A 0 * B 1 - A 1 * B 0) := by
  simp only [normSq, inner, Fin.sum_univ_two, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im]
  ring

/-- Cauchy–Schwarz: `|A† B|² ≤ (A† A)(B† B)`. -/
lemma normSq_inner_le (A B : Fin 2 → ℂ) : Complex.normSq (inner A B) ≤ normSq A * normSq B := by
  have h := lagrange A B
  have := Complex.normSq_nonneg (A 0 * B 1 - A 1 * B 0)
  linarith

end BFB
