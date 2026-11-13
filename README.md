# Machine-checked proofs for the Lavoura–Milagre conjecture on the A4-symmetric three-Higgs-doublet model

**Background.** L. Lavoura and A. Milagre, *Complete set of bounded-from-below conditions for the A4-symmetric
three-Higgs-doublet model*, [arXiv:2611.05475](https://arxiv.org/abs/2611.05475) (3 Nov 2026), derive necessary
conditions for the quartic part V4 of the A4-symmetric potential of three Higgs doublets to be non-negative on
all field configurations (their Eqs. (43)–(47)). After a numerical test on 10^6 potentials they write: "We
therefore conjecture that our necessary conditions for BnessFB are, in fact, necessary and sufficient."

**Results.** This repository contains Lean 4 / Mathlib proofs (no `sorry`, no `native_decide`; axioms: `propext`,
`Quot.sound`, `Classical.choice`) of

1. the conjecture in the case **Λ4 = 0**, in which the symmetry of the potential is S4 (unconditional);
2. the sufficiency of the conditions in the case **Λ0 < 0**, for arbitrary Λ4, *conditional on* the theorem of
   N. Buskin and I. P. Ivanov on neutral configurations ([J. Phys. A 54 (2021)
   325401](https://arxiv.org/abs/2104.11428)), which enters as an explicit hypothesis and is **not** formalized
   here (added on 13 Nov 2026, second version of the repository).

The case Λ4 ≠ 0, Λ0 ≥ 0 is open.

### 1. The case Λ4 = 0

```lean
/-- For Λ4 = 0 the conditions of arXiv:2611.05475, Section 4, are necessary and sufficient
for V4 ≥ 0 on all field configurations. -/
theorem BFB.A4.lm_conjecture_S4 (p : Params) (h4 : p.L4 = 0) : BoundedBelow p ↔ LMConditions p

/-- For Λ4 = 0, V4 ≥ 0 on all field configurations iff the conditions of Ivanov–Vazão hold. -/
theorem BFB.A4.boundedBelow_iff_iv (p : Params) (h4 : p.L4 = 0) :
    BoundedBelow p ↔ S4.IVConditions p.L0 p.L1 p.L2 p.L3

/-- The S4 conditions of Lavoura–Milagre (their Section 5) and those of Ivanov–Vazão are equivalent. -/
theorem BFB.S4.lmS4_iff_iv (L0 L1 L2 L3 : ℝ) : LMConditions L0 L1 L2 L3 ↔ IVConditions L0 L1 L2 L3
```

Here `BoundedBelow p` means `∀ χ₁ χ₂ χ₃ : Fin 2 → ℂ, 0 ≤ V4 p χ₁ χ₂ χ₃`, and `V4` is Eq. (3) of the paper.

**What is new and what is not.** For the S4-symmetric model, necessary and sufficient conditions were derived by
I. P. Ivanov and F. Vazão ([JHEP 11 (2020) 104](https://arxiv.org/abs/2006.00036)) from a geometric description of
the orbit space; Lavoura and Milagre state that they "numerically checked that the two methods ... are in practice
equivalent". Here

* the Ivanov–Vazão result is proved from first principles, directly from the potential, by a different and
  elementary route (`boundedBelow_iff_iv`);
* the equivalence of the two sets of conditions is proved exactly, for all real couplings (`lmS4_iff_iv`);
* together this gives the Lavoura–Milagre conjecture for Λ4 = 0 (`lm_conjecture_S4`).

### 2. The case Λ0 < 0

```lean
/-- Duality: let Λ0 < 0, Λ3 > 0 and let [[Λ1, Λ4/2], [Λ4/2, Λ2]] be positive definite.  If the potential with
the dual couplings is non-negative on all neutral configurations, then V4 ≥ 0 on all field configurations. -/
theorem BFB.A4.boundedBelow_of_dual_neutral (p : Params) (h0 : p.L0 < 0) (h3 : 0 < p.L3) (h1 : 0 < p.L1)
    (hδ : 0 < p.L1 * p.L2 - p.L4 ^ 2 / 4) (hd : NeutralBoundedBelow (dual p)) : BoundedBelow p

/-- If Λ0 < 0 and the conditions of arXiv:2611.05475, Section 4, hold, then V4 ≥ 0 on all field
configurations -- given the "if" direction of Theorem 1 of Buskin–Ivanov. -/
theorem BFB.A4.lm_sufficient_of_L0_neg (hBI : BuskinIvanovTheorem) (p : Params) (h0 : p.L0 < 0)
    (h : LMConditions p) : BoundedBelow p
```

The dual couplings are Λ0' = −1/Λ0, Λ3' = −4/Λ3 and [[Λ1', Λ4'/2], [Λ4'/2, Λ2']] = −4 [[Λ1, Λ4/2], [Λ4/2, Λ2]]⁻¹.
`BuskinIvanovTheorem` is the statement "the conditions (3), (4) of arXiv:2104.11428 imply that the potential (1)
of that paper is non-negative on ℂ³", transcribed from the paper. Lavoura and Milagre prove that their conditions
are necessary; so the second theorem says that their conjecture holds for Λ0 < 0, *if* the published theorem of
Buskin and Ivanov is taken for granted. (Necessity for Λ4 ≠ 0 is not formalized here.) The duality itself
(`boundedBelow_of_dual_neutral`) is unconditional.

### What is not proved

**The case Λ4 ≠ 0, Λ0 ≥ 0 is not proved here.** [`notes/general_case.pdf`](notes/general_case.pdf) contains
partial results for it (a large part of Λ0 > 0). Those are pen-and-paper arguments: **not formalized, not
machine-checked and not read by any human.** They are included for transparency and should be treated as
unverified.

A description of the proofs for human readers is in [`paper/s4_3hdm.pdf`](paper/s4_3hdm.pdf).

## Idea of the proofs

**Λ4 = 0.** With `A_kl = χ_k† χ_l`, `N = A₁₁+A₂₂+A₃₃`, `E = Σ_{k<l} (A_kk A_ll − |A_kl|²)` and `Q = Σ (Im A_kl)²` (pairs 12,
23, 31), every triple of doublets satisfies

```
τ² N² − 3 τ E − 3 (4τ − 3) Q ≥ 0      for every τ ≥ 3/4        (BFB.A4.gG_nonneg)
```

After an SU(2) gauge rotation that makes the upper components of all three doublets real (three real linear
equations, four real unknowns), twice the left-hand side is a sum of squares. Sufficiency of the conditions then
follows by choosing, depending on the couplings, one of these inequalities (τ = 3/4, τ = 3/2, or the τ given by
the "arc" condition) and combining it linearly with trivial ones. Necessity follows by evaluating the potential
on two explicit two-parameter families of field configurations and at two further points. The equivalence of the
two sets of conditions is real arithmetic with case distinctions.

**Λ0 < 0.** Three doublets are linearly dependent: `v₁χ₁ + v₂χ₂ + v₃χ₃ = 0` for some `v ≠ 0` in ℂ³. Taking the
norm gives a linear relation between the Gram data `A_kl` whose coefficients are the Gram data of the *neutral*
configuration `v`. Four applications of the Cauchy–Schwarz inequality (diagonal part with weight Λ3, each
off-diagonal entry with the positive definite form given by Λ1, Λ2, Λ4) turn this relation into `V4 ≥ 0`,
provided the dual potential is non-negative at `v`. The second step shows that conditions (43)–(47) with Λ0 < 0
imply the neutral conditions for the dual couplings: (43b), (43c), (44)–(46) say that the binary quadratic form
`m` given by Λ1, Λ2, Λ4 is at least −Λ0 on the boundary of a triangle, from which the required inequalities
between the coefficients follow.

## Files

| File | Content |
|---|---|
| `Challenge.lean` | the definitions and the six statements with `sorry` (input for Comparator); the only file one has to read in order to trust the results |
| `Solution.lean` | imports the proof (input for Comparator) |
| `comparator.json` | Comparator configuration |
| `BFB/Defs.lean` | the definitions: doublets, the potential `V4`, `BoundedBelow`, the conditions of Lavoura–Milagre (Section 4 and Section 5) and of Ivanov–Vazão, the dual couplings, the statement of the theorem of Buskin–Ivanov |
| `BFB/Doublets.lean` | Cauchy–Schwarz for doublets |
| `BFB/S4Equiv.lean` | `lmS4_iff_iv`: equivalence of the two sets of S4 conditions |
| `BFB/S4ThreeHDM.lean` | the key inequality, sufficiency, necessity, `boundedBelow_iff_iv`, `lm_conjecture_S4` |
| `BFB/Duality.lean` | `boundedBelow_of_dual_neutral`: the duality for Λ0 < 0 |
| `BFB/Triangle.lean` | real algebra: a binary quadratic form on the boundary of a triangle |
| `BFB/NegL0.lean` | conditions (43)–(47) with Λ0 < 0 imply the neutral conditions for the dual couplings |
| `BFB/Neutral.lean` | translation of the theorem of Buskin–Ivanov into the notation of arXiv:2611.05475; `lm_sufficient_of_L0_neg` |
| `Axioms.lean` | prints the axioms used by the main theorems |
| `paper/` | description of the proofs (LaTeX source and PDF) |
| `notes/` | the general case: partial pen-and-paper results, **unverified** (LaTeX source and PDF) |

## Checking

Requirements: [elan](https://github.com/leanprover/elan) (the toolchain `leanprover/lean4:v4.27.0` is selected by
`lean-toolchain`; Mathlib `v4.27.0` is pinned in `lake-manifest.json`).

```
lake exe cache get      # downloads the compiled Mathlib
lake build              # builds the proof and Axioms
```

The build of this project itself takes about a minute and ends with `Build completed successfully`.
`Axioms.lean` prints, for each main theorem, `depends on axioms: [propext, Classical.choice, Quot.sound]`.

**Comparator.** To check that the theorems are proved with exactly the statements and definitions of
`Challenge.lean`, run [Comparator](https://github.com/leanprover/comparator) in this directory:

```
lake env <path to>/comparator comparator.json
```

(with `landrun` and `lean4export` installed as described in the Comparator README). The run ends with
`Lean default kernel accepts the solution` / `Your solution is okay!`.

## How the statement was transcribed

The Lean kernel checks the proof, not whether the formal statement says what the paper says. The definitions in
`BFB/Defs.lean` (repeated verbatim in `Challenge.lean`) were transcribed as follows:

* `V4` is Eq. (3) of arXiv:2611.05475v1; `LMConditions` are Eqs. (43a)–(43e) and (44)–(47); `S4.LMConditions` are
  Eqs. (50)–(53); `S4.IVConditions` are Eqs. (54)–(56). The equation numbers refer to version 1 of the preprint
  (the only version on 13 Nov 2026); the transcription was compared with its LaTeX source.
* The Ivanov–Vazão conditions were in addition compared with the journal version, JHEP 11 (2020) 104,
  Eqs. (4.5), (4.8), (4.9).
* "Bounded from below" means V4 ≥ 0 for all field configurations, as in both papers.
* `BIPotential`, `BIConditions` and `BuskinIvanovTheorem` are Eq. (1), Eqs. (3), (4) and the "if" direction of
  Theorem 1 of arXiv:2104.11428 (compared with its LaTeX source), with γ = arg d. Theorem
  `lm_sufficient_of_L0_neg` is only as good as this hypothesis: if the transcription deviated from what Buskin and
  Ivanov prove, the theorem would rest on an unproved assumption. As a plausibility check, the statement was
  tested numerically (random parameters, including parameters on the boundary of the conditions).
* In Lean, `x / 0 = 0`. This convention does not influence the statements: wherever a denominator could vanish,
  the truth value of the conditions is already decided by another inequality (see the remark in the paper).

## Status and limitations

* The proof was checked with the standard Lean kernel (via `lake build` and Comparator). No second, independent
  kernel was used.
* No human has read the proofs, the description in `paper/` or the note in `notes/`. Where the description and the
  Lean files differ, the Lean files are authoritative.
* The theorem of Buskin and Ivanov is used, not checked: neither its proof nor its statement has been formalized
  beyond the transcription described above.
* The transcription of the conditions into Lean was done by the AI model that produced the proof and has not been
  reviewed by a second person.
* Searches on 13 Nov 2026 (INSPIRE records citing the two papers, arXiv, GitHub, web) found no proof of the
  conjecture, no proof of the equivalence of the two sets of S4 conditions and no formalization of a
  three-Higgs-doublet potential in a proof assistant. For the two-Higgs-doublet model, stability conditions were
  formalized in Lean by J. Tooby-Smith ([arXiv:2603.08139](https://arxiv.org/abs/2603.08139)). We may have missed
  something.
* The authors of arXiv:2611.05475 were informed on 12 Nov 2026, before this repository was made public.

## Credits

The proofs, their Lean formalization, the description and the note were produced by Claude Fable 5 (an AI model by
Anthropic; model ID `claude-fable-5-2`, working in Claude Code) on 11–13 Nov 2026. The work was commissioned by
Dr. Marc Potempa, who set the task and decided to publish it, but did not contribute to the mathematical content.

## License

Apache License 2.0, see `LICENSE`.
