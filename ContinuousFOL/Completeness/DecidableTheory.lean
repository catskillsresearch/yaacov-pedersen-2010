/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.10; vision.md page 25
-/
module

public import ContinuousFOL.Completeness.RecursivePresentation
public import ContinuousFOL.Completeness.DegreeOfTruth
public import ContinuousFOL.Completeness.IsSentence
public import ContinuousFOL.Completeness.IsCompleteTheory
public import ContinuousFOL.LanguageAndSemantics.CompletelySatisfiable
public import ContinuousFOL.Completeness.IsTheory

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- The degree of truth `φ°_T` is *uniformly computable (uniformly recursive) from the
sentence `φ`*: there is a single computable `f : ℕ → ℕ → ℤ` such that for every sentence `φ`
and every `n`, the dyadic `f ⌜φ⌝ n / 2ⁿ` is within `2⁻ⁿ` of `φ°_T`. In particular each
`φ°_T` is a recursive real (computable Cauchy approximation with modulus `2⁻ⁿ`). -/
def DegreeUniformlyComputable.{u} {LM : MetricSignature} (P : RecursivePresentation LM)
    (T : Set (Formula LM.toSignature)) : Prop :=
  ∃ f : ℕ → ℕ → ℤ, Computable₂ f ∧
    ∀ φ : Formula LM.toSignature, IsSentence φ → ∀ n : ℕ,
      |(f (P.code φ) n : ℝ) / 2 ^ n - degreeOfTruthMetric.{u} T φ| ≤ (2 : ℝ) ^ (-(n : ℤ))

/-- Definition 9.10: decidability of a theory `T`.
(i) If `T` is complete, `T` is decidable if for every sentence `φ`, `φ°_T` is a recursive real
and uniformly computable from `φ`.
(ii) If `T` is incomplete, `T` is decidable if for every sentence `φ`, `φ°_T` is uniformly
recursive from `φ`.
(Both clauses come out as `DegreeUniformlyComputable`; "uniformly computable" already makes
each value a recursive real.) -/
def IsDecidableTheory.{u} {LM : MetricSignature} (P : RecursivePresentation LM)
    (T : Set (Formula LM.toSignature)) : Prop :=
  (IsCompleteTheory.{u} T → DegreeUniformlyComputable.{u} P T) ∧
  (¬ IsCompleteTheory.{u} T → DegreeUniformlyComputable.{u} P T)

/-- `Ax` is an *axiomatization* of the theory `T`: `Ax` is a set of sentences and the
sentences of `T` are exactly the sentences entailed by `Ax`. -/
def IsAxiomatization.{u} {LM : MetricSignature} (Ax T : Set (Formula LM.toSignature)) : Prop :=
  IsTheory Ax ∧ ∀ φ, IsSentence φ → (φ ∈ T ↔ EntailsComplete.{u} Ax φ)

end ContinuousFOL
