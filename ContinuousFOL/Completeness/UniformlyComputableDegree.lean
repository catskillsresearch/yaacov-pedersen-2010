/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.10 / Corollary 9.11; vision.md page 25
-/
module

public import ContinuousFOL.Completeness.RecursivePresentation
public import ContinuousFOL.Completeness.DegreeOfTruth
public import ContinuousFOL.Completeness.IsSentence
public import ContinuousFOL.Completeness.IsCompleteTheory
public import ContinuousFOL.LanguageAndSemantics.EntailsPre
public import ContinuousFOL.LanguageAndSemantics.CompletelySatisfiable
public import ContinuousFOL.Group1Axioms.DyadicCode.Val

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- A theory `T` is decidable if for every sentence `φ`, `φ°_T` is uniformly computable from `φ`
    (modeled via uniformly decidable rational Dedekind cuts / Cauchy approximations). -/
structure UniformlyComputableDegree {LM : MetricSignature}
    (P : RecursivePresentation LM) (T : Set (Formula LM.toSignature)) where
  approx : ℕ → ℕ → DyadicCode
  spec   : ∀ (φ : Formula LM.toSignature), IsSentence φ →
    ∀ n : ℕ, |(approx (P.encodeFormula φ) n).val - degreeOfTruthComplete T φ| ≤ (2 : ℝ) ^ (-(n : ℤ))

/-- Corollary 9.11: Every complete theory with an r.e. axiomatization is decidable. -/
theorem complete_re_theory_decidable {LM : MetricSignature}
    (P : RecursivePresentation LM) (T Ax : Set (Formula LM.toSignature))
    (hcomp : IsCompleteTheory T)
    (hax : ∀ φ, IsSentence φ → (φ ∈ T ↔ EntailsComplete Ax φ)) :
    Nonempty (UniformlyComputableDegree P T) := by
  sorry

end ContinuousFOL
