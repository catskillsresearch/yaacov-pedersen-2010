/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §4 Fact 4.4; vision.md page 7
-/
module

public import ContinuousFOL.Group1Axioms.CLPropForm.Provable
public import ContinuousFOL.Group1Axioms.CLPropForm.Dyadic
public import ContinuousFOL.Group1Axioms.DyadicCode.Pow2Neg
public import ContinuousFOL.LukasiewiczAndContinuous.CLPropFormModels

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Fact 4.4 (Approximated Strong Completeness for Continuous Logic):
    "Let S be a continuous propositional logic, Σ ⊆ S, and φ ∈ S.
    Then Σ ⊨ φ if and only if Σ ⊢ φ ∸ 2^{-n} for all n < ω."

    The constant `2^{-n}` is built from the given `φ`, following Notation 3.3
    (`1 := ¬(φ ∸ φ)`), so the statement does not assume that `I` is inhabited. -/
theorem cl_approx_strong_completeness {I : Type*}
    (hypSet : Set (CLPropForm I)) (φ : CLPropForm I) :
    CLPropForm.Entails hypSet φ ↔
      ∀ n : ℕ, CLPropForm.Provable hypSet
        (.tsub φ (CLPropForm.dyadic φ (.pow2Neg n))) := by
  sorry

end ContinuousFOL
