/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.5; vision.md page 17
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Lemma 8.5: Closure properties of consistent sets. -/
theorem consistent_adjoin_approx {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) (φ : Formula L)
    (happrox : ∀ n : ℕ, ProvableQ Γ (.tsub φ (Formula.pow2Neg L n))) :
    ConsistentQ (Γ ∪ {φ}) := by
  sorry

theorem consistent_adjoin_comparable {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) (φ ψ : Formula L) :
    ConsistentQ (Γ ∪ {.tsub φ ψ}) ∨ ConsistentQ (Γ ∪ {.tsub ψ φ}) := by
  sorry

end ContinuousFOL
