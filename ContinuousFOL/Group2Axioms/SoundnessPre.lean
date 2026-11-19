/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §7 Theorem 7.2 without metric; vision.md page 15
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.EntailsPre
public import ContinuousFOL.LanguageAndSemantics.FormulaOne

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Theorem 7.2 (Soundness) for signatures without metric. -/
theorem soundness_pre {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) :
    ProvableQ Γ φ → EntailsPre Γ φ := by
  sorry

theorem satisfiable_consistent_pre {L : Signature} (Γ : Set (Formula L)) :
    SatisfiablePre Γ → ConsistentQ Γ := by
  rintro ⟨M, σ, hM⟩
  refine ⟨Formula.one L, fun hprov => ?_⟩
  have hval := soundness_pre Γ (Formula.one L) hprov M σ hM
  simp at hval

end ContinuousFOL
