/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 consistency via 1; vision.md page 16–17
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaOne

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Consistency criterion via `1`: `Γ` is inconsistent iff `Γ ⊢_Q 1`. -/
lemma inconsistent_iff_provable_one {L : Signature} (Γ : Set (Formula L)) :
    ¬ ConsistentQ Γ ↔ ProvableQ Γ (Formula.one L) := by
  sorry

end ContinuousFOL
