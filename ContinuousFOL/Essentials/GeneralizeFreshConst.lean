/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.4; vision.md page 16
-/
module

public import ContinuousFOL.Group2Axioms.ProvableQ
public import ContinuousFOL.SubstitutionAndCompletions.FormulaHasFunc

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Lemma 8.4: Generalizing over a fresh constant symbol `c`. -/
theorem generalize_fresh_const {L : Signature} (Γ : Set (Formula L)) (φ : Formula L)
    (c : L.Func) (hc0 : L.funcArity c = 0)
    (hcΓ : ∀ ψ ∈ Γ, ¬ ψ.hasFunc c) (x : Var) (hxφ : x ∉ φ.allVars)
    (hprov : ProvableQ Γ φ) :
    ProvableQ Γ (.sup x (φ.substConstVar c x)) := by
  sorry

end ContinuousFOL
