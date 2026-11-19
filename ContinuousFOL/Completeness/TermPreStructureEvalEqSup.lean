/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Truth Lemma / Theorem 9.4 core; vision.md page 21–23
-/
module

public import ContinuousFOL.Completeness.TermPreStructure
public import ContinuousFOL.Completeness.HenkinComplete
public import ContinuousFOL.Essentials.MaximalConsistent

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Truth Lemma for the Henkin term model (core induction of Theorem 9.4):
    `𝔐(φ, σ) = sup { p ∈ D : p ∸ φ ∈ Δ }`. -/
theorem termPreStructure_eval_eq_sup {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (hhenk : HenkinComplete Δ) (φ : Formula L) :
    φ.eval (termPreStructure Δ) (idTermAssign L) =
      sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
        Formula.tsub (Formula.dyadic L p) φ ∈ Δ} := by
  sorry

end ContinuousFOL
