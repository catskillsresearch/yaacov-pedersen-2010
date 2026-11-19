/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Corollary 9.11; vision.md page 25
-/
module

public import ContinuousFOL.Completeness.DecidableTheory
public import Mathlib.Computability.Partrec

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Corollary 9.11: Every complete theory with a recursive or recursively enumerable
axiomatization is decidable. -/
theorem complete_re_theory_decidable.{u} {LM : MetricSignature}
    (P : RecursivePresentation LM) (T : Set (Formula LM.toSignature))
    (hcomp : IsCompleteTheory.{u} T)
    (hax : ∃ Ax : Set (Formula LM.toSignature), IsAxiomatization.{u} Ax T ∧
      (ComputablePred (fun n : ℕ => ∃ φ ∈ Ax, P.code φ = n) ∨
        REPred (fun n : ℕ => ∃ φ ∈ Ax, P.code φ = n))) :
    IsDecidableTheory.{u} P T := by
  sorry

end ContinuousFOL
