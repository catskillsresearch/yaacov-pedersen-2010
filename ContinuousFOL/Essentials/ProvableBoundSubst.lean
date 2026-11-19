/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.3; vision.md page 16
-/
module

public import ContinuousFOL.Group2Axioms.ProvableQ
public import ContinuousFOL.SubstitutionAndCompletions.FormulaBoundSubst

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Lemma 8.3: Provable equivalence of bound variable renaming `φ` and `φ{y/x}`. -/
theorem provable_bound_subst {L : Signature} (φ : Formula L) (x y : Var)
    (hy : y ∉ φ.allVars) :
    ProvableQ ∅ (.tsub φ (φ.boundSubst y x)) ∧
    ProvableQ ∅ (.tsub (φ.boundSubst y x) φ) := by
  sorry

end ContinuousFOL
