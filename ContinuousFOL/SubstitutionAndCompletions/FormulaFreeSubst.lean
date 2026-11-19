/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Definition 6.1; vision.md page 11
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeVars
public import ContinuousFOL.SubstitutionAndCompletions.TermSubst

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

variable {L : Signature}

/-- Free substitution `φ[t/x]` (Definition 6.1). -/
def freeSubst (φ : Formula L) (t : Term L) (x : Var) : Formula L :=
  match φ with
  | .rel P args => .rel P (fun i => (args i).subst t x)
  | .tsub α β   => .tsub (α.freeSubst t x) (β.freeSubst t x)
  | .neg α      => .neg (α.freeSubst t x)
  | .half α     => .half (α.freeSubst t x)
  | .sup y α    => if y = x then .sup y α else .sup y (α.freeSubst t x)

/-- Correctness of free substitution `φ[t/x]` (Definition 6.1): no variable in `t`
    is captured by a quantifier when `x` occurs free. -/
def FreeSubstCorrect (φ : Formula L) (t : Term L) (x : Var) : Prop :=
  match φ with
  | .rel _ _  => True
  | .tsub α β => α.FreeSubstCorrect t x ∧ β.FreeSubstCorrect t x
  | .neg α    => α.FreeSubstCorrect t x
  | .half α   => α.FreeSubstCorrect t x
  | .sup y α  =>
      if y = x then True
      else (x ∈ α.freeVars → y ∉ t.vars) ∧ α.FreeSubstCorrect t x

end Formula

end ContinuousFOL
