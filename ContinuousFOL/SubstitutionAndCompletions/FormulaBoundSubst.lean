/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Definition 6.3; vision.md page 11
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeSubst
public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeVars

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

variable {L : Signature}

/-- Bound substitution `φ{y/x}` (Definition 6.3). -/
def boundSubst (φ : Formula L) (y x : Var) : Formula L :=
  match φ with
  | .rel P args => .rel P args
  | .tsub α β   => .tsub (α.boundSubst y x) (β.boundSubst y x)
  | .neg α      => .neg (α.boundSubst y x)
  | .half α     => .half (α.boundSubst y x)
  | .sup z α    =>
      let α' := α.boundSubst y x
      if z = x then .sup y (α'.freeSubst (.var y) x) else .sup z α'

/-- Correctness of the bound substitution `φ{y/x}` (Definition 6.3): `φ{y/x}` is *correct* if
`y` is not free in `α` and `α[y/x]` is correct in each subformula `sup_x α` of `φ`.
(`inf_x α` abbreviates `¬ sup_x ¬ α`, so its subformula `sup_x ¬α` is covered by the same
clause.) -/
def BoundSubstCorrect (φ : Formula L) (y x : Var) : Prop :=
  match φ with
  | .rel _ _  => True
  | .tsub α β => α.BoundSubstCorrect y x ∧ β.BoundSubstCorrect y x
  | .neg α    => α.BoundSubstCorrect y x
  | .half α   => α.BoundSubstCorrect y x
  | .sup z α  =>
      (z = x → y ∉ α.freeVars ∧ α.FreeSubstCorrect (.var y) x) ∧ α.BoundSubstCorrect y x

end Formula

end ContinuousFOL
