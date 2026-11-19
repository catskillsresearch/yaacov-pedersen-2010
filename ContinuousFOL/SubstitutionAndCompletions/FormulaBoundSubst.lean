/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Definition 6.3; vision.md page 11
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeSubst

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

end Formula

end ContinuousFOL
