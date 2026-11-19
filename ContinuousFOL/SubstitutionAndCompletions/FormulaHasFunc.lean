/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.4 helpers; vision.md page 16
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.TermSubst
public import ContinuousFOL.LanguageAndSemantics.Formula

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Term

variable {L : Signature}

/-- Whether a function symbol `c` occurs in a term `t`. -/
def hasFunc (t : Term L) (c : L.Func) : Prop :=
  match t with
  | .var _       => False
  | .func f args => f = c ∨ ∃ i, hasFunc (args i) c

end Term

namespace Formula

variable {L : Signature}

/-- Whether a function symbol `c` occurs in `φ`. -/
def hasFunc (φ : Formula L) (c : L.Func) : Prop :=
  match φ with
  | .rel _ args => ∃ i, Term.hasFunc (args i) c
  | .tsub α β   => α.hasFunc c ∨ β.hasFunc c
  | .neg α      => α.hasFunc c
  | .half α     => α.hasFunc c
  | .sup _ α    => α.hasFunc c

/-- Replace a 0-ary constant symbol `c` by a variable `x` inside `φ` (Lemma 8.4). -/
def substConstVar (φ : Formula L) (c : L.Func) (x : Var) : Formula L :=
  match φ with
  | .rel P args => .rel P (fun i => (args i).substConstVar c x)
  | .tsub α β   => .tsub (α.substConstVar c x) (β.substConstVar c x)
  | .neg α      => .neg (α.substConstVar c x)
  | .half α     => .half (α.substConstVar c x)
  | .sup z α    => .sup z (α.substConstVar c x)

end Formula

end ContinuousFOL
