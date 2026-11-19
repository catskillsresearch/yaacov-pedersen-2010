/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 / §8 Lemma 8.4 term substitution
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.TermVars

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Term

variable {L : Signature}

/-- Replace `x` by `t` inside a term `s`. -/
def subst (s : Term L) (t : Term L) (x : Var) : Term L :=
  match s with
  | .var y       => if y = x then t else .var y
  | .func f args => .func f (fun i => (args i).subst t x)

/-- Replace a 0-ary constant symbol `c` by a variable `x` inside a term (§8, Lemma 8.4). -/
def substConstVar (s : Term L) (c : L.Func) (x : Var) : Term L :=
  match s with
  | .var y       => .var y
  | .func f args =>
      if f = c ∧ L.funcArity f = 0 then .var x
      else .func f (fun i => (args i).substConstVar c x)

end Term

end ContinuousFOL
