/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 term variables; vision.md page 11
-/
module

public import ContinuousFOL.LanguageAndSemantics.Term
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Union

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Term

variable {L : Signature}

/-- Variables occurring in a term `t`. -/
def vars : Term L → Finset Var
  | .var x       => {x}
  | .func _ args => Finset.univ.biUnion (fun i => (args i).vars)

end Term

end ContinuousFOL
