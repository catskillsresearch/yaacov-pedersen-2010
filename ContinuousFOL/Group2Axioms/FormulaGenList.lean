/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §7 generalizations; vision.md page 14
-/
module

public import ContinuousFOL.LanguageAndSemantics.Formula

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Generalization of a formula `sup_{x₁} ... sup_{x_n} ψ` (§7). -/
def Formula.genList {L : Signature} : List Var → Formula L → Formula L
  | [],      ψ => ψ
  | x :: xs, ψ => .sup x (Formula.genList xs ψ)

end ContinuousFOL
