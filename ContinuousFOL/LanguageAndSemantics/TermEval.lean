/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.10; vision.md page 9
-/
module

public import ContinuousFOL.LanguageAndSemantics.Term
public import ContinuousFOL.LanguageAndSemantics.PreStructure

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Interpretation of a term `t^{𝔐, σ}` (Definition 5.10). -/
def Term.eval {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier) : Term L → M.Carrier
  | .var x       => σ x
  | .func f args => M.funcInterp f (fun i => (args i).eval M σ)

end ContinuousFOL
