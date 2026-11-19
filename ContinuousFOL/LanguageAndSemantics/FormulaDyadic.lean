/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Remark 3.4 / Notation 3.3 in FO language
-/
module

public import ContinuousFOL.LanguageAndSemantics.FormulaOne
public import ContinuousFOL.Group1Axioms.DyadicCode.Pow2Neg

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

/-- Syntactic dyadic constant in `Formula L` (Remark 3.4). -/
def dyadic (L : Signature) : DyadicCode → Formula L
  | .one      => one L
  | .neg d    => .neg (dyadic L d)
  | .tsub a b => .tsub (dyadic L a) (dyadic L b)
  | .half d   => .half (dyadic L d)

/-- `2^{-n}` shorthand in `Formula L` (Notation 3.3). -/
def pow2Neg (L : Signature) (n : ℕ) : Formula L :=
  dyadic L (.pow2Neg n)

end Formula

end ContinuousFOL
