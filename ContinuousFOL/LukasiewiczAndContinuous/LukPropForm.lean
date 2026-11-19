/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §2 Definition 2.1; vision.md page 4
-/
module

public import ContinuousFOL.Introduction.TsubR

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Łukasiewicz propositional formulae over propositional variables `I` (Definition 2.1). -/
inductive LukPropForm (I : Type*) : Type _
  | var  : I → LukPropForm I
  | tsub : LukPropForm I → LukPropForm I → LukPropForm I
  | neg  : LukPropForm I → LukPropForm I
  deriving DecidableEq

end ContinuousFOL
