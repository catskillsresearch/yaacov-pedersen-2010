/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §2 Definition 2.4; vision.md page 4
-/
module

public import ContinuousFOL.Introduction.TsubR

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Continuous propositional formulae over `I` (Definition 2.4). -/
inductive CLPropForm (I : Type*) : Type _
  | var  : I → CLPropForm I
  | tsub : CLPropForm I → CLPropForm I → CLPropForm I
  | neg  : CLPropForm I → CLPropForm I
  | half : CLPropForm I → CLPropForm I
  deriving DecidableEq

end ContinuousFOL
