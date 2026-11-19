/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Remark 3.4 embedding into CL formulae
-/
module

public import ContinuousFOL.Group1Axioms.CLPropForm.One
public import ContinuousFOL.Group1Axioms.DyadicCode.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace CLPropForm

def dyadic {I : Type*} (anchor : CLPropForm I) : DyadicCode → CLPropForm I
  | .one      => one anchor
  | .neg d    => .neg (dyadic anchor d)
  | .tsub a b => .tsub (dyadic anchor a) (dyadic anchor b)
  | .half d   => .half (dyadic anchor d)

end CLPropForm

end ContinuousFOL
