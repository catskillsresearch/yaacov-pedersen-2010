/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Notation 3.3: 0 := ¬1
-/
module

public import ContinuousFOL.Group1Axioms.DyadicCode.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace DyadicCode

def zero : DyadicCode := .neg .one

end DyadicCode

end ContinuousFOL
