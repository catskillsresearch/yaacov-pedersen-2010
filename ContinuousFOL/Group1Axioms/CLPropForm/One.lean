/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Notation 3.3
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.CLPropForm

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace CLPropForm

/-- Canonical formula `1 := ¬(φ₀ ∸ φ₀)` given any anchor formula `φ₀` (Notation 3.3). -/
def one {I : Type*} (anchor : CLPropForm I) : CLPropForm I :=
  .neg (.tsub anchor anchor)

end CLPropForm

end ContinuousFOL
