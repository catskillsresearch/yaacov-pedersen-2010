/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Notation 3.2
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.CLPropForm

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace CLPropForm

/-- Iterated subtraction `ψ ∸ nφ` (Notation 3.2). -/
def iterSub {I : Type*} (ψ φ : CLPropForm I) : ℕ → CLPropForm I
  | 0     => ψ
  | n + 1 => .tsub (iterSub ψ φ n) φ

end CLPropForm

end ContinuousFOL
