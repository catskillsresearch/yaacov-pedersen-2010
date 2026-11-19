/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Notation 3.2 for Łukasiewicz propositional logic
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukPropForm

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

/-- Iterated subtraction `ψ ∸ nφ` (Notation 3.2). -/
def iterSub {I : Type*} (ψ φ : LukPropForm I) : ℕ → LukPropForm I
  | 0     => ψ
  | n + 1 => .tsub (iterSub ψ φ n) φ

end LukPropForm

end ContinuousFOL
