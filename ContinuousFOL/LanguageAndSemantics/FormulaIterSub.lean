/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Notation 3.2 in FO language
-/
module

public import ContinuousFOL.LanguageAndSemantics.Formula

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

variable {L : Signature}

/-- Iterated subtraction `ψ ∸ nφ` (Notation 3.2). -/
def iterSub (ψ φ : Formula L) : ℕ → Formula L
  | 0     => ψ
  | n + 1 => .tsub (iterSub ψ φ n) φ

end Formula

end ContinuousFOL
