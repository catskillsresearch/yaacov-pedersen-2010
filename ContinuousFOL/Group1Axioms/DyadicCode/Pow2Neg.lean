/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Notation 3.3
-/
module

public import ContinuousFOL.Group1Axioms.DyadicCode.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace DyadicCode

/-- `2^{-n}` as `n` applications of `half` to `one` (Notation 3.3). -/
def pow2Neg : ℕ → DyadicCode
  | 0     => .one
  | n + 1 => .half (pow2Neg n)

end DyadicCode

end ContinuousFOL
