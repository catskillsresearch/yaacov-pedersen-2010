/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.1; vision.md page 7
-/
module

public import Mathlib.Data.Nat.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Variable identifiers `V = {v₀, v₁, ...}` (Definition 5.1). -/
abbrev Var := ℕ

end ContinuousFOL
