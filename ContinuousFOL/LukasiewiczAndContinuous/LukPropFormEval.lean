/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §2 Definition 2.1 evaluation
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukPropForm

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

def eval {I : Type*} (v₀ : I → ℝ) : LukPropForm I → ℝ
  | .var i    => v₀ i
  | .tsub φ ψ => eval v₀ φ ∸ eval v₀ ψ
  | .neg φ    => 1 - eval v₀ φ

end LukPropForm

end ContinuousFOL
