/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.2; vision.md page 7–8
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fin.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- A continuous signature `𝓛 = (ℛ, ℱ, 𝒢, n)` (Definition 5.2).
    Note: `ℛ ≠ ∅` is captured by `Nonempty L.Rel`.
    Moduli `δ : ℝ → ℝ` map `(0, 1]` into `(0, 1]`. -/
structure Signature where
  Rel      : Type*
  Func     : Type*
  nonempty_rel : Nonempty Rel
  relArity  : Rel → ℕ
  funcArity : Func → ℕ
  relMod   : (P : Rel) → Fin (relArity P) → ℝ → ℝ
  funcMod  : (f : Func) → Fin (funcArity f) → ℝ → ℝ
  relMod_pos  : ∀ P i ε, 0 < ε → ε ≤ 1 → 0 < relMod P i ε ∧ relMod P i ε ≤ 1
  funcMod_pos : ∀ f i ε, 0 < ε → ε ≤ 1 → 0 < funcMod f i ε ∧ funcMod f i ε ≤ 1

attribute [instance] Signature.nonempty_rel

end ContinuousFOL
