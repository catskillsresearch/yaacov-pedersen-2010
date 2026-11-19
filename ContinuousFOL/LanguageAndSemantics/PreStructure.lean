/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.6 (i)–(ii); vision.md page 8–9
-/
module

public import ContinuousFOL.LanguageAndSemantics.Signature
public import Mathlib.Basic.Real.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- A continuous `𝓛`-pre-structure (Definition 5.6 (i)–(ii)). -/
structure PreStructure (L : Signature) where
  Carrier    : Type
  nonempty   : Nonempty Carrier
  funcInterp : (f : L.Func) → (Fin (L.funcArity f) → Carrier) → Carrier
  relInterp  : (P : L.Rel) → (Fin (L.relArity P) → Carrier) → ℝ
  rel_in_Icc : ∀ P args, 0 ≤ relInterp P args ∧ relInterp P args ≤ 1

attribute [instance] PreStructure.nonempty

end ContinuousFOL
