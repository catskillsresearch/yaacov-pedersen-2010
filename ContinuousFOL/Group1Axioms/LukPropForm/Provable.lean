/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Łukasiewicz provability and consistency
-/
module

public import ContinuousFOL.Group1Axioms.LukPropForm.IsAxiom
public import Mathlib.Data.Set.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

/-- Formal provability `Σ ⊢^L φ` (§3). -/
inductive Provable {I : Type*} (Σ_set : Set (LukPropForm I)) : LukPropForm I → Prop
  | ax  {φ}   : IsAxiom φ → Provable Σ_set φ
  | hyp {φ}   : φ ∈ Σ_set → Provable Σ_set φ
  | mp  {φ ψ} : Provable Σ_set φ → Provable Σ_set (.tsub ψ φ) → Provable Σ_set ψ

def Consistent {I : Type*} (Σ_set : Set (LukPropForm I)) : Prop :=
  ∃ φ, ¬ Provable Σ_set φ

end LukPropForm

end ContinuousFOL
