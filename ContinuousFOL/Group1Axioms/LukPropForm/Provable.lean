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
inductive Provable {I : Type*} (hypSet : Set (LukPropForm I)) : LukPropForm I → Prop
  | ax  {φ}   : IsAxiom φ → Provable hypSet φ
  | hyp {φ}   : φ ∈ hypSet → Provable hypSet φ
  | mp  {φ ψ} : Provable hypSet φ → Provable hypSet (.tsub ψ φ) → Provable hypSet ψ

def Consistent {I : Type*} (hypSet : Set (LukPropForm I)) : Prop :=
  ∃ φ, ¬ Provable hypSet φ

end LukPropForm

end ContinuousFOL
