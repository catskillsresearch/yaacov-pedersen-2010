/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §7 FO provability without metric; vision.md page 14
-/
module

public import ContinuousFOL.Group2Axioms.BaseAxiomSchema
public import Mathlib.Data.Set.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Provability `Γ ⊢_Q φ` over a signature without metric (all generalizations of (A1)–(A9)). -/
inductive ProvableQ {L : Signature} (Γ : Set (Formula L)) : Formula L → Prop
  | ax  {xs : List Var} {ψ : Formula L} : BaseAxiomSchema ψ → ProvableQ Γ (Formula.genList xs ψ)
  | hyp {φ : Formula L} : φ ∈ Γ → ProvableQ Γ φ
  | mp  {φ ψ : Formula L} : ProvableQ Γ φ → ProvableQ Γ (.tsub ψ φ) → ProvableQ Γ ψ

end ContinuousFOL
