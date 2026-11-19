/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §7 FO provability with metric; vision.md page 14
-/
module

public import ContinuousFOL.Group2Axioms.MetricAxiomSchema
public import Mathlib.Data.Set.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Provability `Γ ⊢_Q φ` over a metric signature (all generalizations of (A1)–(A14)). -/
inductive ProvableMetricQ {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    Formula LM.toSignature → Prop
  | ax  {xs : List Var} {ψ : Formula LM.toSignature} :
      MetricAxiomSchema (LM := LM) ψ → ProvableMetricQ Γ (Formula.genList xs ψ)
  | hyp {φ : Formula LM.toSignature} : φ ∈ Γ → ProvableMetricQ Γ φ
  | mp  {φ ψ : Formula LM.toSignature} :
      ProvableMetricQ Γ φ → ProvableMetricQ Γ (.tsub ψ φ) → ProvableMetricQ Γ ψ

end ContinuousFOL
