/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Definition 8.8 (metric) / Theorem 8.10 metric; vision.md pages 18–19
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.Essentials.MaximalConsistent
public import ContinuousFOL.Essentials.ProvableQMono

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

structure MaximalConsistentMetric {LM : MetricSignature}
    (Δ : Set (Formula LM.toSignature)) : Prop where
  consistent : ConsistentMetricQ Δ
  archimedean : ∀ φ,
    (∀ n : ℕ, ProvableMetricQ Δ (.tsub φ (Formula.pow2Neg LM.toSignature n))) → φ ∈ Δ
  comparable  : ∀ φ ψ, Formula.tsub φ ψ ∈ Δ ∨ Formula.tsub ψ φ ∈ Δ

/-- All generalizations of (A10)–(A14) (and (A1)–(A9)) as a set of formulae. -/
def metricAxiomSet (LM : MetricSignature) : Set (Formula LM.toSignature) :=
  {φ | ∃ (xs : List Var) (ψ : Formula LM.toSignature),
    MetricAxiomSchema (LM := LM) ψ ∧ φ = Formula.genList xs ψ}

/-- `Γ ⊢_Q φ` over a metric signature is `⊢_Q` from `Γ` plus the metric axioms. -/
lemma provableMetricQ_iff_provableQ {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) :
    ProvableMetricQ Γ φ ↔ ProvableQ (Γ ∪ metricAxiomSet LM) φ := by
  constructor
  · intro h
    induction h with
    | @ax xs ψ hax => exact .hyp (Or.inr ⟨xs, ψ, hax, rfl⟩)
    | hyp hmem => exact .hyp (Or.inl hmem)
    | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂
  · intro h
    induction h with
    | ax hax => exact .ax (.base hax)
    | hyp hmem =>
      rcases hmem with hmem | ⟨xs, ψ, hψ, rfl⟩
      · exact .hyp hmem
      · exact .ax hψ
    | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

/-- Theorem 8.10 metric variant. -/
theorem exists_maximal_consistent_metric {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (hcons : ConsistentMetricQ Γ) :
    ∃ Δ : Set (Formula LM.toSignature), Γ ⊆ Δ ∧ MaximalConsistentMetric Δ := by
  -- Reduce to Theorem 8.10 for `Γ ∪ {metric axioms}`.
  have hcons' : ConsistentQ (Γ ∪ metricAxiomSet LM) := by
    obtain ⟨φ, hφ⟩ := hcons
    exact ⟨φ, fun h => hφ ((provableMetricQ_iff_provableQ Γ φ).mpr h)⟩
  obtain ⟨Δ, hsub, hmc⟩ := exists_maximal_consistent hcons'
  have key : ∀ φ, ProvableMetricQ Δ φ ↔ ProvableQ Δ φ := fun φ =>
    (provableMetricQ_iff_provableQ Δ φ).trans
      ⟨fun h => h.mono (Set.union_subset subset_rfl fun _ hm => hsub (Or.inr hm)),
        fun h => h.mono Set.subset_union_left⟩
  refine ⟨Δ, fun _ h => hsub (Or.inl h), ⟨?_, ?_, hmc.comparable⟩⟩
  · obtain ⟨φ, hφ⟩ := hmc.consistent
    exact ⟨φ, fun h => hφ ((key φ).mp h)⟩
  · exact fun φ h => hmc.archimedean φ fun n => (key _).mp (h n)

end ContinuousFOL
