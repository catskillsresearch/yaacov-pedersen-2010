/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Corollary 9.12 with metric; vision.md page 25–26
-/
module

public import ContinuousFOL.Completeness.CompletenessMetric
public import ContinuousFOL.Group2Axioms.SoundnessMetric
public import ContinuousFOL.LanguageAndSemantics.FormulaOne

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Corollary 9.12 (Compactness — with complete metric). -/
theorem compactness_metric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    (∀ Γ₀ : Finset (Formula LM.toSignature),
      (↑Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ → CompletelySatisfiable (↑Γ₀)) →
    CompletelySatisfiable Γ := by
  intro hfin
  rw [← completeness_metric]
  by_contra hincons
  have hprov1 : ProvableMetricQ Γ (Formula.one LM.toSignature) := by
    by_contra hnot
    exact hincons ⟨Formula.one LM.toSignature, hnot⟩
  have hcompact_metric : ∀ {ψ}, ProvableMetricQ Γ ψ →
      ∃ Γ₀ : Finset (Formula LM.toSignature),
        (↑Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ ∧ ProvableMetricQ (↑Γ₀) ψ := by
    intro ψ hp
    induction hp with
    | ax hax => exact ⟨∅, Set.empty_subset _, .ax hax⟩
    | hyp hmem => exact ⟨{_}, Set.singleton_subset_iff.mpr hmem, .hyp (Finset.mem_singleton_self _)⟩
    | mp _ _ ih₁ ih₂ =>
      obtain ⟨Γ₁, h₁s, hp₁⟩ := ih₁
      obtain ⟨Γ₂, h₂s, hp₂⟩ := ih₂
      have hmono : ∀ {A B : Set (Formula LM.toSignature)} (hab : A ⊆ B) {χ},
          ProvableMetricQ A χ → ProvableMetricQ B χ := by
        intro A B hab χ hd
        induction hd with
        | ax ha => exact .ax ha
        | hyp hm => exact .hyp (hab hm)
        | mp _ _ i1 i2 => exact .mp i1 i2
      refine ⟨Γ₁ ∪ Γ₂, ?_, .mp (hmono ?_ hp₁) (hmono ?_ hp₂)⟩
      · rw [Finset.coe_union]; exact Set.union_subset h₁s h₂s
      · rw [Finset.coe_union]; exact Set.subset_union_left
      · rw [Finset.coe_union]; exact Set.subset_union_right
  obtain ⟨Γ₀, hsub, hprov₀⟩ := hcompact_metric hprov1
  obtain ⟨M, σ, hM⟩ := hfin Γ₀ hsub
  have hv := soundness_metric (↑Γ₀) (Formula.one LM.toSignature) hprov₀ M σ hM
  simp at hv

end ContinuousFOL
