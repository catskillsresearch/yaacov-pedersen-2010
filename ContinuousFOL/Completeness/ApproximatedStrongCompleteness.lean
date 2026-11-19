/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Corollary 9.6; vision.md page 23–24
-/
module

public import ContinuousFOL.Completeness.CompletenessPre
public import ContinuousFOL.Completeness.CompletenessMetric
public import ContinuousFOL.Completeness.ProvableTsubOfInconsistentAdjoin
public import ContinuousFOL.Group2Axioms.SoundnessPre
public import ContinuousFOL.Group2Axioms.SoundnessMetric
public import ContinuousFOL.Group1Axioms.DyadicCode.Val

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Corollary 9.6 (Approximated Strong Completeness — without metric). -/
theorem approximated_strong_completeness_pre {L : Signature}
    (Γ : Set (Formula L)) (φ : Formula L) :
    EntailsPre Γ φ ↔ ∀ n : ℕ, ProvableQ Γ (.tsub φ (Formula.pow2Neg L n)) := by
  constructor
  · intro hent n
    apply provable_tsub_of_inconsistent_adjoin Γ φ (.pow2Neg n)
    rw [completeness_pre_iff]
    rintro ⟨M, σ, hM⟩
    have hφ0 : φ.eval M σ = 0 := hent M σ (fun ψ hψ => hM ψ (Set.mem_union_left _ hψ))
    have hmem : Formula.tsub (Formula.dyadic L (.pow2Neg n)) φ ∈
        Γ ∪ {Formula.tsub (Formula.dyadic L (.pow2Neg n)) φ} :=
      Set.mem_union_right _ (Set.mem_singleton _)
    have hval := hM _ hmem
    -- `p ∸ φ` evaluates to a positive power of 1/2, contradicting models-to-0.
    simp [Formula.eval, hφ0, DyadicCode.val_pow2Neg] at hval
  · intro hprov M σ hM
    have hle : ∀ n : ℕ, φ.eval M σ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
      intro n
      have hv := soundness_pre Γ _ (hprov n) M σ hM
      simpa [Formula.eval, Formula.pow2Neg, DyadicCode.val_pow2Neg] using hv
    have hnonneg := (φ.eval_in_Icc M σ).1
    by_contra hne
    have hpos : 0 < φ.eval M σ := lt_of_le_of_ne hnonneg (Ne.symm hne)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (2 : ℝ) ^ (-(n : ℤ)) < φ.eval M σ := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨n, by simpa [zpow_neg, zpow_natCast, one_div, inv_pow] using hn⟩
    linarith [hle n]

/-- Corollary 9.6, metric pre-structure clause: `Γ ⊨_Q φ` iff
    `Γ ⊢_Q φ ∸ 2^{-n}` for all `n`. -/
theorem approximated_strong_completeness_metric_pre {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    EntailsMetricPre Γ φ ↔
      ∀ n : ℕ, ProvableMetricQ Γ (.tsub φ (Formula.pow2Neg LM.toSignature n)) := by
  constructor
  · intro hent n
    apply provable_tsub_of_inconsistent_adjoin_metric Γ φ (.pow2Neg n)
    intro hcons
    obtain ⟨M, σ, hM⟩ := metric_prestructure_model_of_consistent hcons
    have hφ0 : φ.eval M.toPreStructure σ = 0 :=
      hent M σ (fun ψ hψ => hM ψ (Set.mem_union_left _ hψ))
    have hmem : Formula.tsub (Formula.dyadic LM.toSignature (.pow2Neg n)) φ ∈
        Γ ∪ {Formula.tsub (Formula.dyadic LM.toSignature (.pow2Neg n)) φ} :=
      Set.mem_union_right _ (Set.mem_singleton _)
    have hval := hM _ hmem
    simp [Formula.eval, hφ0, DyadicCode.val_pow2Neg] at hval
  · intro hprov M σ hM
    have hle : ∀ n : ℕ, φ.eval M.toPreStructure σ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
      intro n
      have hv := soundness_metric_pre Γ _ (hprov n) M σ hM
      simpa [Formula.eval, Formula.pow2Neg, DyadicCode.val_pow2Neg] using hv
    have hnonneg := (φ.eval_in_Icc M.toPreStructure σ).1
    by_contra hne
    have hpos : 0 < φ.eval M.toPreStructure σ := lt_of_le_of_ne hnonneg (Ne.symm hne)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (2 : ℝ) ^ (-(n : ℤ)) < φ.eval M.toPreStructure σ := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨n, by simpa [zpow_neg, zpow_natCast, one_div, inv_pow] using hn⟩
    linarith [hle n]

/-- Corollary 9.6, `⊨_QC` clause (the paper's "moreover"). -/
theorem approximated_strong_completeness_metric_complete {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    EntailsComplete Γ φ ↔
      ∀ n : ℕ, ProvableMetricQ Γ (.tsub φ (Formula.pow2Neg LM.toSignature n)) := by
  constructor
  · intro hent n
    apply provable_tsub_of_inconsistent_adjoin_metric Γ φ (.pow2Neg n)
    rw [completeness_metric_iff]
    rintro ⟨M, σ, hM⟩
    have hφ0 : φ.eval M.toPreStructure σ = 0 :=
      hent M σ (fun ψ hψ => hM ψ (Set.mem_union_left _ hψ))
    have hmem : Formula.tsub (Formula.dyadic LM.toSignature (.pow2Neg n)) φ ∈
        Γ ∪ {Formula.tsub (Formula.dyadic LM.toSignature (.pow2Neg n)) φ} :=
      Set.mem_union_right _ (Set.mem_singleton _)
    have hval := hM _ hmem
    simp [Formula.eval, hφ0, DyadicCode.val_pow2Neg] at hval
  · intro hprov M σ hM
    have hle : ∀ n : ℕ, φ.eval M.toPreStructure σ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
      intro n
      have hv := soundness_metric Γ _ (hprov n) M σ hM
      simpa [Formula.eval, Formula.pow2Neg, DyadicCode.val_pow2Neg] using hv
    have hnonneg := (φ.eval_in_Icc M.toPreStructure σ).1
    by_contra hne
    have hpos : 0 < φ.eval M.toPreStructure σ := lt_of_le_of_ne hnonneg (Ne.symm hne)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (2 : ℝ) ^ (-(n : ℤ)) < φ.eval M.toPreStructure σ := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (1 / 2 : ℝ) < 1)
      exact ⟨n, by simpa [zpow_neg, zpow_natCast, one_div, inv_pow] using hn⟩
    linarith [hle n]

/-- Corollary 9.6 for a signature with a metric: `Γ ⊨_Q φ` if and only if
    `Γ ⊢_Q φ ∸ 2^{-n}` for all `n`, and moreover `Γ ⊨_QC φ` if and only if
    `Γ ⊢_Q φ ∸ 2^{-n}` for all `n`. -/
theorem approximated_strong_completeness_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    (EntailsMetricPre Γ φ ↔
      ∀ n : ℕ, ProvableMetricQ Γ (.tsub φ (Formula.pow2Neg LM.toSignature n))) ∧
    (EntailsComplete Γ φ ↔
      ∀ n : ℕ, ProvableMetricQ Γ (.tsub φ (Formula.pow2Neg LM.toSignature n))) :=
  ⟨approximated_strong_completeness_metric_pre Γ φ,
    approximated_strong_completeness_metric_complete Γ φ⟩

end ContinuousFOL
