/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Corollary 9.8; vision.md page 24–25
-/
module

public import ContinuousFOL.Completeness.CompletenessPre
public import ContinuousFOL.Completeness.CompletenessMetric
public import ContinuousFOL.Essentials.MaximalConsistentMetric
public import ContinuousFOL.Completeness.DegreeOfTruth
public import ContinuousFOL.Completeness.DegreeOfProvability
public import ContinuousFOL.Completeness.ProvableTsubOfInconsistentAdjoin
public import ContinuousFOL.Group2Axioms.SoundnessPre
public import ContinuousFOL.Group1Axioms.DyadicCode.Val

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Corollary 9.8 (Pavelka-style Completeness): `φ°_Γ = φ^⊛_Γ`.

    The paper states this for every `Γ ⊆ For(L)`, with no consistency hypothesis.
    Its written proof treats (i) soundness in any model and (ii) a consistent
    extension when `p < φ^⊛_Γ`. It is silent on inconsistent `Γ`, where there
    are no models and `φ°_Γ` is `sSup ∅`. The equality still holds because
    Mathlib's convention `Real.sSup_empty : sSup (∅ : Set ℝ) = 0` gives
    `φ°_Γ = 0`, while an inconsistent `Γ` proves `φ ∸ 0`, so `φ^⊛_Γ = 0`
    as well. (If one instead took `sSup ∅ = -∞`, the paper's unrestricted
    statement would fail in this case.) -/
theorem pavelka_completeness_pre {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) :
    degreeOfTruthPre.{0} Γ φ = degreeOfProvabilityPre Γ φ := by
  unfold degreeOfTruthPre degreeOfProvabilityPre
  by_cases hcons : ConsistentQ Γ
  swap
  · -- Inconsistent `Γ` (not discussed in the paper's proof of Corollary 9.8).
    -- No models, so `φ°_Γ = sSup ∅`. We use Mathlib's `Real.sSup_empty`,
    -- `sSup (∅ : Set ℝ) = 0`. Also `Γ ⊢ φ ∸ 0`, so `φ^⊛_Γ = 0`.
    have hall : ∀ ψ, ProvableQ Γ ψ := fun ψ => by
      by_contra h
      exact hcons ⟨ψ, h⟩
    have hT : {r : ℝ | ∃ (M : PreStructure.{0} L) (σ : Var → M.Carrier),
        ModelsPre M σ Γ ∧ r = φ.eval M σ} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨M, σ, hM, -⟩
      exact hcons (satisfiable_consistent_pre Γ ⟨M, σ, hM⟩)
    rw [hT, Real.sSup_empty]
    have h0 : (0 : ℝ) ∈ {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
        ProvableQ Γ (.tsub φ (Formula.dyadic L p))} :=
      ⟨.zero, DyadicCode.val_zero.symm, hall _⟩
    refine le_antisymm ?_ (csInf_le ⟨0, ?_⟩ h0)
    · refine le_csInf ⟨0, h0⟩ ?_
      rintro _ ⟨p, rfl, -⟩
      exact (DyadicCode.val_mem_Icc p).1
    · rintro _ ⟨p, rfl, -⟩
      exact (DyadicCode.val_mem_Icc p).1
  -- The set of truth values in models of `Γ` is nonempty (Theorem 9.5) and bounded by `1`.
  obtain ⟨M₀, σ₀, hM₀⟩ := completeness_pre Γ hcons
  have hTne : {r : ℝ | ∃ (M : PreStructure.{0} L) (σ : Var → M.Carrier),
      ModelsPre M σ Γ ∧ r = φ.eval M σ}.Nonempty := ⟨_, M₀, σ₀, hM₀, rfl⟩
  have hTbdd : BddAbove {r : ℝ | ∃ (M : PreStructure.{0} L) (σ : Var → M.Carrier),
      ModelsPre M σ Γ ∧ r = φ.eval M σ} := by
    refine ⟨1, ?_⟩
    rintro _ ⟨M, σ, -, rfl⟩
    exact (φ.eval_in_Icc M σ).2
  -- The set of provable dyadic bounds contains `1` and is bounded below by `0`.
  have hPne : {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
      ProvableQ Γ (.tsub φ (Formula.dyadic L p))}.Nonempty :=
    ⟨1, .one, DyadicCode.val_one.symm, ProvableQ.tsub_one Γ φ⟩
  have hPbdd : BddBelow {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
      ProvableQ Γ (.tsub φ (Formula.dyadic L p))} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl, -⟩
    exact (DyadicCode.val_mem_Icc p).1
  apply le_antisymm
  · -- (i) Soundness.
    apply csSup_le hTne
    rintro _ ⟨M, σ, hM, rfl⟩
    apply le_csInf hPne
    rintro _ ⟨p, rfl, hp⟩
    have h := soundness_pre Γ _ hp M σ hM
    simp only [Formula.eval, Formula.eval_dyadic, tsubR] at h
    have := le_max_left (φ.eval M σ - p.val) 0
    linarith
  · -- (ii) Completeness (Theorem 9.5).
    by_contra hlt
    push Not at hlt
    have hT0 : 0 ≤ sSup {r : ℝ | ∃ (M : PreStructure.{0} L) (σ : Var → M.Carrier),
        ModelsPre M σ Γ ∧ r = φ.eval M σ} :=
      le_trans (φ.eval_in_Icc M₀ σ₀).1 (le_csSup hTbdd ⟨M₀, σ₀, hM₀, rfl⟩)
    have hP1 : sInf {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
        ProvableQ Γ (.tsub φ (Formula.dyadic L p))} ≤ 1 :=
      csInf_le hPbdd ⟨.one, DyadicCode.val_one.symm, ProvableQ.tsub_one Γ φ⟩
    obtain ⟨p, hTp, hpP⟩ := DyadicCode.dense_in_Icc hT0 hP1 hlt
    have hnot : ¬ ProvableQ Γ (.tsub φ (Formula.dyadic L p)) := fun hp =>
      absurd (csInf_le hPbdd ⟨p, rfl, hp⟩) (not_le.mpr hpP)
    have hcons' : ConsistentQ (Γ ∪ {.tsub (Formula.dyadic L p) φ}) := by
      by_contra h
      exact hnot (provable_tsub_of_inconsistent_adjoin Γ φ p h)
    obtain ⟨M, σ, hM⟩ := completeness_pre _ hcons'
    have hMΓ : ModelsPre M σ Γ := fun ψ hψ => hM ψ (Set.mem_union_left _ hψ)
    have h := hM _ (Set.mem_union_right _ (Set.mem_singleton _))
    simp only [Formula.eval, Formula.eval_dyadic, tsubR] at h
    have h1 := le_max_left (p.val - φ.eval M σ) 0
    have h2 := le_csSup hTbdd ⟨M, σ, hMΓ, rfl⟩
    linarith

/-- Corollary 9.8 for a signature with a metric: `φ°_Γ = φ^⊛_Γ`, now over
    continuous `𝓛`-pre-structures and metric provability. As in the
    non-metric case, the paper does not discuss inconsistent `Γ`; the
    empty-sup identity is again Mathlib's `Real.sSup_empty : sSup (∅ : Set ℝ) = 0`. -/
theorem pavelka_completeness_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    degreeOfTruthMetric.{0} Γ φ = degreeOfProvabilityMetric Γ φ := by
  unfold degreeOfTruthMetric degreeOfProvabilityMetric
  have hone : ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature .one)) :=
    (provableMetricQ_iff_provableQ Γ _).mpr (ProvableQ.tsub_one _ φ)
  have hPbdd : BddBelow {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
      ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p))} := by
    refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl, -⟩
    exact (DyadicCode.val_mem_Icc p).1
  have hPne : {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
      ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p))}.Nonempty :=
    ⟨1, .one, DyadicCode.val_one.symm, hone⟩
  have hTbdd : BddAbove {r : ℝ | ∃ (M : MetricPreStructure.{0} LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ} := by
    refine ⟨1, ?_⟩
    rintro _ ⟨M, σ, -, rfl⟩
    exact (φ.eval_in_Icc M.toPreStructure σ).2
  by_cases hcons : ConsistentMetricQ Γ
  swap
  · -- Inconsistent `Γ` (not discussed in the paper's proof of Corollary 9.8).
    -- No metric pre-structure models, so `φ°_Γ = sSup ∅`. We use Mathlib's
    -- `Real.sSup_empty`, `sSup (∅ : Set ℝ) = 0`. Also `Γ ⊢ φ ∸ 0`, so `φ^⊛_Γ = 0`.
    have hall : ∀ ψ, ProvableMetricQ Γ ψ := fun ψ => by
      by_contra h
      exact hcons ⟨ψ, h⟩
    have hT : {r : ℝ | ∃ (M : MetricPreStructure.{0} LM) (σ : Var → M.Carrier),
        ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ} = ∅ := by
      ext r
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨M, σ, hM, -⟩
      exact hcons (satisfiable_consistent_metric_pre Γ ⟨M, σ, hM⟩)
    rw [hT, Real.sSup_empty]
    have h0 : (0 : ℝ) ∈ {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
        ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p))} :=
      ⟨.zero, DyadicCode.val_zero.symm, hall _⟩
    refine le_antisymm ?_ (csInf_le hPbdd h0)
    refine le_csInf ⟨0, h0⟩ ?_
    rintro _ ⟨p, rfl, -⟩
    exact (DyadicCode.val_mem_Icc p).1
  -- Consistent `Γ`: a metric pre-structure model exists
  -- (`metric_prestructure_model_of_consistent`, the first step of Theorem 9.5).
  obtain ⟨M₀, σ₀, hM₀⟩ := metric_prestructure_model_of_consistent hcons
  have hTne : {r : ℝ | ∃ (M : MetricPreStructure.{0} LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}.Nonempty :=
    ⟨_, M₀, σ₀, hM₀, rfl⟩
  apply le_antisymm
  · -- (i) Soundness.
    apply csSup_le hTne
    rintro _ ⟨M, σ, hM, rfl⟩
    apply le_csInf hPne
    rintro _ ⟨p, rfl, hp⟩
    have h := soundness_metric_pre Γ _ hp M σ hM
    simp only [Formula.eval, Formula.eval_dyadic, tsubR] at h
    have := le_max_left (φ.eval M.toPreStructure σ - p.val) 0
    linarith
  · -- (ii) Completeness (Theorem 9.5, via a metric pre-structure model).
    by_contra hlt
    push Not at hlt
    have hT0 : 0 ≤ sSup {r : ℝ | ∃ (M : MetricPreStructure.{0} LM) (σ : Var → M.Carrier),
        ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ} :=
      le_trans (φ.eval_in_Icc M₀.toPreStructure σ₀).1 (le_csSup hTbdd ⟨M₀, σ₀, hM₀, rfl⟩)
    have hP1 : sInf {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
        ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p))} ≤ 1 :=
      csInf_le hPbdd ⟨.one, DyadicCode.val_one.symm, hone⟩
    obtain ⟨p, hTp, hpP⟩ := DyadicCode.dense_in_Icc hT0 hP1 hlt
    have hnot : ¬ ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p)) := fun hp =>
      absurd (csInf_le hPbdd ⟨p, rfl, hp⟩) (not_le.mpr hpP)
    have hcons' : ConsistentMetricQ (Γ ∪ {.tsub (Formula.dyadic LM.toSignature p) φ}) := by
      by_contra h
      exact hnot (provable_tsub_of_inconsistent_adjoin_metric Γ φ p h)
    obtain ⟨M, σ, hM⟩ := metric_prestructure_model_of_consistent hcons'
    have hMΓ : ModelsPre M.toPreStructure σ Γ := fun ψ hψ => hM ψ (Set.mem_union_left _ hψ)
    have h := hM _ (Set.mem_union_right _ (Set.mem_singleton _))
    simp only [Formula.eval, Formula.eval_dyadic, tsubR] at h
    have h1 := le_max_left (p.val - φ.eval M.toPreStructure σ) 0
    have h2 := le_csSup hTbdd ⟨M, σ, hMΓ, rfl⟩
    linarith

end ContinuousFOL
