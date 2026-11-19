/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Corollary 9.8; vision.md page 24–25
-/
module

public import ContinuousFOL.Completeness.CompletenessPre
public import ContinuousFOL.Completeness.DegreeOfTruth
public import ContinuousFOL.Completeness.DegreeOfProvability
public import ContinuousFOL.Completeness.ProvableTsubOfInconsistentAdjoin
public import ContinuousFOL.Group2Axioms.SoundnessPre
public import ContinuousFOL.Group1Axioms.DyadicCode.Val

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Corollary 9.8 (Pavelka-style Completeness): `φ°_Γ = φ^⊛_Γ`. -/
theorem pavelka_completeness_pre {L : Signature} (Γ : Set (Formula L))
    (hcons : ConsistentQ Γ) (φ : Formula L) :
    degreeOfTruthPre Γ φ = degreeOfProvabilityPre Γ φ := by
  unfold degreeOfTruthPre degreeOfProvabilityPre
  -- The set of truth values in models of `Γ` is nonempty (Theorem 9.5) and bounded by `1`.
  obtain ⟨M₀, σ₀, hM₀⟩ := (completeness_pre Γ).mp hcons
  have hTne : {r : ℝ | ∃ (M : PreStructure L) (σ : Var → M.Carrier),
      ModelsPre M σ Γ ∧ r = φ.eval M σ}.Nonempty := ⟨_, M₀, σ₀, hM₀, rfl⟩
  have hTbdd : BddAbove {r : ℝ | ∃ (M : PreStructure L) (σ : Var → M.Carrier),
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
    have hT0 : 0 ≤ sSup {r : ℝ | ∃ (M : PreStructure L) (σ : Var → M.Carrier),
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
    obtain ⟨M, σ, hM⟩ := (completeness_pre _).mp hcons'
    have hMΓ : ModelsPre M σ Γ := fun ψ hψ => hM ψ (Set.mem_union_left _ hψ)
    have h := hM _ (Set.mem_union_right _ (Set.mem_singleton _))
    simp only [Formula.eval, Formula.eval_dyadic, tsubR] at h
    have h1 := le_max_left (p.val - φ.eval M σ) 0
    have h2 := le_csSup hTbdd ⟨M, σ, hMΓ, rfl⟩
    linarith

theorem pavelka_completeness_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (hcons : ConsistentMetricQ Γ)
    (φ : Formula LM.toSignature) :
    degreeOfTruthComplete Γ φ = degreeOfProvabilityMetric Γ φ := by
  sorry

end ContinuousFOL
