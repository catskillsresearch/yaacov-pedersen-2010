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
  let ST := {r : ℝ | ∃ (M : PreStructure L) (σ : Var → M.Carrier),
    ModelsPre M σ Γ ∧ r = φ.eval M σ}
  let SP := {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ ProvableQ Γ (.tsub φ (Formula.dyadic L p))}
  obtain ⟨M₀, σ₀, hM₀⟩ := (completeness_pre Γ).mp hcons
  have hST_ne : ST.Nonempty := ⟨φ.eval M₀ σ₀, M₀, σ₀, hM₀, rfl⟩
  have hST_bdd : BddAbove ST := ⟨1, by rintro _ ⟨M, σ, _, rfl⟩; exact (φ.eval_in_Icc M σ).2⟩
  have hSP_ne : SP.Nonempty := by
    refine ⟨1, .one, DyadicCode.val_one.symm, ?_⟩
    sorry
  have hSP_bdd : BddBelow SP := ⟨0, by rintro _ ⟨p, rfl, _⟩; exact (p.val_mem_Icc).1⟩
  apply le_antisymm
  · -- Case (i): φ°_Γ ≤ φ^⊛_Γ
    apply le_csInf hSP_ne
    rintro _ ⟨p, rfl, hprov⟩
    apply csSup_le hST_ne
    rintro _ ⟨M, σ, hM, rfl⟩
    have hv := soundness_pre Γ _ hprov M σ hM
    simpa [Formula.eval, tsubR.eq_zero_iff] using hv
  · -- Case (ii): φ^⊛_Γ ≤ φ°_Γ
    by_contra hlt
    push_neg at hlt
    obtain ⟨p, hp₁, hp₂⟩ := DyadicCode.dense_in_Icc
      (le_trans (φ.eval_in_Icc M₀ σ₀).1 (le_csSup hST_bdd ⟨M₀, σ₀, hM₀, rfl⟩))
      (csInf_le hSP_bdd ⟨.one, DyadicCode.val_one.symm, by sorry⟩ |>.trans (by norm_num))
      hlt
    have hnprov : ¬ ProvableQ Γ (.tsub φ (Formula.dyadic L p)) := by
      intro hp
      have hle : degreeOfProvabilityPre Γ φ ≤ p.val := csInf_le hSP_bdd ⟨p, rfl, hp⟩
      linarith
    have hcons' : ConsistentQ (Γ ∪ {.tsub (Formula.dyadic L p) φ}) := by
      by_contra hinc
      exact hnprov (provable_tsub_of_inconsistent_adjoin Γ φ p hinc)
    obtain ⟨M, σ, hM⟩ := (completeness_pre _).mp hcons'
    have hMΓ : ModelsPre M σ Γ := fun ψ hψ => hM ψ (Set.mem_union_left _ hψ)
    have hpφ : (Formula.tsub (Formula.dyadic L p) φ).eval M σ = 0 :=
      hM _ (Set.mem_union_right _ (Set.mem_singleton _))
    simp [Formula.eval, tsubR.eq_zero_iff] at hpφ
    have hle_sup : φ.eval M σ ≤ degreeOfTruthPre Γ φ := le_csSup hST_bdd ⟨M, σ, hMΓ, rfl⟩
    linarith

theorem pavelka_completeness_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (hcons : ConsistentMetricQ Γ)
    (φ : Formula LM.toSignature) :
    degreeOfTruthComplete Γ φ = degreeOfProvabilityMetric Γ φ := by
  sorry

end ContinuousFOL
