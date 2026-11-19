/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.7 (i); vision.md page 24
-/
module

public import ContinuousFOL.LanguageAndSemantics.ModelsPre
public import ContinuousFOL.LanguageAndSemantics.ContinuousStructure
public import ContinuousFOL.SubstitutionAndCompletions.ExistsMetricCompletion
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Definition 9.7 (i): Degree of truth `φ°_Γ` with respect to `Γ`, for a continuous
    signature (possibly without a metric). This is
    `sup { 𝔐(φ, σ) : (𝔐, σ) ⊨ Γ }`, the supremum ranging over continuous
    `𝓛`-pre-structures. -/
def degreeOfTruthPre {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) : ℝ :=
  sSup {r : ℝ | ∃ (M : PreStructure L) (σ : Var → M.Carrier),
    ModelsPre M σ Γ ∧ r = φ.eval M σ}

/-- Definition 9.7 (i) when `𝓛` has a metric: the same supremum
    `φ°_Γ := sup { 𝔐(φ, σ) : (𝔐, σ) ⊨ Γ }`, ranging over continuous
    `𝓛`-pre-structures (not merely complete `𝓛`-structures). -/
def degreeOfTruthMetric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : ℝ :=
  sSup {r : ℝ | ∃ (M : MetricPreStructure LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}

/-- Helper (not a paper definition): the supremum of `𝔐(φ, σ)` restricted to complete
    continuous `𝓛`-structures. Agrees with `degreeOfTruthMetric` by Theorem 6.9;
    see `degreeOfTruthMetric_eq_complete`. -/
def degreeOfTruthComplete {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : ℝ :=
  sSup {r : ℝ | ∃ (M : ContinuousStructure LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}

/-- The paper's degree of truth over metric pre-structures equals the helper supremum
    over complete structures, by Theorem 6.9 (an elementary embedding into a completion
    preserves the value of `φ`). -/
theorem degreeOfTruthMetric_eq_complete {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    degreeOfTruthMetric Γ φ = degreeOfTruthComplete Γ φ := by
  unfold degreeOfTruthMetric degreeOfTruthComplete
  congr 1
  ext r
  constructor
  · rintro ⟨M, σ, hM, rfl⟩
    obtain ⟨Mhat, ⟨e⟩⟩ := exists_metric_completion M
    refine ⟨Mhat, e.toFun ∘ σ, ?_, e.map_eval σ φ⟩
    intro ψ hψ
    rw [← e.map_eval σ ψ]
    exact hM ψ hψ
  · rintro ⟨M, σ, hM, rfl⟩
    exact ⟨M.toMetricPreStructure, σ, hM, rfl⟩

end ContinuousFOL
