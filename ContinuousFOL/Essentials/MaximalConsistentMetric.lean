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
public import ContinuousFOL.Essentials.DeductionTheorem
public import ContinuousFOL.Essentials.InconsistentIffProvableOne

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


lemma consistentMetricQ_iff {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    ConsistentMetricQ Γ ↔ ConsistentQ (Γ ∪ metricAxiomSet LM) := by
  constructor
  · intro h
    obtain ⟨φ, hφ⟩ := h
    exact ⟨φ, fun h => hφ ((provableMetricQ_iff_provableQ Γ φ).mpr h)⟩
  · intro h
    obtain ⟨φ, hφ⟩ := h
    exact ⟨φ, fun h => hφ ((provableMetricQ_iff_provableQ Γ φ).mp h)⟩

lemma inconsistent_iff_provable_one_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) :
    ¬ ConsistentMetricQ Γ ↔ ProvableMetricQ Γ (Formula.one LM.toSignature) := by
  constructor
  · intro h
    by_contra hnot
    exact h ⟨Formula.one LM.toSignature, hnot⟩
  · intro h1 ⟨φ, hφ⟩
    exact hφ (ProvableMetricQ.mp h1 (ProvableMetricQ.of_provableQ (ProvableQ.tsub_one Γ φ)))

lemma ProvableMetricQ.ax0 {LM : MetricSignature} {Γ : Set (Formula LM.toSignature)}
    {ψ : Formula LM.toSignature} (h : MetricAxiomSchema (LM := LM) ψ) :
    ProvableMetricQ Γ ψ :=
  .ax (xs := []) h

lemma ProvableMetricQ.of_half {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} {φ : Formula LM.toSignature}
    (h : ProvableMetricQ Γ (.half φ)) : ProvableMetricQ Γ φ := by
  have hA6 : ProvableMetricQ Γ (.tsub (.tsub φ (.half φ)) (.half φ)) :=
    ProvableMetricQ.ax0 (.base (.A6 φ))
  exact ProvableMetricQ.mp h (ProvableMetricQ.mp h hA6)

lemma ProvableMetricQ.one_of_pow2Neg {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (n : ℕ)
    (h : ProvableMetricQ Γ (Formula.pow2Neg LM.toSignature n)) :
    ProvableMetricQ Γ (Formula.one LM.toSignature) := by
  induction n with
  | zero =>
    simpa [Formula.pow2Neg, DyadicCode.pow2Neg, Formula.dyadic] using h
  | succ n ih =>
    have hhalf : ProvableMetricQ Γ (.half (Formula.pow2Neg LM.toSignature n)) := by
      simpa [Formula.pow2Neg, DyadicCode.pow2Neg, Formula.dyadic] using h
    exact ih (ProvableMetricQ.of_half hhalf)

/-- A metrically maximal consistent set is maximal consistent in the sense of
    Definition 8.8 (plain `⊢_Q` is weaker, so the archimedean clause still holds). -/
lemma MaximalConsistentMetric.toMaximalConsistent {LM : MetricSignature}
    {Δ : Set (Formula LM.toSignature)} (hmc : MaximalConsistentMetric Δ) :
    MaximalConsistent Δ where
  consistent := by
    obtain ⟨φ, hφ⟩ := hmc.consistent
    exact ⟨φ, fun h => hφ (ProvableMetricQ.of_provableQ h)⟩
  archimedean := fun φ h =>
    hmc.archimedean φ (fun n => ProvableMetricQ.of_provableQ (h n))
  comparable := hmc.comparable

/-- Remark 8.9, metric variant: `φ ∈ Δ` iff `Δ ⊢_Q φ`. -/
lemma MaximalConsistentMetric.mem_iff_provable {LM : MetricSignature}
    {Δ : Set (Formula LM.toSignature)} (hmc : MaximalConsistentMetric Δ)
    (φ : Formula LM.toSignature) :
    φ ∈ Δ ↔ ProvableMetricQ Δ φ := by
  constructor
  · exact fun h => .hyp h
  · intro hprov
    exact hmc.archimedean φ fun n =>
      ProvableMetricQ.mp hprov
        (ProvableMetricQ.ax0 (.base (.A1 φ (Formula.pow2Neg LM.toSignature n))))

/-- Helper: metric Lemma 8.6 with the right-hand side packaged as
    `MaximalConsistentMetric`. -/
theorem maximal_in_consistent_extensions_iff_maximalConsistent_metric
    {LM : MetricSignature} {Γ Δ : Set (Formula LM.toSignature)}
    (_hΓ : ConsistentMetricQ Γ) :
    Maximal (fun Γ' => Γ ⊆ Γ' ∧ ConsistentMetricQ Γ') Δ ↔
      (Γ ⊆ Δ ∧ MaximalConsistentMetric Δ) := by
  constructor
  · rintro ⟨⟨hsub, hcons⟩, hmax⟩
    refine ⟨hsub, ⟨hcons, ?_, ?_⟩⟩
    · intro φ happrox
      have hcons' := consistent_adjoin_approx_metric hcons φ happrox
      have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hcons'⟩
        Set.subset_union_left
      exact heq (Set.mem_union_right _ (Set.mem_singleton φ))
    · intro φ ψ
      rcases consistent_adjoin_comparable_metric hcons φ ψ with hc₁ | hc₂
      · left
        have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hc₁⟩
          Set.subset_union_left
        exact heq (Set.mem_union_right _ (Set.mem_singleton _))
      · right
        have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hc₂⟩
          Set.subset_union_left
        exact heq (Set.mem_union_right _ (Set.mem_singleton _))
  · rintro ⟨hsub, hmc⟩
    refine ⟨⟨hsub, hmc.consistent⟩, ?_⟩
    rintro Γ' ⟨_hΓ'sub, hΓ'cons⟩ hΔΓ' φ hφ
    apply hmc.archimedean
    intro n
    rcases hmc.comparable φ (Formula.pow2Neg LM.toSignature n) with hle | hge
    · exact .hyp hle
    · exfalso
      have hpow : ProvableMetricQ Γ' (Formula.pow2Neg LM.toSignature n) :=
        ProvableMetricQ.mp (.hyp hφ) (.hyp (hΔΓ' hge))
      exact (inconsistent_iff_provable_one_metric Γ').mpr
        (ProvableMetricQ.one_of_pow2Neg n hpow) hΓ'cons

/-- Lemma 8.6 for a signature with a metric, with the paper's clauses (i)–(iii). -/
theorem maximal_in_consistent_extensions_iff_metric {LM : MetricSignature}
    {Γ Δ : Set (Formula LM.toSignature)} (hΓ : ConsistentMetricQ Γ) :
    Maximal (fun Γ' => Γ ⊆ Γ' ∧ ConsistentMetricQ Γ') Δ ↔
      (Γ ⊆ Δ ∧ ConsistentMetricQ Δ ∧
        (∀ φ, (∀ n : ℕ, ProvableMetricQ Δ
            (.tsub φ (Formula.pow2Neg LM.toSignature n))) → φ ∈ Δ) ∧
        (∀ φ ψ, Formula.tsub φ ψ ∈ Δ ∨ Formula.tsub ψ φ ∈ Δ)) := by
  constructor
  · intro h
    obtain ⟨hsub, hmc⟩ :=
      (maximal_in_consistent_extensions_iff_maximalConsistent_metric hΓ).mp h
    exact ⟨hsub, hmc.consistent, hmc.archimedean, hmc.comparable⟩
  · intro ⟨hsub, hcons, harch, hcomp⟩
    exact (maximal_in_consistent_extensions_iff_maximalConsistent_metric hΓ).mpr
      ⟨hsub, ⟨hcons, harch, hcomp⟩⟩

/-- Lemma 8.11 for a signature with a metric. -/
theorem maximal_consistent_sup_instantiate_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) {Δ : Set (Formula LM.toSignature)}
    (hmc : MaximalConsistentMetric Δ) (hΓΔ : Γ ⊆ Δ) (t : Term LM.toSignature)
    (p : DyadicCode) (x : Var) (φ : Formula LM.toSignature) :
    Formula.tsub (.sup x φ) (Formula.dyadic LM.toSignature p) ∈ Δ →
      ∃ φ' : Formula LM.toSignature, (φ ≡ᵐ φ') ∧
        Formula.tsub (φ'.freeSubst t x) (Formula.dyadic LM.toSignature p) ∈ Δ := by
  intro hmem
  obtain ⟨φ', heq, hmem'⟩ :=
    maximal_consistent_sup_instantiate Γ hmc.toMaximalConsistent hΓΔ t p x φ hmem
  exact ⟨φ', heq.toMetric, hmem'⟩

/-- Lemma 8.12 for a signature with a metric. -/
theorem maximal_consistent_sup_eq_inf_metric {LM : MetricSignature}
    {Γ Δ : Set (Formula LM.toSignature)} (hcons : ConsistentMetricQ Γ)
    (hmc : MaximalConsistentMetric Δ) (hΓΔ : Γ ⊆ Δ) (φ : Formula LM.toSignature) :
    sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
      Formula.tsub (Formula.dyadic LM.toSignature p) φ ∈ Δ} =
    sInf {r : ℝ | ∃ q : DyadicCode, r = q.val ∧
      Formula.tsub φ (Formula.dyadic LM.toSignature q) ∈ Δ} := by
  have hconsQ : ConsistentQ Γ := by
    obtain ⟨ψ, hψ⟩ := hcons
    exact ⟨ψ, fun h => hψ (ProvableMetricQ.of_provableQ h)⟩
  exact maximal_consistent_sup_eq_inf hconsQ hmc.toMaximalConsistent hΓΔ φ

end ContinuousFOL
