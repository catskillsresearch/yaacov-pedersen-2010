/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §7 Theorem 7.2 with metric; vision.md page 15
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.CompletelySatisfiable
public import ContinuousFOL.LanguageAndSemantics.FormulaOne
public import ContinuousFOL.Group2Axioms.SoundnessPre

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

lemma Term.eval_func_replaceArg_var {L : Signature} (M : PreStructure L)
    (σ : Var → M.Carrier) (f : L.Func) (v : Fin (L.funcArity f) → Var)
    (i : Fin (L.funcArity f)) (z : Var) :
    (Term.func f (replaceArg (fun j => .var (v j)) i (.var z))).eval M σ =
      M.funcInterp f (replaceArg (fun j => σ (v j)) i (σ z)) := by
  simp only [Term.eval]
  congr 1
  funext j
  simp only [replaceArg]
  split_ifs <;> rfl

lemma Formula.eval_rel_replaceArg_var {L : Signature} (M : PreStructure L)
    (σ : Var → M.Carrier) (P : L.Rel) (v : Fin (L.relArity P) → Var)
    (i : Fin (L.relArity P)) (z : Var) :
    (M.relInterp P fun j => (replaceArg (fun j => Term.var (v j)) i (Term.var z) j).eval M σ) =
      M.relInterp P (replaceArg (fun j => σ (v j)) i (σ z)) := by
  congr 1
  funext j
  simp only [replaceArg]
  split_ifs <;> rfl

lemma Formula.eval_dist {LM : MetricSignature} (M : MetricPreStructure LM)
    (σ : Var → M.Carrier) (t₀ t₁ : Term LM.toSignature) :
    (Formula.dist (LM := LM) t₀ t₁).eval M.toPreStructure σ =
      M.distVal (t₀.eval M.toPreStructure σ) (t₁.eval M.toPreStructure σ) := by
  rw [M.distVal_eq]
  simp only [Formula.dist, Formula.eval]
  congr 1
  funext i
  split_ifs <;> rfl

/-- `min(x, y) = 0` when one argument is `0` (real form of `minF`). -/
lemma tsubR.min_eq_zero {x y : ℝ} (hx : 0 ≤ x) (h : x = 0 ∨ y = 0) : x ∸ (x ∸ y) = 0 := by
  rcases h with h | h
  · subst h
    exact (tsubR.eq_zero_iff _ _).mpr (tsubR.nonneg _ _)
  · subst h
    refine (tsubR.eq_zero_iff _ _).mpr ?_
    simp [tsubR, hx]

/-- Each metric axiom (A1)–(A14) is valid in every continuous metric pre-structure. -/
lemma metricAxiom_eval_zero {LM : MetricSignature} {ψ : Formula LM.toSignature}
    (h : MetricAxiomSchema (LM := LM) ψ) (M : MetricPreStructure LM)
    (σ : Var → M.Carrier) : ψ.eval M.toPreStructure σ = 0 := by
  cases h with
  | base hb => exact baseAxiom_eval_zero hb _ σ
  | A10 x =>
    rw [Formula.eval_dist]
    exact M.dist_self _
  | A11 x y =>
    simp only [Formula.eval]
    rw [Formula.eval_dist, Formula.eval_dist, M.dist_symm]
    exact (tsubR.eq_zero_iff _ _).mpr le_rfl
  | A12 x y z =>
    have h0 := (Formula.eval_in_Icc M.toPreStructure σ
      (Formula.dist (LM := LM) (.var y) (.var z))).1
    rw [Formula.eval_dist] at h0
    simp only [Formula.eval]
    rw [Formula.eval_dist, Formula.eval_dist, Formula.eval_dist]
    refine (tsubR.eq_zero_iff _ _).mpr ((tsubR.sub_le_iff_add h0).mpr ?_)
    exact M.dist_triangle _ _ _
  | A13 f i ε r q v z w hε hε1 hr hq =>
    simp only [Formula.minF]
    refine tsubR.min_eq_zero (Formula.eval_in_Icc _ σ _).1 ?_
    simp only [Formula.eval]
    rw [Formula.eval_dist, Formula.eval_dist, Formula.eval_dyadic, Formula.eval_dyadic,
      Term.eval_func_replaceArg_var, Term.eval_func_replaceArg_var]
    simp only [Term.eval]
    by_cases hd : q.val ≤ M.distVal (σ z) (σ w)
    · exact Or.inl ((tsubR.eq_zero_iff _ _).mpr hd)
    · push Not at hd
      refine Or.inr ((tsubR.eq_zero_iff _ _).mpr ?_)
      have := M.func_unif_cont f i ε hε hε1 (fun j => σ (v j)) (σ z) (σ w)
        (lt_trans hd hq)
      linarith
  | A14 P i ε r q v z w hε hε1 hr hq =>
    simp only [Formula.minF]
    refine tsubR.min_eq_zero (Formula.eval_in_Icc _ σ _).1 ?_
    simp only [Formula.eval]
    rw [Formula.eval_dist, Formula.eval_dyadic, Formula.eval_dyadic,
      Formula.eval_rel_replaceArg_var, Formula.eval_rel_replaceArg_var]
    simp only [Term.eval]
    by_cases hd : q.val ≤ M.distVal (σ z) (σ w)
    · exact Or.inl ((tsubR.eq_zero_iff _ _).mpr hd)
    · push Not at hd
      refine Or.inr ((tsubR.eq_zero_iff _ _).mpr ?_)
      have := M.rel_unif_cont P i ε hε hε1 (fun j => σ (v j)) (σ z) (σ w)
        (lt_trans hd hq)
      linarith

/-- Theorem 7.2 (Soundness) over continuous `𝓛`-pre-structures, for a signature with
    a metric: `Γ ⊢_Q φ` implies `Γ ⊨_Q φ`. -/
theorem soundness_metric_pre.{u} {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) :
    ProvableMetricQ Γ φ → EntailsMetricPre.{u} Γ φ := by
  intro hprov
  induction hprov with
  | @ax xs ψ hax =>
    intro M σ _
    exact Formula.eval_genList_eq_zero M.toPreStructure xs ψ
      (fun σ' => metricAxiom_eval_zero hax M σ') σ
  | @hyp φ hmem =>
    intro M σ hM
    exact hM φ hmem
  | @mp φ ψ _hφ _himp ihφ ihimp =>
    intro M σ hM
    have hφ0 : φ.eval M.toPreStructure σ = 0 := ihφ M σ hM
    have himp0 : (Formula.tsub ψ φ).eval M.toPreStructure σ = 0 := ihimp M σ hM
    have hle : ψ.eval M.toPreStructure σ ≤ φ.eval M.toPreStructure σ := by
      have : ψ.eval M.toPreStructure σ ∸ φ.eval M.toPreStructure σ = 0 := by
        simpa [Formula.eval] using himp0
      exact (tsubR.eq_zero_iff _ _).mp this
    have hle0 : ψ.eval M.toPreStructure σ ≤ 0 := by simpa [hφ0] using hle
    exact le_antisymm hle0 (Formula.eval_in_Icc M.toPreStructure σ ψ).1

/-- Theorem 7.2 (Soundness) for signatures with a metric, restricted to complete
    structures (follows from `soundness_metric_pre`). -/
theorem soundness_metric.{u} {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) :
    ProvableMetricQ Γ φ → EntailsComplete.{u} Γ φ :=
  fun hprov M σ hM => soundness_metric_pre.{u} Γ φ hprov M.toMetricPreStructure σ hM

theorem satisfiable_consistent_metric_pre.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) :
    SatisfiableMetricPre.{u} Γ → ConsistentMetricQ Γ := by
  rintro ⟨M, σ, hM⟩
  refine ⟨Formula.one LM.toSignature, fun hprov => ?_⟩
  have hval := soundness_metric_pre Γ (Formula.one LM.toSignature) hprov M σ hM
  simp at hval

theorem satisfiable_consistent_metric.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) :
    CompletelySatisfiable.{u} Γ → ConsistentMetricQ Γ := by
  rintro ⟨M, σ, hM⟩
  exact satisfiable_consistent_metric_pre Γ ⟨M.toMetricPreStructure, σ, hM⟩

/-- Theorem 7.2 (Soundness) for a continuous signature with a metric, in the
    paper's form: (i) if `Γ ⊢_Q φ`, then `Γ ⊨_Q φ` (`Γ ⊨_QC φ`);
    (ii) if `Γ` is (completely) satisfiable, then `Γ` is consistent. -/
theorem soundness_metric_full.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    (ProvableMetricQ Γ φ → EntailsMetricPre.{u} Γ φ ∧ EntailsComplete.{u} Γ φ) ∧
    (SatisfiableMetricPre.{u} Γ → ConsistentMetricQ Γ) ∧
    (CompletelySatisfiable.{u} Γ → ConsistentMetricQ Γ) :=
  ⟨fun h => ⟨soundness_metric_pre Γ φ h, soundness_metric Γ φ h⟩,
    satisfiable_consistent_metric_pre Γ,
    satisfiable_consistent_metric Γ⟩

end ContinuousFOL
