/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: helper — satisfiability, entailment, degree of truth, and complete
theories are independent of the type universe of the underlying set.
-/
module

public import ContinuousFOL.Completeness.CompletenessPre
public import ContinuousFOL.Completeness.CompletenessMetric
public import ContinuousFOL.Completeness.DegreeOfTruth
public import ContinuousFOL.Completeness.IsCompleteTheory
public import ContinuousFOL.LanguageAndSemantics.UliftPreStructure
public import ContinuousFOL.LanguageAndSemantics.EntailsPre
public import ContinuousFOL.LanguageAndSemantics.CompletelySatisfiable
public import ContinuousFOL.Group1Axioms.DyadicCode.Val
public import ContinuousFOL.Introduction.TsubR

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-! ### Degree of truth is independent of the universe -/

lemma degreeOfTruthPre_nonneg.{u} {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) :
    0 ≤ degreeOfTruthPre.{u} Γ φ := by
  unfold degreeOfTruthPre
  set S := {r : ℝ | ∃ (M : PreStructure.{u} L) (σ : Var → M.Carrier),
    ModelsPre M σ Γ ∧ r = φ.eval M σ}
  by_cases hne : S.Nonempty
  · obtain ⟨r, M, σ, hM, hr⟩ := hne
    have hbdd : BddAbove S := ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N τ).2⟩
    have : 0 ≤ r := by rw [hr]; exact (φ.eval_in_Icc M σ).1
    exact le_trans this (le_csSup hbdd ⟨M, σ, hM, hr⟩)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]

lemma degreeOfTruthMetric_nonneg.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    0 ≤ degreeOfTruthMetric.{u} Γ φ := by
  unfold degreeOfTruthMetric
  set S := {r : ℝ | ∃ (M : MetricPreStructure.{u} LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}
  by_cases hne : S.Nonempty
  · obtain ⟨r, M, σ, hM, hr⟩ := hne
    have hbdd : BddAbove S :=
      ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N.toPreStructure τ).2⟩
    have : 0 ≤ r := by rw [hr]; exact (φ.eval_in_Icc M.toPreStructure σ).1
    exact le_trans this (le_csSup hbdd ⟨M, σ, hM, hr⟩)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]

lemma degreeOfTruthComplete_nonneg.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    0 ≤ degreeOfTruthComplete.{u} Γ φ := by
  unfold degreeOfTruthComplete
  set S := {r : ℝ | ∃ (M : ContinuousStructure.{u} LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}
  by_cases hne : S.Nonempty
  · obtain ⟨r, M, σ, hM, hr⟩ := hne
    have hbdd : BddAbove S :=
      ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N.toPreStructure τ).2⟩
    have : 0 ≤ r := by rw [hr]; exact (φ.eval_in_Icc M.toPreStructure σ).1
    exact le_trans this (le_csSup hbdd ⟨M, σ, hM, hr⟩)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]

theorem degreeOfTruthPre_eq_universe.{u} {L : Signature}
    (Γ : Set (Formula L)) (φ : Formula L) :
    degreeOfTruthPre.{u} Γ φ = degreeOfTruthPre.{0} Γ φ := by
  unfold degreeOfTruthPre
  set Su := {r : ℝ | ∃ (M : PreStructure.{u} L) (σ : Var → M.Carrier),
    ModelsPre M σ Γ ∧ r = φ.eval M σ}
  set S0 := {r : ℝ | ∃ (M : PreStructure.{0} L) (σ : Var → M.Carrier),
    ModelsPre M σ Γ ∧ r = φ.eval M σ}
  have hbdd0 : BddAbove S0 :=
    ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N τ).2⟩
  have hbddu : BddAbove Su :=
    ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N τ).2⟩
  apply le_antisymm
  · by_cases hne : Su.Nonempty
    · apply csSup_le hne
      rintro _ ⟨M, σ, hM, rfl⟩
      set r := φ.eval M σ
      have hr0 := (φ.eval_in_Icc M σ).1
      have hr1 := (φ.eval_in_Icc M σ).2
      by_cases hr : r = 0
      · convert (degreeOfTruthPre_nonneg.{0} Γ φ); rfl
      · have hpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
        have h0ne : S0.Nonempty := by
          obtain ⟨N, τ, hN⟩ :=
            (satisfiablePre_iff_universe.{u} Γ).mp ⟨M, σ, hM⟩
          exact ⟨_, N, τ, hN, rfl⟩
        by_contra hlt
        have hlt' : sSup S0 < r := lt_of_not_ge hlt
        have hT0 : 0 ≤ sSup S0 := degreeOfTruthPre_nonneg.{0} Γ φ
        obtain ⟨p, hp0, hpr⟩ := DyadicCode.dense_in_Icc hT0 hr1 hlt'
        have hsat : SatisfiablePre.{u} (Γ ∪ {Formula.tsub (Formula.dyadic L p) φ}) := by
          refine ⟨M, σ, ?_⟩
          intro ψ hψ
          simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
          rcases hψ with hΓ | rfl
          · exact hM ψ hΓ
          · exact (tsubR.eq_zero_iff _ _).mpr (by
              simpa [Formula.eval, Formula.eval_dyadic] using hpr.le)
        obtain ⟨N, τ, hN⟩ := (satisfiablePre_iff_universe.{u} _).mp hsat
        have hNΓ : ModelsPre N τ Γ := fun ψ hψ => hN ψ (Set.mem_union_left _ hψ)
        have hpφ := hN _ (Set.mem_union_right _ (Set.mem_singleton _))
        have hple : p.val ≤ φ.eval N τ :=
          (tsubR.eq_zero_iff _ _).mp (by
            simpa [Formula.eval, Formula.eval_dyadic] using hpφ)
        have : p.val ≤ sSup S0 :=
          le_trans hple (le_csSup hbdd0 ⟨N, τ, hNΓ, rfl⟩)
        linarith
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      convert (degreeOfTruthPre_nonneg.{0} Γ φ); rfl
  · by_cases hne : S0.Nonempty
    · apply csSup_le_csSup hbddu hne
      rintro _ ⟨M, σ, hM, rfl⟩
      refine ⟨PreStructure.ulift.{u} M, uliftUp.{u} M ∘ σ, ?_,
        (Formula.eval_ulift.{u} M σ φ).symm⟩
      exact (ModelsPre.ulift_iff).mpr hM
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      convert (degreeOfTruthPre_nonneg.{u} Γ φ); rfl

theorem degreeOfTruthMetric_eq_universe.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    degreeOfTruthMetric.{u} Γ φ = degreeOfTruthMetric.{0} Γ φ := by
  unfold degreeOfTruthMetric
  set Su := {r : ℝ | ∃ (M : MetricPreStructure.{u} LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}
  set S0 := {r : ℝ | ∃ (M : MetricPreStructure.{0} LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}
  have hbdd0 : BddAbove S0 :=
    ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N.toPreStructure τ).2⟩
  have hbddu : BddAbove Su :=
    ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N.toPreStructure τ).2⟩
  apply le_antisymm
  · by_cases hne : Su.Nonempty
    · apply csSup_le hne
      rintro _ ⟨M, σ, hM, rfl⟩
      set r := φ.eval M.toPreStructure σ
      have hr0 := (φ.eval_in_Icc M.toPreStructure σ).1
      have hr1 := (φ.eval_in_Icc M.toPreStructure σ).2
      by_cases hr : r = 0
      · convert (degreeOfTruthMetric_nonneg.{0} Γ φ); rfl
      · have h0ne : S0.Nonempty := by
          obtain ⟨N, τ, hN⟩ :=
            (satisfiableMetricPre_iff_universe.{u} Γ).mp ⟨M, σ, hM⟩
          exact ⟨_, N, τ, hN, rfl⟩
        by_contra hlt
        have hlt' : sSup S0 < r := lt_of_not_ge hlt
        have hT0 : 0 ≤ sSup S0 := degreeOfTruthMetric_nonneg.{0} Γ φ
        obtain ⟨p, hp0, hpr⟩ := DyadicCode.dense_in_Icc hT0 hr1 hlt'
        have hsat : SatisfiableMetricPre.{u}
            (Γ ∪ {Formula.tsub (Formula.dyadic LM.toSignature p) φ}) := by
          refine ⟨M, σ, ?_⟩
          intro ψ hψ
          simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
          rcases hψ with hΓ | rfl
          · exact hM ψ hΓ
          · exact (tsubR.eq_zero_iff _ _).mpr (by
              simpa [Formula.eval, Formula.eval_dyadic] using hpr.le)
        obtain ⟨N, τ, hN⟩ := (satisfiableMetricPre_iff_universe.{u} _).mp hsat
        have hNΓ : ModelsPre N.toPreStructure τ Γ :=
          fun ψ hψ => hN ψ (Set.mem_union_left _ hψ)
        have hpφ := hN _ (Set.mem_union_right _ (Set.mem_singleton _))
        have hple : p.val ≤ φ.eval N.toPreStructure τ :=
          (tsubR.eq_zero_iff _ _).mp (by
            simpa [Formula.eval, Formula.eval_dyadic] using hpφ)
        have : p.val ≤ sSup S0 :=
          le_trans hple (le_csSup hbdd0 ⟨N, τ, hNΓ, rfl⟩)
        linarith
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      convert (degreeOfTruthMetric_nonneg.{0} Γ φ); rfl
  · by_cases hne : S0.Nonempty
    · apply csSup_le_csSup hbddu hne
      rintro _ ⟨M, σ, hM, rfl⟩
      refine ⟨MetricPreStructure.ulift.{u} M, uliftUp.{u} M.toPreStructure ∘ σ, ?_,
        (Formula.eval_ulift.{u} M.toPreStructure σ φ).symm⟩
      exact (ModelsPre.ulift_iff (M := M.toPreStructure) (σ := σ)).mpr hM
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      convert (degreeOfTruthMetric_nonneg.{u} Γ φ); rfl

theorem degreeOfTruthComplete_eq_universe.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    degreeOfTruthComplete.{u} Γ φ = degreeOfTruthComplete.{0} Γ φ := by
  unfold degreeOfTruthComplete
  set Su := {r : ℝ | ∃ (M : ContinuousStructure.{u} LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}
  set S0 := {r : ℝ | ∃ (M : ContinuousStructure.{0} LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}
  have hbdd0 : BddAbove S0 :=
    ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N.toPreStructure τ).2⟩
  have hbddu : BddAbove Su :=
    ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N.toPreStructure τ).2⟩
  apply le_antisymm
  · by_cases hne : Su.Nonempty
    · apply csSup_le hne
      rintro _ ⟨M, σ, hM, rfl⟩
      set r := φ.eval M.toPreStructure σ
      have hr0 := (φ.eval_in_Icc M.toPreStructure σ).1
      have hr1 := (φ.eval_in_Icc M.toPreStructure σ).2
      by_cases hr : r = 0
      · convert (degreeOfTruthComplete_nonneg.{0} Γ φ); rfl
      · have h0ne : S0.Nonempty := by
          obtain ⟨N, τ, hN⟩ :=
            (completelySatisfiable_iff_universe.{u} Γ).mp ⟨M, σ, hM⟩
          exact ⟨_, N, τ, hN, rfl⟩
        by_contra hlt
        have hlt' : sSup S0 < r := lt_of_not_ge hlt
        have hT0 : 0 ≤ sSup S0 := degreeOfTruthComplete_nonneg.{0} Γ φ
        obtain ⟨p, hp0, hpr⟩ := DyadicCode.dense_in_Icc hT0 hr1 hlt'
        have hsat : CompletelySatisfiable.{u}
            (Γ ∪ {Formula.tsub (Formula.dyadic LM.toSignature p) φ}) := by
          refine ⟨M, σ, ?_⟩
          intro ψ hψ
          simp only [Set.mem_union, Set.mem_singleton_iff] at hψ
          rcases hψ with hΓ | rfl
          · exact hM ψ hΓ
          · exact (tsubR.eq_zero_iff _ _).mpr (by
              simpa [Formula.eval, Formula.eval_dyadic] using hpr.le)
        obtain ⟨N, τ, hN⟩ := (completelySatisfiable_iff_universe.{u} _).mp hsat
        have hNΓ : ModelsPre N.toPreStructure τ Γ :=
          fun ψ hψ => hN ψ (Set.mem_union_left _ hψ)
        have hpφ := hN _ (Set.mem_union_right _ (Set.mem_singleton _))
        have hple : p.val ≤ φ.eval N.toPreStructure τ :=
          (tsubR.eq_zero_iff _ _).mp (by
            simpa [Formula.eval, Formula.eval_dyadic] using hpφ)
        have : p.val ≤ sSup S0 :=
          le_trans hple (le_csSup hbdd0 ⟨N, τ, hNΓ, rfl⟩)
        linarith
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      convert (degreeOfTruthComplete_nonneg.{0} Γ φ); rfl
  · by_cases hne : S0.Nonempty
    · apply csSup_le_csSup hbddu hne
      rintro _ ⟨M, σ, hM, rfl⟩
      refine ⟨ContinuousStructure.ulift.{u} M, uliftUp.{u} M.toPreStructure ∘ σ, ?_,
        (Formula.eval_ulift.{u} M.toPreStructure σ φ).symm⟩
      exact (ModelsPre.ulift_iff (M := M.toPreStructure) (σ := σ)).mpr hM
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      convert (degreeOfTruthComplete_nonneg.{u} Γ φ); rfl

/-! ### Entailment is independent of the universe -/

lemma entailsPre_iff_degree_eq_zero.{u} {L : Signature}
    (Γ : Set (Formula L)) (φ : Formula L) :
    EntailsPre.{u} Γ φ ↔ degreeOfTruthPre.{u} Γ φ = 0 := by
  constructor
  · intro h
    unfold degreeOfTruthPre
    set S := {r : ℝ | ∃ (M : PreStructure.{u} L) (σ : Var → M.Carrier),
      ModelsPre M σ Γ ∧ r = φ.eval M σ}
    by_cases hne : S.Nonempty
    · have hS : S = {0} := by
        ext r
        constructor
        · rintro ⟨M, σ, hM, rfl⟩
          simp [h M σ hM]
        · rintro rfl
          obtain ⟨_, M, σ, hM, _⟩ := hne
          exact ⟨M, σ, hM, (h M σ hM).symm⟩
      rw [hS, csSup_singleton]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
  · intro hDOT M σ hM
    have hbdd : BddAbove {r : ℝ | ∃ (N : PreStructure.{u} L) (τ : Var → N.Carrier),
        ModelsPre N τ Γ ∧ r = φ.eval N τ} :=
      ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N τ).2⟩
    have hle : φ.eval M σ ≤ 0 := by
      have := le_csSup hbdd ⟨M, σ, hM, rfl⟩
      rw [degreeOfTruthPre] at hDOT
      rwa [hDOT] at this
    exact le_antisymm hle (φ.eval_in_Icc M σ).1

lemma entailsMetricPre_iff_degree_eq_zero.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    EntailsMetricPre.{u} Γ φ ↔ degreeOfTruthMetric.{u} Γ φ = 0 := by
  constructor
  · intro h
    unfold degreeOfTruthMetric
    set S := {r : ℝ | ∃ (M : MetricPreStructure.{u} LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}
    by_cases hne : S.Nonempty
    · have hS : S = {0} := by
        ext r
        constructor
        · rintro ⟨M, σ, hM, rfl⟩
          simp [h M σ hM]
        · rintro rfl
          obtain ⟨_, M, σ, hM, _⟩ := hne
          exact ⟨M, σ, hM, (h M σ hM).symm⟩
      rw [hS, csSup_singleton]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
  · intro hDOT M σ hM
    have hbdd : BddAbove {r : ℝ | ∃ (N : MetricPreStructure.{u} LM) (τ : Var → N.Carrier),
        ModelsPre N.toPreStructure τ Γ ∧ r = φ.eval N.toPreStructure τ} :=
      ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N.toPreStructure τ).2⟩
    have hle : φ.eval M.toPreStructure σ ≤ 0 := by
      have := le_csSup hbdd ⟨M, σ, hM, rfl⟩
      rw [degreeOfTruthMetric] at hDOT
      rwa [hDOT] at this
    exact le_antisymm hle (φ.eval_in_Icc M.toPreStructure σ).1

lemma entailsComplete_iff_degree_eq_zero.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    EntailsComplete.{u} Γ φ ↔ degreeOfTruthComplete.{u} Γ φ = 0 := by
  constructor
  · intro h
    unfold degreeOfTruthComplete
    set S := {r : ℝ | ∃ (M : ContinuousStructure.{u} LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}
    by_cases hne : S.Nonempty
    · have hS : S = {0} := by
        ext r
        constructor
        · rintro ⟨M, σ, hM, rfl⟩
          simp [h M σ hM]
        · rintro rfl
          obtain ⟨_, M, σ, hM, _⟩ := hne
          exact ⟨M, σ, hM, (h M σ hM).symm⟩
      rw [hS, csSup_singleton]
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
  · intro hDOT M σ hM
    have hbdd : BddAbove {r : ℝ | ∃ (N : ContinuousStructure.{u} LM) (τ : Var → N.Carrier),
        ModelsPre N.toPreStructure τ Γ ∧ r = φ.eval N.toPreStructure τ} :=
      ⟨1, by rintro _ ⟨N, τ, -, rfl⟩; exact (φ.eval_in_Icc N.toPreStructure τ).2⟩
    have hle : φ.eval M.toPreStructure σ ≤ 0 := by
      have := le_csSup hbdd ⟨M, σ, hM, rfl⟩
      rw [degreeOfTruthComplete] at hDOT
      rwa [hDOT] at this
    exact le_antisymm hle (φ.eval_in_Icc M.toPreStructure σ).1

theorem entailsPre_iff_universe.{u} {L : Signature}
    (Γ : Set (Formula L)) (φ : Formula L) :
    EntailsPre.{u} Γ φ ↔ EntailsPre.{0} Γ φ := by
  simp [entailsPre_iff_degree_eq_zero, degreeOfTruthPre_eq_universe.{u}]

theorem entailsMetricPre_iff_universe.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    EntailsMetricPre.{u} Γ φ ↔ EntailsMetricPre.{0} Γ φ := by
  simp [entailsMetricPre_iff_degree_eq_zero, degreeOfTruthMetric_eq_universe.{u}]

theorem entailsComplete_iff_universe.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    EntailsComplete.{u} Γ φ ↔ EntailsComplete.{0} Γ φ := by
  simp [entailsComplete_iff_degree_eq_zero, degreeOfTruthComplete_eq_universe.{u}]

/-! ### Complete theories are independent of the universe -/

theorem isCompleteTheory_iff_universe.{u} {LM : MetricSignature}
    (T : Set (Formula LM.toSignature)) :
    IsCompleteTheory.{u} T ↔ IsCompleteTheory.{0} T := by
  constructor
  · rintro ⟨hth, M, σ, hT⟩
    let T' : Set (Formula LM.toSignature) :=
      {φ | φ.eval M.toPreStructure σ = 0}
    have hsat0 : CompletelySatisfiable.{0} T' :=
      (completelySatisfiable_iff_universe.{u} T').mp ⟨M, σ, fun φ hφ => hφ⟩
    obtain ⟨N, τ, hN⟩ := hsat0
    refine ⟨hth, N, τ, ?_⟩
    ext ψ
    constructor
    · intro hmem
      have hsent : IsSentence ψ := hth ψ hmem
      have hval0 : ψ.eval M.toPreStructure σ = 0 := by
        have : ψ ∈ {φ | IsSentence φ ∧ φ.eval M.toPreStructure σ = 0} := by
          simpa [hT] using hmem
        exact (Set.mem_ofPred.mp this).2
      exact ⟨hsent, hN ψ hval0⟩
    · intro hmem
      obtain ⟨hsent, hNψ⟩ := Set.mem_ofPred.mp hmem
      have hM0 : ψ.eval M.toPreStructure σ = 0 := by
        by_contra hne
        have hpos : 0 < ψ.eval M.toPreStructure σ :=
          lt_of_le_of_ne (ψ.eval_in_Icc M.toPreStructure σ).1 (Ne.symm hne)
        have hr1 := (ψ.eval_in_Icc M.toPreStructure σ).2
        obtain ⟨p, hp0, hpr⟩ := DyadicCode.dense_in_Icc (le_refl (0 : ℝ)) hr1 hpos
        have hmemT' : Formula.tsub (Formula.dyadic LM.toSignature p) ψ ∈ T' :=
          (tsubR.eq_zero_iff _ _).mpr (by
            simpa [T', Formula.eval, Formula.eval_dyadic] using hpr.le)
        have hpφ := hN _ hmemT'
        have hple : p.val ≤ ψ.eval N.toPreStructure τ :=
          (tsubR.eq_zero_iff _ _).mp (by
            simpa [Formula.eval, Formula.eval_dyadic] using hpφ)
        linarith
      have : ψ ∈ {φ | IsSentence φ ∧ φ.eval M.toPreStructure σ = 0} := ⟨hsent, hM0⟩
      simpa [hT] using this
  · rintro ⟨hth, M, σ, hT⟩
    refine ⟨hth, ContinuousStructure.ulift.{u} M, uliftUp.{u} M.toPreStructure ∘ σ, ?_⟩
    rw [hT]
    ext ψ
    simp [ContinuousStructure.eval_ulift.{u} M σ]

end ContinuousFOL
