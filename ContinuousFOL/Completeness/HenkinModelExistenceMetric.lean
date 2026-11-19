/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Theorem 9.4 metric; vision.md page 23
-/
module

public import ContinuousFOL.Completeness.HenkinModelExistence
public import ContinuousFOL.LanguageAndSemantics.MetricPreStructure
public import ContinuousFOL.Essentials.MaximalConsistentMetric
public import ContinuousFOL.Group2Axioms.SoundnessMetric

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace HenkinMetric

/-- If `genList xs ψ` holds at `σ`, then `ψ` holds at every reassignment of the variables
in `xs`. -/
lemma eval_of_genList {L : Signature} (N : PreStructure L) (xs : List Var) (ψ : Formula L)
    (σ : Var → N.Carrier) (h : (Formula.genList xs ψ).eval N σ = 0) (τ : Var → N.Carrier) :
    ψ.eval N (fun y => if y ∈ xs then τ y else σ y) = 0 := by
  induction xs generalizing σ with
  | nil => simpa [Formula.genList] using h
  | cons x xs ih =>
    simp only [Formula.genList, Formula.eval] at h
    have hbdd : BddAbove (Set.range (fun a : N.Carrier =>
        (Formula.genList xs ψ).eval N (updateAssign σ x a))) :=
      ⟨1, by rintro _ ⟨a, rfl⟩; exact (Formula.eval_in_Icc N _ _).2⟩
    have hx : (Formula.genList xs ψ).eval N (updateAssign σ x (τ x)) = 0 :=
      le_antisymm (h ▸ le_csSup hbdd ⟨τ x, rfl⟩) (Formula.eval_in_Icc N _ _).1
    have := ih _ hx
    convert this using 2
    funext y
    by_cases hy : y ∈ xs
    · simp [hy]
    · by_cases hyx : y = x
      · subst hyx; simp [updateAssign]
      · simp [hy, hyx, updateAssign, Ne.symm hyx]

/-- Evaluation of `d(t₀, t₁)` in a pre-structure. -/
lemma eval_dist' {LM : MetricSignature} (N : PreStructure LM.toSignature)
    (σ : Var → N.Carrier) (t₀ t₁ : Term LM.toSignature) :
    (Formula.dist (LM := LM) t₀ t₁).eval N σ =
      N.relInterp LM.distSym (fun i =>
        if Fin.cast LM.distArity i = 0 then t₀.eval N σ else t₁.eval N σ) := by
  simp only [Formula.dist, Formula.eval]
  congr 1
  funext i
  split_ifs <;> rfl

/-- A pre-structure in which (some assignment satisfies) every generalized metric axiom is a
metric pre-structure. -/
def ofMetricAxioms {LM : MetricSignature} (N : PreStructure LM.toSignature)
    (σ₀ : Var → N.Carrier) (h : ModelsPre N σ₀ (metricAxiomSet LM)) :
    MetricPreStructure LM :=
  have hax : ∀ (xs : List Var) (ψ : Formula LM.toSignature), MetricAxiomSchema (LM := LM) ψ →
      ∀ τ : Var → N.Carrier, ψ.eval N (fun y => if y ∈ xs then τ y else σ₀ y) = 0 :=
    fun xs ψ hψ τ => eval_of_genList N xs ψ σ₀ (h _ ⟨xs, ψ, hψ, rfl⟩) τ
  let D : N.Carrier → N.Carrier → ℝ := fun a b =>
    N.relInterp LM.distSym (fun i => if Fin.cast LM.distArity i = 0 then a else b)
  have hD : ∀ a b, 0 ≤ D a b ∧ D a b ≤ 1 := fun a b => N.rel_in_Icc _ _
  -- Assignment sending `0 ↦ c`, `1 ↦ e`, `j + 2 ↦ v j`.
  let τ : ∀ {n : ℕ}, (Fin n → N.Carrier) → N.Carrier → N.Carrier → Var → N.Carrier :=
    fun {n} v c e y => if y = 0 then c else if y = 1 then e else
      if hy : y - 2 < n then v ⟨y - 2, hy⟩ else c
  let xsOf : ℕ → List Var := fun n => 0 :: 1 :: List.ofFn (fun j : Fin n => (j : ℕ) + 2)
  have hτ0 : ∀ {n} (v : Fin n → N.Carrier) c e,
      (if 0 ∈ xsOf n then τ v c e 0 else σ₀ 0) = c := by
    intros; simp [xsOf, τ]
  have hτ1 : ∀ {n} (v : Fin n → N.Carrier) c e,
      (if 1 ∈ xsOf n then τ v c e 1 else σ₀ 1) = e := by
    intros; simp [xsOf, τ]
  have hτv : ∀ {n} (v : Fin n → N.Carrier) c e,
      (fun j : Fin n => if (j : ℕ) + 2 ∈ xsOf n then τ v c e ((j : ℕ) + 2) else σ₀ ((j : ℕ) + 2)) = v := by
    intro n v c e
    funext j
    have hmem : (j : ℕ) + 2 ∈ xsOf n := by
      simp only [xsOf, List.mem_cons, List.mem_ofFn]
      exact Or.inr (Or.inr ⟨j, rfl⟩)
    simp [hmem, τ]
  -- From "`D c e < q` for a dyadic `q` forces `X ≤ r` for all dyadic `r > ε`", get `X ≤ ε`.
  have key : ∀ (X ε : ℝ) (δ : ℝ) (c e : N.Carrier), 0 ≤ ε → X ≤ 1 → δ ≤ 1 → D c e < δ →
      (∀ q r : DyadicCode, ε < r.val → q.val < δ → D c e < q.val → X ≤ r.val) → X ≤ ε := by
    intro X ε δ c e hε0 hX hδ hce H
    obtain ⟨q, hq1, hq2⟩ := DyadicCode.dense_in_Icc (hD c e).1 hδ hce
    by_contra hlt
    push Not at hlt
    obtain ⟨r, hr1, hr2⟩ := DyadicCode.dense_in_Icc hε0 hX hlt
    have := H q r hr1 hq2 hq1
    linarith
  { toPreStructure := N
    dist_self := fun a => by
      have := hax [0] _ (.A10 0) (fun _ => a)
      rw [eval_dist'] at this
      simpa [Term.eval] using this
    dist_symm := fun a b => by
      let ρ : Var → N.Carrier := fun y => if y = 0 then a else b
      have := hax [0, 1] _ (.A11 0 1) ρ
      simp only [Formula.eval] at this
      rw [eval_dist', eval_dist'] at this
      have h2 := hax [0, 1] _ (.A11 1 0) ρ
      simp only [Formula.eval] at h2
      rw [eval_dist', eval_dist'] at h2
      simp [ρ, Term.eval] at this h2
      exact le_antisymm this h2
    dist_triangle := fun a b c => by
      let ρ : Var → N.Carrier := fun y => if y = 0 then a else if y = 1 then b else c
      have := hax [0, 1, 2] _ (.A12 0 1 2) ρ
      simp only [Formula.eval] at this
      rw [eval_dist', eval_dist', eval_dist'] at this
      simp [ρ, Term.eval] at this
      have h1 := this.1
      dsimp only
      linarith
    func_unif_cont := fun f i ε hε hε1 v c e hce => by
      have hδ := (LM.funcMod_pos f i ε hε hε1).2
      refine key _ ε _ c e hε.le (hD _ _).2 hδ hce ?_
      intro q r hr hq hq'
      have hA := hax (xsOf (LM.funcArity f)) _
        (.A13 f i ε r q (fun j => (j : ℕ) + 2) 0 1 hε hε1 hr hq) (τ v c e)
      simp only [Formula.minF, Formula.eval, Formula.eval_dyadic] at hA
      rw [tsubR.tsub_tsub_eq_min (tsubR.nonneg _ _) (tsubR.nonneg _ _)] at hA
      rw [eval_dist', eval_dist', Term.eval_func_replaceArg_var,
        Term.eval_func_replaceArg_var] at hA
      simp only [Term.eval, hτ0, hτ1, hτv] at hA
      rcases min_eq_iff.mp hA with ⟨h, -⟩ | ⟨h, -⟩
      · have := (tsubR.eq_zero_iff _ _).mp h
        exact absurd this (not_le.mpr hq')
      · exact (tsubR.eq_zero_iff _ _).mp h
    rel_unif_cont := fun P i ε hε hε1 v c e hce => by
      have hδ := (LM.relMod_pos P i ε hε hε1).2
      refine key _ ε _ c e hε.le ?_ hδ hce ?_
      · exact le_trans (tsubR.tsub_le_self (N.rel_in_Icc _ _).1 (N.rel_in_Icc _ _).1)
          (N.rel_in_Icc _ _).2
      intro q r hr hq hq'
      have hA := hax (xsOf (LM.relArity P)) _
        (.A14 P i ε r q (fun j => (j : ℕ) + 2) 0 1 hε hε1 hr hq) (τ v c e)
      simp only [Formula.minF, Formula.eval, Formula.eval_dyadic] at hA
      rw [tsubR.tsub_tsub_eq_min (tsubR.nonneg _ _) (tsubR.nonneg _ _)] at hA
      rw [eval_dist', Formula.eval_rel_replaceArg_var, Formula.eval_rel_replaceArg_var] at hA
      simp only [Term.eval, hτ0, hτ1, hτv] at hA
      rcases min_eq_iff.mp hA with ⟨h, -⟩ | ⟨h, -⟩
      · have := (tsubR.eq_zero_iff _ _).mp h
        exact absurd this (not_le.mpr hq')
      · exact (tsubR.eq_zero_iff _ _).mp h }

end HenkinMetric

theorem henkin_model_existence_metric {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (hcons : ConsistentMetricQ Γ) :
    ∃ (M : MetricPreStructure LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ Γ := by
  -- Apply Theorem 9.4 to `Γ ∪ {metric axioms}` and take the reduct to `L`.
  have hcons' : ConsistentQ (Γ ∪ metricAxiomSet LM) := by
    obtain ⟨φ, hφ⟩ := hcons
    exact ⟨φ, fun h => hφ ((provableMetricQ_iff_provableQ Γ φ).mpr h)⟩
  obtain ⟨Lc, ext, Δ, M, σ, -, -, hΓΔ, hMΔ⟩ := henkin_model_existence hcons'
  have hN : ModelsPre (ext.reductPre M) σ (Γ ∪ metricAxiomSet LM) := by
    intro φ hφ
    rw [ext.eval_reduct M σ φ]
    exact hMΔ _ (hΓΔ ⟨φ, hφ, rfl⟩)
  refine ⟨HenkinMetric.ofMetricAxioms (ext.reductPre M) σ
    (fun φ hφ => hN φ (Or.inr hφ)), σ, fun φ hφ => hN φ (Or.inl hφ)⟩

end ContinuousFOL
