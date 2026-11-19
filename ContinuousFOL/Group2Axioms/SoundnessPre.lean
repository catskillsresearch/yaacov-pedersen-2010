/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §7 Theorem 7.2 without metric; vision.md page 15
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.EntailsPre
public import ContinuousFOL.LanguageAndSemantics.FormulaOne
public import ContinuousFOL.SubstitutionAndCompletions.SubstitutionLemma
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace tsubR

lemma tsub_le_self {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x ∸ y ≤ x := by
  have hsub : x - y ≤ x := by linarith
  rw [def_eq]
  exact max_le hsub hx

lemma le_add_tsub (x y : ℝ) : x ≤ y + (x ∸ y) := by
  by_cases h : x ≤ y
  · have h0 : x - y ≤ 0 := by linarith
    rw [show x ∸ y = 0 by rw [def_eq, max_eq_right h0]]
    linarith
  · push Not at h
    have h0 : 0 ≤ x - y := by linarith
    rw [show x ∸ y = x - y by rw [def_eq, max_eq_left h0]]
    linarith

lemma sub_le_iff_add {x y z : ℝ} (hz : 0 ≤ z) : x ∸ y ≤ z ↔ x ≤ y + z := by
  rw [le_iff x y z hz]
  constructor <;> intro h <;> linarith

/-- `((c ∸ a) ∸ (c ∸ b)) ≤ b ∸ a`, the real form of (A2). -/
lemma tsub_tsub_le (a b c : ℝ) : (c ∸ a) ∸ (c ∸ b) ≤ b ∸ a := by
  by_cases hcb : c ≤ b
  · have hb0 : c ∸ b = 0 := (eq_zero_iff c b).mpr hcb
    have hleft : (c ∸ a) ∸ (c ∸ b) = c ∸ a := by
      rw [hb0, def_eq]
      have hsub : c ∸ a - 0 = c ∸ a := by ring
      rw [hsub]
      exact max_eq_left (nonneg c a)
    rw [hleft]
    by_cases hca : c ≤ a
    · rw [(eq_zero_iff c a).mpr hca]
      exact nonneg b a
    · push Not at hca
      have hca' : c ∸ a = c - a := by
        rw [def_eq, max_eq_left (show 0 ≤ c - a by linarith)]
      rw [hca']
      have hab : a < b := by linarith
      have hba : b ∸ a = b - a := by
        rw [def_eq, max_eq_left (show 0 ≤ b - a by linarith)]
      rw [hba]
      linarith
  · push Not at hcb
    by_cases hca : c ≤ a
    · have ha0 : c ∸ a = 0 := (eq_zero_iff c a).mpr hca
      rw [ha0, def_eq]
      have hsub : (0 : ℝ) - (c ∸ b) ≤ 0 := by linarith [nonneg c b]
      rw [max_eq_right hsub]
      exact nonneg b a
    · push Not at hca
      have hca' : c ∸ a = c - a := by
        rw [def_eq, max_eq_left (show 0 ≤ c - a by linarith)]
      have hcb' : c ∸ b = c - b := by
        rw [def_eq, max_eq_left (show 0 ≤ c - b by linarith)]
      rw [hca', hcb', def_eq]
      have hdiff : (c - a) - (c - b) = b - a := by ring
      rw [hdiff, def_eq]

lemma tsub_tsub_eq_min {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ∸ (x ∸ y) = min x y := by
  by_cases h : x ≤ y
  · have h0 : x ∸ y = 0 := (eq_zero_iff x y).mpr h
    rw [h0, def_eq]
    have hsub : x - 0 = x := by ring
    rw [hsub, max_eq_left hx]
    exact (min_eq_left h).symm
  · push Not at h
    have hxy : x ∸ y = x - y := by
      rw [def_eq, max_eq_left (show 0 ≤ x - y by linarith)]
    rw [hxy]
    have hr : x - (x - y) = y := by ring
    rw [def_eq, hr, max_eq_left hy]
    exact (min_eq_right (le_of_lt h)).symm

lemma neg_congr (x y : ℝ) : (1 - y) ∸ (1 - x) = x ∸ y := by
  have h : (1 - y) - (1 - x) = x - y := by ring
  rw [def_eq, def_eq, h]

lemma half_tsub {x : ℝ} (hx : 0 ≤ x) : x ∸ (x / 2) = x / 2 := by
  have h : x - x / 2 = x / 2 := by ring
  have h0 : 0 ≤ x / 2 := by linarith
  rw [def_eq, h, max_eq_left h0]

end tsubR

lemma Formula.eval_genList_eq_zero {L : Signature} (M : PreStructure L)
    (xs : List Var) (ψ : Formula L)
    (hψ : ∀ σ : Var → M.Carrier, ψ.eval M σ = 0) (σ : Var → M.Carrier) :
    (Formula.genList xs ψ).eval M σ = 0 := by
  induction xs generalizing σ with
  | nil =>
    simpa [Formula.genList] using hψ σ
  | cons x xs ih =>
    simp only [Formula.genList, Formula.eval]
    let S := Set.range (fun a : M.Carrier =>
      (Formula.genList xs ψ).eval M (updateAssign σ x a))
    have hne : S.Nonempty := Set.range_nonempty _
    have hzero : ∀ r ∈ S, r = 0 := by
      rintro r ⟨a, rfl⟩
      exact ih (updateAssign σ x a)
    have hbdd : BddAbove S := ⟨0, fun r hr => le_of_eq (hzero r hr)⟩
    obtain ⟨a₀⟩ := M.nonempty
    have h0 : (0 : ℝ) ∈ S := ⟨a₀, ih (updateAssign σ x a₀)⟩
    exact le_antisymm (csSup_le hne (fun r hr => le_of_eq (hzero r hr))) (le_csSup hbdd h0)

lemma baseAxiom_eval_zero {L : Signature} {ψ : Formula L} (h : BaseAxiomSchema ψ)
    (M : PreStructure L) (σ : Var → M.Carrier) : ψ.eval M σ = 0 := by
  cases h with
  | A1 φ ψ =>
    have hx : 0 ≤ φ.eval M σ := (Formula.eval_in_Icc M σ φ).1
    have hy : 0 ≤ ψ.eval M σ := (Formula.eval_in_Icc M σ ψ).1
    simp only [Formula.eval]
    exact (tsubR.eq_zero_iff _ _).mpr (tsubR.tsub_le_self hx hy)
  | A2 φ ψ χ =>
    simp only [Formula.eval]
    exact (tsubR.eq_zero_iff _ _).mpr
      (tsubR.tsub_tsub_le (φ.eval M σ) (ψ.eval M σ) (χ.eval M σ))
  | A3 φ ψ =>
    have hφ := Formula.eval_in_Icc M σ φ
    have hψ := Formula.eval_in_Icc M σ ψ
    simp only [Formula.eval]
    have hmin :
        φ.eval M σ ∸ (φ.eval M σ ∸ ψ.eval M σ) =
          ψ.eval M σ ∸ (ψ.eval M σ ∸ φ.eval M σ) := by
      rw [tsubR.tsub_tsub_eq_min hφ.1 hψ.1, tsubR.tsub_tsub_eq_min hψ.1 hφ.1, min_comm]
    exact (tsubR.eq_zero_iff _ _).mpr (le_of_eq hmin)
  | A4 φ ψ =>
    simp only [Formula.eval]
    rw [tsubR.neg_congr (φ.eval M σ) (ψ.eval M σ)]
    exact (tsubR.eq_zero_iff _ _).mpr le_rfl
  | A5 φ =>
    have hx := (Formula.eval_in_Icc M σ φ).1
    simp only [Formula.eval]
    rw [tsubR.half_tsub hx]
    exact (tsubR.eq_zero_iff _ _).mpr le_rfl
  | A6 φ =>
    have hx := (Formula.eval_in_Icc M σ φ).1
    simp only [Formula.eval]
    rw [tsubR.half_tsub hx]
    exact (tsubR.eq_zero_iff _ _).mpr le_rfl
  | A7 x φ ψ =>
    simp only [Formula.eval]
    set Sφ := Set.range (fun a : M.Carrier => φ.eval M (updateAssign σ x a))
    set Sψ := Set.range (fun a : M.Carrier => ψ.eval M (updateAssign σ x a))
    set Sd := Set.range (fun a : M.Carrier =>
      ψ.eval M (updateAssign σ x a) ∸ φ.eval M (updateAssign σ x a))
    have hbφ : BddAbove Sφ := ⟨1, by
      rintro _ ⟨a, rfl⟩
      exact (Formula.eval_in_Icc M _ φ).2⟩
    have hbψ : BddAbove Sψ := ⟨1, by
      rintro _ ⟨a, rfl⟩
      exact (Formula.eval_in_Icc M _ ψ).2⟩
    have hbd : BddAbove Sd := ⟨1, by
      rintro _ ⟨a, rfl⟩
      simpa [Formula.eval] using
        (Formula.eval_in_Icc M (updateAssign σ x a) (.tsub ψ φ)).2⟩
    have hneψ : Sψ.Nonempty := Set.range_nonempty _
    have hpoint : ∀ a : M.Carrier,
        ψ.eval M (updateAssign σ x a) ≤ sSup Sφ + sSup Sd := by
      intro a
      calc
        ψ.eval M (updateAssign σ x a)
            ≤ φ.eval M (updateAssign σ x a) +
                (ψ.eval M (updateAssign σ x a) ∸ φ.eval M (updateAssign σ x a)) :=
          tsubR.le_add_tsub _ _
        _ ≤ sSup Sφ + sSup Sd :=
          add_le_add (le_csSup hbφ ⟨a, rfl⟩) (le_csSup hbd ⟨a, rfl⟩)
    have hsup : sSup Sψ ≤ sSup Sφ + sSup Sd :=
      csSup_le hneψ (by rintro _ ⟨a, rfl⟩; exact hpoint a)
    have hd0 : 0 ≤ sSup Sd := by
      obtain ⟨a⟩ := M.nonempty
      exact le_trans (tsubR.nonneg _ _) (le_csSup hbd ⟨a, rfl⟩)
    exact (tsubR.eq_zero_iff _ _).mpr ((tsubR.sub_le_iff_add hd0).mpr hsup)
  | A8 x t φ hcorr =>
    simp only [Formula.eval]
    rw [substitution_lemma M σ t x φ hcorr]
    refine (tsubR.eq_zero_iff _ _).mpr (le_csSup ?_ ⟨t.eval M σ, rfl⟩)
    refine ⟨1, ?_⟩
    rintro _ ⟨a, rfl⟩
    exact (Formula.eval_in_Icc M _ φ).2
  | A9 x φ hx =>
    simp only [Formula.eval]
    have hconst : ∀ a : M.Carrier,
        φ.eval M (updateAssign σ x a) = φ.eval M σ :=
      fun a => Formula.eval_update_of_not_mem_freeVars M σ x a φ hx
    have hrange :
        Set.range (fun a : M.Carrier => φ.eval M (updateAssign σ x a)) =
          {φ.eval M σ} := by
      ext r
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨a, rfl⟩
        exact hconst a
      · intro hr
        obtain ⟨a⟩ := M.nonempty
        exact ⟨a, by rw [hconst a, hr]⟩
    rw [hrange, csSup_singleton]
    exact (tsubR.eq_zero_iff _ _).mpr le_rfl

/-- Theorem 7.2 (Soundness) for signatures without metric. -/
theorem soundness_pre.{u} {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) :
    ProvableQ Γ φ → EntailsPre.{u} Γ φ := by
  intro hprov
  induction hprov with
  | @ax xs ψ hax =>
    intro M σ _
    exact Formula.eval_genList_eq_zero M xs ψ
      (fun σ' => baseAxiom_eval_zero hax M σ') σ
  | @hyp φ hmem =>
    intro M σ hM
    exact hM φ hmem
  | @mp φ ψ _hφ _himp ihφ ihimp =>
    intro M σ hM
    have hφ0 : φ.eval M σ = 0 := ihφ M σ hM
    have himp0 : (Formula.tsub ψ φ).eval M σ = 0 := ihimp M σ hM
    have hle : ψ.eval M σ ≤ φ.eval M σ := by
      have : ψ.eval M σ ∸ φ.eval M σ = 0 := by simpa [Formula.eval] using himp0
      exact (tsubR.eq_zero_iff _ _).mp this
    have hle0 : ψ.eval M σ ≤ 0 := by simpa [hφ0] using hle
    exact le_antisymm hle0 (Formula.eval_in_Icc M σ ψ).1

theorem satisfiable_consistent_pre.{u} {L : Signature} (Γ : Set (Formula L)) :
    SatisfiablePre.{u} Γ → ConsistentQ Γ := by
  rintro ⟨M, σ, hM⟩
  refine ⟨Formula.one L, fun hprov => ?_⟩
  have hval := soundness_pre Γ (Formula.one L) hprov M σ hM
  simp at hval

end ContinuousFOL
