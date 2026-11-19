/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Lemma 6.4; vision.md page 11–12
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.FormulaBoundSubst
public import ContinuousFOL.LanguageAndSemantics.FormulaEquiv
public import ContinuousFOL.SubstitutionAndCompletions.SubstitutionLemma
public import Mathlib.Data.Finset.Max

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- A variable strictly above every member of `s`. -/
def freshAbove (s : Finset Var) : Var :=
  match s.max with
  | ⊥ => 0
  | (n : Var) => n + 1

lemma freshAbove_not_mem (s : Finset Var) : freshAbove s ∉ s := by
  intro hs
  have hle : (freshAbove s : WithBot Var) ≤ s.max := Finset.le_max hs
  cases hmax : s.max with
  | bot =>
    rw [Finset.max_eq_bot.mp hmax] at hs
    simp at hs
  | coe n =>
    rw [hmax] at hle
    have hf : freshAbove s = n + 1 := by simp [freshAbove, hmax]
    rw [hf] at hle
    have hlt : n + 1 ≤ n := (WithBot.coe_le_coe).mp hle
    exact absurd hlt (Nat.not_succ_le_self n)

lemma Formula.freeVars_subset_allVars {L : Signature} (φ : Formula L) :
    φ.freeVars ⊆ φ.allVars := by
  induction φ with
  | rel _ _ => simp [Formula.freeVars, Formula.allVars]
  | tsub α β ihα ihβ =>
    simp only [Formula.freeVars, Formula.allVars]
    exact Finset.union_subset_union ihα ihβ
  | neg α ih =>
    simpa [Formula.freeVars, Formula.allVars] using ih
  | half α ih =>
    simpa [Formula.freeVars, Formula.allVars] using ih
  | sup x α ih =>
    intro v hv
    exact Finset.mem_insert_of_mem (ih (Finset.mem_of_mem_erase hv))

lemma Formula.boundVars_freeSubst {L : Signature} (φ : Formula L) (t : Term L) (x : Var) :
    (φ.freeSubst t x).boundVars = φ.boundVars := by
  induction φ with
  | rel _ _ => simp [Formula.freeSubst, Formula.boundVars]
  | tsub α β ihα ihβ => simp [Formula.freeSubst, Formula.boundVars, ihα, ihβ]
  | neg α ih => simp [Formula.freeSubst, Formula.boundVars, ih]
  | half α ih => simp [Formula.freeSubst, Formula.boundVars, ih]
  | sup y α ih =>
    by_cases h : y = x
    · simp [Formula.freeSubst, Formula.boundVars, h]
    · simp [Formula.freeSubst, Formula.boundVars, h, ih]

/-- Replacing a variable absent from `φ` cannot be captured. -/
lemma Formula.freeSubstCorrect_of_fresh {L : Signature} (φ : Formula L) (x y : Var)
    (hy : y ∉ φ.allVars) : φ.FreeSubstCorrect (.var y) x := by
  induction φ with
  | rel _ _ =>
    simp [Formula.FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    exact ⟨ihα (fun h => hy (Finset.mem_union_left _ h)),
      ihβ (fun h => hy (Finset.mem_union_right _ h))⟩
  | neg α ih =>
    exact ih (by simpa [Formula.allVars] using hy)
  | half α ih =>
    exact ih (by simpa [Formula.allVars] using hy)
  | sup z α ih =>
    unfold Formula.FreeSubstCorrect
    by_cases hz : z = x
    · simp [hz]
    · simp [hz]
      refine ⟨?_, ih (fun h => hy (Finset.mem_insert_of_mem h))⟩
      intro _hx hyvar
      have : z = y := by simpa [Term.vars] using hyvar
      exact hy (by simp [Formula.allVars, this])

/-- Rename bound variables of `φ` off `avoid`, by bound substitution at clashing binders. -/
def Formula.renameBound {L : Signature} (avoid : Finset Var) : Formula L → Formula L
  | .rel P args => .rel P args
  | .tsub α β => .tsub (α.renameBound avoid) (β.renameBound avoid)
  | .neg α => .neg (α.renameBound avoid)
  | .half α => .half (α.renameBound avoid)
  | .sup x α =>
    let α' := α.renameBound avoid
    if x ∈ avoid then
      let y := freshAbove (avoid ∪ α'.allVars)
      .sup y (α'.freeSubst (.var y) x)
    else
      .sup x α'

lemma Formula.boundVars_renameBound {L : Signature} (avoid : Finset Var) (φ : Formula L) :
    Disjoint avoid (φ.renameBound avoid).boundVars := by
  induction φ with
  | rel _ _ =>
    simp [Formula.renameBound, Formula.boundVars]
  | tsub α β ihα ihβ =>
    unfold Formula.renameBound Formula.boundVars
    rw [Finset.disjoint_left]
    intro v hv hvb
    rcases Finset.mem_union.mp hvb with hvα | hvβ
    · exact Finset.disjoint_left.mp ihα hv hvα
    · exact Finset.disjoint_left.mp ihβ hv hvβ
  | neg α ih =>
    simpa [Formula.renameBound, Formula.boundVars] using ih
  | half α ih =>
    simpa [Formula.renameBound, Formula.boundVars] using ih
  | sup x α ih =>
    simp only [Formula.renameBound]
    split_ifs with hx
    · set α' := α.renameBound avoid
      set y := freshAbove (avoid ∪ α'.allVars)
      simp only [Formula.boundVars]
      rw [Formula.boundVars_freeSubst]
      rw [Finset.disjoint_left]
      intro v hv hvb
      rcases Finset.mem_insert.mp hvb with rfl | hvα
      · exact freshAbove_not_mem (avoid ∪ α'.allVars) (Finset.mem_union_left _ hv)
      · exact Finset.disjoint_left.mp ih hv hvα
    · simp only [Formula.boundVars]
      rw [Finset.disjoint_left]
      intro v hv hvb
      rcases Finset.mem_insert.mp hvb with rfl | hvα
      · exact hx hv
      · exact Finset.disjoint_left.mp ih hv hvα

lemma Formula.eval_renameBound {L : Signature} (M : PreStructure L) (avoid : Finset Var)
    (φ : Formula L) (σ : Var → M.Carrier) :
    (φ.renameBound avoid).eval M σ = φ.eval M σ := by
  induction φ generalizing σ with
  | rel _ _ =>
    rfl
  | tsub α β ihα ihβ =>
    simp [Formula.renameBound, Formula.eval, ihα σ, ihβ σ]
  | neg α ih =>
    simp [Formula.renameBound, Formula.eval, ih σ]
  | half α ih =>
    simp [Formula.renameBound, Formula.eval, ih σ]
  | sup x α ih =>
    simp only [Formula.renameBound, Formula.eval]
    split_ifs with hx
    · set α' := α.renameBound avoid
      set y := freshAbove (avoid ∪ α'.allVars)
      have hy_all : y ∉ α'.allVars := by
        intro hy
        exact freshAbove_not_mem (avoid ∪ α'.allVars) (Finset.mem_union_right _ hy)
      have hy_free : y ∉ α'.freeVars := fun h => hy_all (freeVars_subset_allVars α' h)
      have hyx : y ≠ x := by
        intro hxy
        have hmem : y ∈ avoid ∪ α'.allVars := by
          rw [hxy]
          exact Finset.mem_union_left _ hx
        exact freshAbove_not_mem _ hmem
      have hcorr : α'.FreeSubstCorrect (.var y) x :=
        freeSubstCorrect_of_fresh α' x y hy_all
      have hfun : ∀ a : M.Carrier,
          (α'.freeSubst (.var y) x).eval M (updateAssign σ y a) =
            α.eval M (updateAssign σ x a) := by
        intro a
        rw [substitution_lemma M (updateAssign σ y a) (.var y) x α' hcorr]
        have hvar : ((Term.var y).eval M (updateAssign σ y a)) = a := by
          simp [Term.eval]
        rw [hvar, updateAssign_comm σ hyx.symm a a,
          Formula.eval_update_of_not_mem_freeVars M (updateAssign σ x a) y a α' hy_free]
        exact ih (updateAssign σ x a)
      apply congrArg sSup
      apply congrArg Set.range
      funext a
      exact hfun a
    · apply congrArg sSup
      refine Set.ext fun r => ?_
      simp only [Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a, (ih (updateAssign σ x a)).symm⟩
      · rintro ⟨a, rfl⟩
        exact ⟨a, ih (updateAssign σ x a)⟩

/-- Lemma 6.4 (Bound Substitution Lemma). -/
theorem bound_substitution_lemma {L : Signature} (φ : Formula L) (xs : Finset Var) :
    ∃ φ' : Formula L, Disjoint xs φ'.boundVars ∧ (φ ≡ᶠ φ') := by
  refine ⟨φ.renameBound xs, Formula.boundVars_renameBound xs φ, ?_⟩
  intro M σ
  exact (Formula.eval_renameBound M xs φ σ).symm

end ContinuousFOL
