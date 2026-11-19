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

/-- `φ'` is obtained from `φ` by a (finite, possibly empty) sequence of bound substitutions
`· {y/x}` (Definition 6.3). -/
def Formula.BoundSubstReach {L : Signature} : Formula L → Formula L → Prop :=
  Relation.ReflTransGen (fun φ ψ => ∃ y x : Var, ψ = φ.boundSubst y x)

namespace BoundSubstAux

variable {L : Signature}

lemma term_not_mem_vars_subst_var (s : Term L) {x y : Var} (hyx : y ≠ x) :
    x ∉ (s.subst (.var y) x).vars := by
  induction s with
  | var z =>
    by_cases hz : z = x
    · simp [Term.subst, hz, Term.vars, Ne.symm hyx]
    · simp [Term.subst, hz, Term.vars, Ne.symm hz]
  | func f args ih =>
    simp only [Term.subst, Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists]
    exact ih

lemma not_mem_freeVars_freeSubst_var (φ : Formula L) {x y : Var} (hyx : y ≠ x) :
    x ∉ (φ.freeSubst (.var y) x).freeVars := by
  induction φ with
  | rel P args =>
    simp only [Formula.freeSubst, Formula.freeVars, Finset.mem_biUnion, Finset.mem_univ,
      true_and, not_exists]
    exact fun i => term_not_mem_vars_subst_var _ hyx
  | tsub α β ihα ihβ => simp [Formula.freeSubst, Formula.freeVars, ihα, ihβ]
  | neg α ih => simpa [Formula.freeSubst, Formula.freeVars] using ih
  | half α ih => simpa [Formula.freeSubst, Formula.freeVars] using ih
  | sup z α ih =>
    by_cases hz : z = x
    · simp [Formula.freeSubst, Formula.freeVars, hz]
    · simp [Formula.freeSubst, Formula.freeVars, hz, ih]

lemma freeSubstCorrect_of_not_mem_freeVars (φ : Formula L) (t : Term L) {x : Var}
    (hx : x ∉ φ.freeVars) : φ.FreeSubstCorrect t x := by
  induction φ with
  | rel _ _ => simp [Formula.FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    simp only [Formula.freeVars, Finset.mem_union, not_or] at hx
    exact ⟨ihα hx.1, ihβ hx.2⟩
  | neg α ih => exact ih (by simpa [Formula.freeVars] using hx)
  | half α ih => exact ih (by simpa [Formula.freeVars] using hx)
  | sup z α ih =>
    unfold Formula.FreeSubstCorrect
    by_cases hz : z = x
    · simp [hz]
    · have hx' : x ∉ α.freeVars := by
        intro h
        exact hx (Finset.mem_erase.mpr ⟨Ne.symm hz, h⟩)
      simp only [hz, ite_false]
      exact ⟨fun h => absurd h hx', ih hx'⟩

lemma freeSubstCorrect_boundSubst (φ : Formula L) {x y : Var} (hy : y ∉ φ.allVars) :
    (φ.boundSubst y x).FreeSubstCorrect (.var y) x := by
  induction φ with
  | rel _ _ => simp [Formula.boundSubst, Formula.FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    simp only [Formula.allVars, Finset.mem_union, not_or] at hy
    exact ⟨ihα hy.1, ihβ hy.2⟩
  | neg α ih => exact ih (by simpa [Formula.allVars] using hy)
  | half α ih => exact ih (by simpa [Formula.allVars] using hy)
  | sup z α ih =>
    simp only [Formula.allVars, Finset.mem_insert, not_or] at hy
    simp only [Formula.boundSubst]
    split_ifs with hz
    · subst hz
      unfold Formula.FreeSubstCorrect
      simp only [hy.1, ite_false]
      exact ⟨fun h => absurd h (not_mem_freeVars_freeSubst_var _ hy.1),
        freeSubstCorrect_of_not_mem_freeVars _ _ (not_mem_freeVars_freeSubst_var _ hy.1)⟩
    · unfold Formula.FreeSubstCorrect
      simp only [hz, ite_false]
      refine ⟨fun _ hzv => ?_, ih hy.2⟩
      have : z = y := by simpa [Term.vars] using hzv
      exact hy.1 this.symm

lemma eval_boundSubst (M : PreStructure L) (φ : Formula L) {x y : Var}
    (hy : y ∉ φ.allVars) (σ : Var → M.Carrier) :
    (φ.boundSubst y x).eval M σ = φ.eval M σ := by
  induction φ generalizing σ with
  | rel _ _ => rfl
  | tsub α β ihα ihβ =>
    simp only [Formula.allVars, Finset.mem_union, not_or] at hy
    simp [Formula.boundSubst, Formula.eval, ihα hy.1 σ, ihβ hy.2 σ]
  | neg α ih =>
    simp [Formula.boundSubst, Formula.eval, ih (by simpa [Formula.allVars] using hy) σ]
  | half α ih =>
    simp [Formula.boundSubst, Formula.eval, ih (by simpa [Formula.allVars] using hy) σ]
  | sup z α ih =>
    simp only [Formula.allVars, Finset.mem_insert, not_or] at hy
    have ih' := ih hy.2
    simp only [Formula.boundSubst, Formula.eval]
    split_ifs with hz
    · subst hz
      have hyx : y ≠ z := hy.1
      have hy_free : y ∉ α.freeVars := fun h => hy.2 (Formula.freeVars_subset_allVars α h)
      have hcorr := freeSubstCorrect_boundSubst α (x := z) hy.2
      apply congrArg sSup
      apply congrArg Set.range
      funext a
      rw [substitution_lemma M (updateAssign σ y a) (.var y) z _ hcorr]
      have hvar : ((Term.var y).eval M (updateAssign σ y a)) = a := by simp [Term.eval]
      rw [hvar, ih', ← updateAssign_comm σ hyx a a,
        Formula.eval_update_of_not_mem_freeVars M (updateAssign σ z a) y a α hy_free]
    · simp only [Formula.eval]
      apply congrArg sSup
      apply congrArg Set.range
      funext a
      exact ih' _

lemma not_mem_boundVars_boundSubst (φ : Formula L) {x y : Var} (hyx : y ≠ x) :
    x ∉ (φ.boundSubst y x).boundVars := by
  induction φ with
  | rel _ _ => simp [Formula.boundSubst, Formula.boundVars]
  | tsub α β ihα ihβ => simp [Formula.boundSubst, Formula.boundVars, ihα, ihβ]
  | neg α ih => simpa [Formula.boundSubst, Formula.boundVars] using ih
  | half α ih => simpa [Formula.boundSubst, Formula.boundVars] using ih
  | sup z α ih =>
    simp only [Formula.boundSubst]
    split_ifs with hz
    · simp [Formula.boundVars, Formula.boundVars_freeSubst, Ne.symm hyx, ih]
    · simp [Formula.boundVars, Ne.symm hz, ih]

lemma boundVars_boundSubst_subset (φ : Formula L) (x y : Var) :
    (φ.boundSubst y x).boundVars ⊆ insert y φ.boundVars := by
  induction φ with
  | rel _ _ => simp [Formula.boundSubst, Formula.boundVars]
  | tsub α β ihα ihβ =>
    simp only [Formula.boundSubst, Formula.boundVars]
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · rcases Finset.mem_insert.mp (ihα h) with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h')
    · rcases Finset.mem_insert.mp (ihβ h) with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h')
  | neg α ih => simpa [Formula.boundSubst, Formula.boundVars] using ih
  | half α ih => simpa [Formula.boundSubst, Formula.boundVars] using ih
  | sup z α ih =>
    simp only [Formula.boundSubst]
    split_ifs with hz
    · simp only [Formula.boundVars, Formula.boundVars_freeSubst]
      intro v hv
      rcases Finset.mem_insert.mp hv with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · rcases Finset.mem_insert.mp (ih h) with h' | h'
        · exact Finset.mem_insert.mpr (Or.inl h')
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h')
    · simp only [Formula.boundVars]
      intro v hv
      rcases Finset.mem_insert.mp hv with h | h
      · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h))
      · rcases Finset.mem_insert.mp (ih h) with h' | h'
        · exact Finset.mem_insert.mpr (Or.inl h')
        · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h')

/-- Finset form of Lemma 6.4. -/
lemma exists_reach (s : Finset Var) (φ : Formula L) :
    ∃ φ' : Formula L, φ.BoundSubstReach φ' ∧ Disjoint s φ'.boundVars ∧ (φ ≡ᶠ φ') := by
  induction s using Finset.induction_on with
  | empty => exact ⟨φ, Relation.ReflTransGen.refl, Finset.disjoint_empty_left _, fun _ _ => rfl⟩
  | insert a s _ ih =>
    obtain ⟨φ₁, hr, hd, he⟩ := ih
    set y := freshAbove (insert a s ∪ φ₁.allVars)
    have hy1 : y ∉ φ₁.allVars := fun h =>
      freshAbove_not_mem (insert a s ∪ φ₁.allVars) (Finset.mem_union_right _ h)
    have hys : y ∉ insert a s := fun h =>
      freshAbove_not_mem (insert a s ∪ φ₁.allVars) (Finset.mem_union_left _ h)
    have hya : y ≠ a := fun h => hys (h ▸ Finset.mem_insert_self _ _)
    refine ⟨φ₁.boundSubst y a, hr.tail ⟨y, a, rfl⟩, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro v hv hvb
      rcases Finset.mem_insert.mp hv with rfl | hvs
      · exact not_mem_boundVars_boundSubst φ₁ hya hvb
      · rcases Finset.mem_insert.mp (boundVars_boundSubst_subset φ₁ a y hvb) with h | h
        · subst h
          exact hys (Finset.mem_insert_of_mem hvs)
        · exact Finset.disjoint_left.mp hd hvs h
    · intro M σ
      rw [he M σ, eval_boundSubst M φ₁ hy1 σ]

end BoundSubstAux

/-- Lemma 6.4 (Bound Substitution Lemma): Let `φ` be a formula, and let `x₀, …, x_{n-1}` be a
finite sequence of variables. Then by a sequence of bound substitutions there is a formula `φ'`
in which `x₀, …, x_{n-1}` are not bound and `φ ≡ φ'`. -/
theorem bound_substitution_lemma {L : Signature} (φ : Formula L) (n : ℕ) (xs : Fin n → Var) :
    ∃ φ' : Formula L, φ.BoundSubstReach φ' ∧ (∀ i, xs i ∉ φ'.boundVars) ∧ (φ ≡ᶠ φ') := by
  obtain ⟨φ', hr, hd, he⟩ := BoundSubstAux.exists_reach (Finset.univ.image xs) φ
  exact ⟨φ', hr, fun i h => Finset.disjoint_left.mp hd
    (Finset.mem_image_of_mem xs (Finset.mem_univ i)) h, he⟩

end ContinuousFOL
