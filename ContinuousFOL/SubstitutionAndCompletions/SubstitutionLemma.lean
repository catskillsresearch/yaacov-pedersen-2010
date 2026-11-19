/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Lemma 6.2; vision.md page 11
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeSubst
public import ContinuousFOL.LanguageAndSemantics.FormulaEval
public import ContinuousFOL.LanguageAndSemantics.UpdateAssign

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

lemma updateAssign_comm {M : Type*} (σ : Var → M) {x y : Var} (hxy : x ≠ y) (a v : M) :
    updateAssign (updateAssign σ y a) x v = updateAssign (updateAssign σ x v) y a := by
  funext z
  simp only [updateAssign]
  by_cases hx : x = z
  · subst hx
    have : ¬(y = x) := hxy.symm
    simp [this]
  · by_cases hy : y = z
    · subst hy
      simp [hxy]
    · simp [hx, hy]

lemma Term.eval_subst {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (t : Term L) (x : Var) (s : Term L) :
    (s.subst t x).eval M σ = s.eval M (updateAssign σ x (t.eval M σ)) := by
  induction s with
  | var y =>
    by_cases h : y = x
    · subst h; simp [Term.subst, Term.eval, updateAssign]
    · simp [Term.subst, Term.eval, updateAssign, h, Ne.symm h]
  | func f args ih =>
    simp only [Term.subst, Term.eval]
    congr 1
    ext i
    exact ih i

lemma Term.eval_update_of_not_mem_vars {L : Signature} (M : PreStructure L)
    (σ : Var → M.Carrier) (y : Var) (a : M.Carrier) (t : Term L) (hy : y ∉ t.vars) :
    t.eval M (updateAssign σ y a) = t.eval M σ := by
  induction t with
  | var z =>
    have hz : y ≠ z := by
      intro h; subst h; simp [Term.vars] at hy
    simp [Term.eval, updateAssign, hz]
  | func f args ih =>
    have hy' : ∀ i, y ∉ (args i).vars := by
      intro i hi
      apply hy
      simp only [Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, hi⟩
    simp only [Term.eval]
    congr 1
    ext i
    exact ih i (hy' i)

lemma Formula.eval_update_of_not_mem_freeVars {L : Signature} (M : PreStructure L)
    (σ : Var → M.Carrier) (x : Var) (a : M.Carrier) (φ : Formula L)
    (hx : x ∉ φ.freeVars) :
    φ.eval M (updateAssign σ x a) = φ.eval M σ := by
  induction φ generalizing σ with
  | rel P args =>
    have hx' : ∀ i, x ∉ (args i).vars := by
      intro i hi
      apply hx
      simp only [Formula.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, hi⟩
    simp only [Formula.eval]
    congr 1
    ext i
    exact Term.eval_update_of_not_mem_vars M σ x a (args i) (hx' i)
  | tsub α β ihα ihβ =>
    have hxα : x ∉ α.freeVars := fun h => hx (Finset.mem_union_left _ h)
    have hxβ : x ∉ β.freeVars := fun h => hx (Finset.mem_union_right _ h)
    simp [Formula.eval, ihα σ hxα, ihβ σ hxβ]
  | neg α ih =>
    have hxα : x ∉ α.freeVars := by simpa [Formula.freeVars] using hx
    simp [Formula.eval, ih σ hxα]
  | half α ih =>
    have hxα : x ∉ α.freeVars := by simpa [Formula.freeVars] using hx
    simp [Formula.eval, ih σ hxα]
  | sup y α ih =>
    simp only [Formula.eval]
    congr 1
    ext r
    simp only [Set.mem_range]
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      by_cases hxy : x = y
      · subst hxy
        have : updateAssign (updateAssign σ x a) x b = updateAssign σ x b := by
          funext z; simp [updateAssign]; split_ifs <;> rfl
        rw [this]
      · have hxα : x ∉ α.freeVars := fun hmem =>
          hx (Finset.mem_erase.mpr ⟨hxy, hmem⟩)
        -- ih: eval (update (update σ y b) x a) = eval (update σ y b)
        have := (ih (updateAssign σ y b) hxα).symm
        rw [this, updateAssign_comm σ hxy b a]
    · rintro ⟨b, rfl⟩
      refine ⟨b, ?_⟩
      by_cases hxy : x = y
      · subst hxy
        have : updateAssign (updateAssign σ x a) x b = updateAssign σ x b := by
          funext z; simp [updateAssign]; split_ifs <;> rfl
        rw [this]
      · have hxα : x ∉ α.freeVars := fun hmem =>
          hx (Finset.mem_erase.mpr ⟨hxy, hmem⟩)
        have := ih (updateAssign σ y b) hxα
        rw [← updateAssign_comm σ hxy b a, this]

/-- Lemma 6.2 (Substitution Lemma). -/
theorem substitution_lemma {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (t : Term L) (x : Var) (φ : Formula L) (hcorr : φ.FreeSubstCorrect t x) :
    (φ.freeSubst t x).eval M σ = φ.eval M (updateAssign σ x (t.eval M σ)) := by
  induction φ generalizing σ with
  | rel P args =>
    simp only [Formula.freeSubst, Formula.eval]
    congr 1
    ext i
    exact Term.eval_subst M σ t x (args i)
  | tsub α β ihα ihβ =>
    obtain ⟨hα, hβ⟩ : α.FreeSubstCorrect t x ∧ β.FreeSubstCorrect t x := by
      simpa [Formula.FreeSubstCorrect] using hcorr
    simp [Formula.freeSubst, Formula.eval, ihα σ hα, ihβ σ hβ]
  | neg α ih =>
    have hα : α.FreeSubstCorrect t x := by simpa [Formula.FreeSubstCorrect] using hcorr
    simp [Formula.freeSubst, Formula.eval, ih σ hα]
  | half α ih =>
    have hα : α.FreeSubstCorrect t x := by simpa [Formula.FreeSubstCorrect] using hcorr
    simp [Formula.freeSubst, Formula.eval, ih σ hα]
  | sup y α ih =>
    by_cases hxy : y = x
    · subst hxy
      simp only [Formula.freeSubst, Formula.eval, ↓reduceIte]
      congr 1
      ext r
      simp only [Set.mem_range]
      constructor
      · rintro ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        have : updateAssign (updateAssign σ y (t.eval M σ)) y a = updateAssign σ y a := by
          funext z; simp [updateAssign]; split_ifs <;> rfl
        rw [this]
      · rintro ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        have : updateAssign (updateAssign σ y (t.eval M σ)) y a = updateAssign σ y a := by
          funext z; simp [updateAssign]; split_ifs <;> rfl
        rw [this]
    · have hcorr' : (x ∈ α.freeVars → y ∉ t.vars) ∧ α.FreeSubstCorrect t x := by
        simpa [Formula.FreeSubstCorrect, hxy] using hcorr
      simp only [Formula.freeSubst, Formula.eval, hxy, ↓reduceIte]
      congr 1
      ext r
      simp only [Set.mem_range]
      -- f a := (α.freeSubst).eval (update σ y a)
      -- g a := α.eval (update (update σ x t.eval) y a)
      constructor
      · -- f a = r ⊢ ∃ b, g b = r; take b = a, need g a = f a
        rintro ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        have iht := (ih (updateAssign σ y a) hcorr'.2).symm
        have ht_align :
            α.eval M (updateAssign (updateAssign σ y a) x (t.eval M σ)) =
              α.eval M (updateAssign (updateAssign σ y a) x
                (t.eval M (updateAssign σ y a))) := by
          by_cases hxfree : x ∈ α.freeVars
          · rw [Term.eval_update_of_not_mem_vars M σ y a t (hcorr'.1 hxfree)]
          · rw [Formula.eval_update_of_not_mem_freeVars M (updateAssign σ y a) x
                (t.eval M σ) α hxfree,
              Formula.eval_update_of_not_mem_freeVars M (updateAssign σ y a) x
                (t.eval M (updateAssign σ y a)) α hxfree]
        calc
          α.eval M (updateAssign (updateAssign σ x (t.eval M σ)) y a)
              = α.eval M (updateAssign (updateAssign σ y a) x (t.eval M σ)) := by
                rw [updateAssign_comm σ (Ne.symm hxy) a (t.eval M σ)]
          _ = α.eval M (updateAssign (updateAssign σ y a) x
                (t.eval M (updateAssign σ y a))) := ht_align
          _ = (α.freeSubst t x).eval M (updateAssign σ y a) := iht
      · -- g a = r ⊢ ∃ b, f b = r; take b = a, need f a = g a
        rintro ⟨a, rfl⟩
        refine ⟨a, ?_⟩
        have iht := ih (updateAssign σ y a) hcorr'.2
        have ht_align :
            α.eval M (updateAssign (updateAssign σ y a) x
                (t.eval M (updateAssign σ y a))) =
              α.eval M (updateAssign (updateAssign σ y a) x (t.eval M σ)) := by
          by_cases hxfree : x ∈ α.freeVars
          · rw [Term.eval_update_of_not_mem_vars M σ y a t (hcorr'.1 hxfree)]
          · rw [Formula.eval_update_of_not_mem_freeVars M (updateAssign σ y a) x
                (t.eval M (updateAssign σ y a)) α hxfree,
              Formula.eval_update_of_not_mem_freeVars M (updateAssign σ y a) x
                (t.eval M σ) α hxfree]
        calc
          (α.freeSubst t x).eval M (updateAssign σ y a)
              = α.eval M (updateAssign (updateAssign σ y a) x
                  (t.eval M (updateAssign σ y a))) := iht
          _ = α.eval M (updateAssign (updateAssign σ y a) x (t.eval M σ)) := ht_align
          _ = α.eval M (updateAssign (updateAssign σ x (t.eval M σ)) y a) := by
                rw [updateAssign_comm σ (Ne.symm hxy) a (t.eval M σ)]

end ContinuousFOL
