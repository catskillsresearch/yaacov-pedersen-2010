/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Definition 6.5 / Theorem 6.6; vision.md page 12
-/
module

public import ContinuousFOL.LanguageAndSemantics.PreStructure
public import ContinuousFOL.LanguageAndSemantics.Formula
public import ContinuousFOL.LanguageAndSemantics.TermEval
public import ContinuousFOL.LanguageAndSemantics.FormulaEval
public import ContinuousFOL.LanguageAndSemantics.UpdateAssign

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- An `𝓛`-morphism between pre-structures (Definition 6.5). -/
structure LMorphism {L : Signature} (M N : PreStructure L) where
  toFun    : M.Carrier → N.Carrier
  map_func : ∀ (f : L.Func) (args : Fin (L.funcArity f) → M.Carrier),
    toFun (M.funcInterp f args) = N.funcInterp f (fun i => toFun (args i))
  map_rel  : ∀ (P : L.Rel) (args : Fin (L.relArity P) → M.Carrier),
    M.relInterp P args = N.relInterp P (fun i => toFun (args i))

namespace LMorphism

lemma map_term {L : Signature} {M N : PreStructure L} (h : LMorphism M N)
    (σ : Var → M.Carrier) (t : Term L) :
    h.toFun (t.eval M σ) = t.eval N (h.toFun ∘ σ) := by
  induction t with
  | var x => rfl
  | func f args ih =>
    simp only [Term.eval, h.map_func]
    congr 1; ext i; exact ih i

end LMorphism

/-- Theorem 6.6: Every surjective `𝓛`-morphism is elementary. -/
theorem surjective_morphism_elementary {L : Signature} {M N : PreStructure L}
    (h : LMorphism M N) (hsurj : Function.Surjective h.toFun) :
    ∀ (σ : Var → M.Carrier) (φ : Formula L), φ.eval M σ = φ.eval N (h.toFun ∘ σ) := by
  intro σ φ
  induction φ generalizing σ with
  | rel P args =>
    simp only [Formula.eval, h.map_rel]
    congr 1; ext i; exact h.map_term σ (args i)
  | tsub α β ihα ihβ => simp [Formula.eval, ihα σ, ihβ σ]
  | neg α ih => simp [Formula.eval, ih σ]
  | half α ih => simp [Formula.eval, ih σ]
  | sup x α ih =>
    simp only [Formula.eval]
    congr 1
    ext r
    simp only [Set.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨h.toFun a, ?_⟩
      rw [ih (updateAssign σ x a)]
      congr 1; ext y; by_cases hxy : x = y <;> simp [updateAssign, hxy]
    · rintro ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj b
      refine ⟨a, ?_⟩
      rw [ih (updateAssign σ x a)]
      congr 1; ext y; by_cases hxy : x = y <;> simp [updateAssign, hxy]

end ContinuousFOL
