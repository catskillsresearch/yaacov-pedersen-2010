/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 term model construction; vision.md page 21–22
-/
module

public import ContinuousFOL.LanguageAndSemantics.PreStructure
public import ContinuousFOL.LanguageAndSemantics.TermEval
public import ContinuousFOL.LanguageAndSemantics.FormulaEval
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.Group1Axioms.DyadicCode.Val
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Canonical syntactic term pre-structure built from a maximal consistent set `Δ`
    (Proof of Theorem 9.4). -/
def termPreStructure {L : Signature} (Δ : Set (Formula L)) : PreStructure L where
  Carrier    := Term L
  nonempty   := ⟨.var 0⟩
  funcInterp := fun f args => .func f args
  relInterp  := fun P args =>
    sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
      Formula.tsub (Formula.dyadic L p) (.rel P args) ∈ Δ}
  rel_in_Icc := by
    intro P args
    set S := {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
      Formula.tsub (Formula.dyadic L p) (.rel P args) ∈ Δ}
    by_cases hne : S.Nonempty
    · have hbdd : BddAbove S := ⟨1, by rintro _ ⟨p, rfl, _⟩; exact (p.val_mem_Icc).2⟩
      refine ⟨?_, csSup_le hne (by rintro _ ⟨p, rfl, _⟩; exact (p.val_mem_Icc).2)⟩
      obtain ⟨r₀, hr₀⟩ := hne
      obtain ⟨p₀, rfl, hp₀⟩ := hr₀
      exact le_trans (p₀.val_mem_Icc).1 (le_csSup hbdd ⟨p₀, rfl, hp₀⟩)
    · have hS : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simp [hS, Real.sSup_empty]

/-- Canonical identity assignment `σ(x) = x` in the term pre-structure. -/
def idTermAssign (L : Signature) : Var → Term L := Term.var

@[simp] lemma term_eval_idTermAssign {L : Signature} (Δ : Set (Formula L)) (t : Term L) :
    t.eval (termPreStructure Δ) (idTermAssign L) = t := by
  induction t with
  | var x => rfl
  | func f args ih =>
    simp only [Term.eval, termPreStructure]
    congr 1; ext i; exact ih i

end ContinuousFOL
