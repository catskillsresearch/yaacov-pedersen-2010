/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 free/bound variables; vision.md page 11
-/
module

public import Mathlib.Data.Finset.Sort
public import ContinuousFOL.SubstitutionAndCompletions.TermVars
public import ContinuousFOL.LanguageAndSemantics.Formula

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

variable {L : Signature}

/-- Free variables of a formula `φ`. -/
def freeVars : Formula L → Finset Var
  | .rel _ args => Finset.univ.biUnion (fun i => (args i).vars)
  | .tsub α β   => α.freeVars ∪ β.freeVars
  | .neg α      => α.freeVars
  | .half α     => α.freeVars
  | .sup x α    => α.freeVars.erase x

/-- All variables (free or bound) occurring in `φ`. -/
def allVars : Formula L → Finset Var
  | .rel _ args => Finset.univ.biUnion (fun i => (args i).vars)
  | .tsub α β   => α.allVars ∪ β.allVars
  | .neg α      => α.allVars
  | .half α     => α.allVars
  | .sup x α    => insert x α.allVars

/-- The *sup-closure* of `φ`: bind every free variable, in increasing order,
    by a prefix of `sup`. The result is a sentence, and is `φ` itself when `φ`
    is already a sentence. This is the canonical sentence whose degree of truth,
    over a complete theory, coincides with that of `φ`. -/
def supClosure (φ : Formula L) : Formula L :=
  (φ.freeVars.sort (· ≤ ·)).foldr (fun x ψ => .sup x ψ) φ

lemma supClosure_of_freeVars_empty {φ : Formula L} (h : φ.freeVars = ∅) :
    φ.supClosure = φ := by
  rw [supClosure, h, Finset.sort_empty, List.foldr_nil]

lemma foldr_sup_freeVars (xs : List Var) (φ : Formula L) :
    (xs.foldr (fun x ψ => .sup x ψ) φ).freeVars = φ.freeVars \ xs.toFinset := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons, Formula.freeVars, List.toFinset_cons, ih]
    exact (Finset.sdiff_insert _ _ _).symm

lemma toFinset_sort (s : Finset Var) : (s.sort (· ≤ ·)).toFinset = s := by
  ext x
  simp
lemma supClosure_freeVars (φ : Formula L) : φ.supClosure.freeVars = ∅ := by
  rw [supClosure, foldr_sup_freeVars, toFinset_sort, Finset.sdiff_self]

/-- Bound variables occurring in `φ`. -/
def boundVars : Formula L → Finset Var
  | .rel _ _  => ∅
  | .tsub α β => α.boundVars ∪ β.boundVars
  | .neg α    => α.boundVars
  | .half α   => α.boundVars
  | .sup x α  => insert x α.boundVars

end Formula

end ContinuousFOL
