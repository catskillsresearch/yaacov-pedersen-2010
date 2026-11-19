/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.1; vision.md page 20–21
-/
module

public import ContinuousFOL.LanguageAndSemantics.FormulaConnectives
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeSubst
public import ContinuousFOL.Group1Axioms.DyadicCode.Val

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Definition 9.1: Henkin completeness of a set of formulae `Γ`. -/
def HenkinComplete {L : Signature} (Γ : Set (Formula L)) : Prop :=
  ∀ (φ : Formula L) (x : Var) (p q : DyadicCode),
    p.val < q.val →
    ∃ (c : L.Func) (hc : L.funcArity c = 0),
      let cTerm : Term L := .func c (fun i => (Fin.elim0 (Fin.cast hc i)))
      Formula.minF (.tsub (.sup x φ) (Formula.dyadic L q))
                   (.tsub (Formula.dyadic L p) (φ.freeSubst cTerm x)) ∈ Γ

end ContinuousFOL
