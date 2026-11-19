/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.2; vision.md page 16
-/
module

public import ContinuousFOL.Essentials.InconsistentIffProvableOne
public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeVars

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Lemma 8.2 (Generalization Theorem). -/
theorem generalization_theorem {L : Signature} (Γ : Set (Formula L)) (φ : Formula L)
    (x : Var) (hx : ∀ ψ ∈ Γ, x ∉ ψ.freeVars) (h : ProvableQ Γ φ) :
    ProvableQ Γ (.sup x φ) := by
  induction h with
  | @ax xs ψ hax =>
    -- `sup x (genList xs ψ) = genList (x :: xs) ψ`
    simpa [Formula.genList] using
      (ProvableQ.ax (Γ := Γ) (xs := x :: xs) (ψ := ψ) hax)
  | @hyp ψ hmem =>
    exact ProvableQ.mp (.hyp hmem) (ProvableQ.ax0 (.A9 x ψ (hx ψ hmem)))
  | @mp α ψ hα himp ihα ihimp =>
    -- A7: `sup (ψ ∸ α) → (sup α → sup ψ)`
    have hA7 : ProvableQ Γ
        (.tsub (.tsub (.sup x ψ) (.sup x α)) (.sup x (.tsub ψ α))) :=
      ProvableQ.ax0 (.A7 x α ψ)
    exact ProvableQ.mp ihα (ProvableQ.mp ihimp hA7)

end ContinuousFOL
