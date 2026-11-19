/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.11; vision.md page 9–10
-/
module

public import ContinuousFOL.LanguageAndSemantics.TermEval
public import ContinuousFOL.LanguageAndSemantics.UpdateAssign
public import ContinuousFOL.LanguageAndSemantics.FormulaOne
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.Introduction.UnitInterval
public import ContinuousFOL.Group1Axioms.DyadicCode.Val
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Value of a formula `𝔐(φ, σ)` in `[0, 1]` (Definition 5.11). -/
def Formula.eval {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier) : Formula L → ℝ
  | .rel P args => M.relInterp P (fun i => (args i).eval M σ)
  | .tsub α β   => α.eval M σ ∸ β.eval M σ
  | .neg α      => 1 - α.eval M σ
  | .half α     => α.eval M σ / 2
  | .sup x α    => sSup (Set.range (fun a : M.Carrier => α.eval M (updateAssign σ x a)))

lemma Formula.eval_in_Icc {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (φ : Formula L) : 0 ≤ φ.eval M σ ∧ φ.eval M σ ≤ 1 := by
  induction φ generalizing σ with
  | rel P args => exact M.rel_in_Icc P _
  | tsub α β ihα ihβ => exact tsubR.unitClosed (ihα σ).1 (ihα σ).2 (ihβ σ).1
  | neg α ih => exact unit_closed_neg (ih σ).1 (ih σ).2
  | half α ih => exact unit_closed_half (ih σ).1 (ih σ).2
  | sup x α ih =>
    let S := Set.range (fun a : M.Carrier => α.eval M (updateAssign σ x a))
    have hne : S.Nonempty := Set.range_nonempty _
    have hbdd : BddAbove S := ⟨1, by rintro _ ⟨a, rfl⟩; exact (ih _).2⟩
    refine ⟨?_, csSup_le hne (by rintro _ ⟨a, rfl⟩; exact (ih _).2)⟩
    obtain ⟨a₀⟩ := M.nonempty
    exact le_trans (ih (updateAssign σ x a₀)).1 (le_csSup hbdd ⟨a₀, rfl⟩)

@[simp] lemma Formula.eval_one {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier) :
    (Formula.one L).eval M σ = 1 := by
  simp [Formula.one, Formula.eval, tsubR]

@[simp] lemma Formula.eval_dyadic {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (d : DyadicCode) : (Formula.dyadic L d).eval M σ = d.val := by
  induction d with
  | one => simp [Formula.dyadic]
  | neg d ih => simp [Formula.dyadic, Formula.eval, DyadicCode.val, ih]
  | tsub a b iha ihb => simp [Formula.dyadic, Formula.eval, DyadicCode.val, iha, ihb]
  | half d ih => simp [Formula.dyadic, Formula.eval, DyadicCode.val, ih]

/-- Remark 3.4 under an arbitrary assignment: `{M(d, σ) : d ∈ 𝒟} = 𝔻`. -/
theorem Formula.eval_dyadic_range {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier) :
    (Set.range fun d : DyadicCode => (Formula.dyadic L d).eval M σ) = DyadicCode.dyadics := by
  simp [Formula.eval_dyadic, DyadicCode.val_range_eq_dyadics]

end ContinuousFOL
