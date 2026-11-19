/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Remark 3.4 / Notation 3.3 evaluation
-/
module

public import ContinuousFOL.Group1Axioms.DyadicCode.Pow2Neg
public import ContinuousFOL.Group1Axioms.DyadicCode.Zero
public import ContinuousFOL.Introduction.UnitInterval
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace DyadicCode

/-- Real evaluation of a dyadic code in `[0, 1]`. -/
def val : DyadicCode → ℝ
  | .one      => 1
  | .neg d    => 1 - d.val
  | .tsub a b => a.val ∸ b.val
  | .half d   => d.val / 2

@[simp] lemma val_one : DyadicCode.one.val = 1 := rfl
@[simp] lemma val_zero : DyadicCode.zero.val = 0 := by simp [zero, val]

lemma val_pow2Neg (n : ℕ) : (pow2Neg n).val = (2 : ℝ) ^ (-(n : ℤ)) := by
  induction n with
  | zero => simp [pow2Neg]
  | succ n ih =>
    change (pow2Neg n).val / 2 = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ))
    rw [ih, div_eq_mul_inv, ← zpow_neg_one (2 : ℝ), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    omega

lemma val_mem_Icc (d : DyadicCode) : 0 ≤ d.val ∧ d.val ≤ 1 := by
  induction d with
  | one => simp [val]
  | neg d ih => exact unit_closed_neg ih.1 ih.2
  | tsub a b iha ihb => exact tsubR.unitClosed iha.1 iha.2 ihb.1
  | half d ih => exact unit_closed_half ih.1 ih.2

/-- Every dyadic rational `k / 2^n` in `[0, 1]` is realized by a `DyadicCode` (Remark 3.4). -/
lemma dense_in_Icc {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y) :
    ∃ d : DyadicCode, x < d.val ∧ d.val < y := by
  sorry

end DyadicCode

end ContinuousFOL
