/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: preliminaries; used throughout (cf. vision.md)
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Truncated subtraction on ℝ: `x ∸ y = max (x - y) 0`. -/
def tsubR (x y : ℝ) : ℝ := max (x - y) 0

infixl:65 " ∸ " => tsubR

namespace tsubR

@[simp] lemma def_eq (x y : ℝ) : x ∸ y = max (x - y) 0 := rfl

lemma nonneg (x y : ℝ) : 0 ≤ x ∸ y := le_max_right _ _

lemma eq_zero_iff (x y : ℝ) : x ∸ y = 0 ↔ x ≤ y := by
  simp [tsubR]

lemma le_iff (x y z : ℝ) (hz : 0 ≤ z) : x ∸ y ≤ z ↔ x - y ≤ z := by
  simp [tsubR, hz]

lemma unitClosed {x y : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) (_hy0 : 0 ≤ y) :
    0 ≤ x ∸ y ∧ x ∸ y ≤ 1 := by
  refine ⟨nonneg x y, max_le ?_ zero_le_one⟩
  linarith

end tsubR

end ContinuousFOL
