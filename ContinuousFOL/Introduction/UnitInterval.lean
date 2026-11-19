/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: unit interval closure lemmas for ¬ and ½
-/
module

public import ContinuousFOL.Introduction.TsubR
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

lemma unit_closed_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 1 - x ∧ 1 - x ≤ 1 := by
  constructor <;> linarith

lemma unit_closed_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x / 2 ∧ x / 2 ≤ 1 := by
  constructor <;> linarith

end ContinuousFOL
