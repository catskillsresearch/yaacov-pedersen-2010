/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: preliminaries; used throughout (cf. vision.md)
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

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

lemma tsub_le_self {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : x ∸ y ≤ x := by
  have hsub : x - y ≤ x := by linarith
  rw [def_eq]
  exact max_le hsub hx

lemma le_add_tsub (x y : ℝ) : x ≤ y + (x ∸ y) := by
  by_cases h : x ≤ y
  · have h0 : x - y ≤ 0 := by linarith
    rw [show x ∸ y = 0 by rw [def_eq, max_eq_right h0]]
    linarith
  · push Not at h
    have h0 : 0 ≤ x - y := by linarith
    rw [show x ∸ y = x - y by rw [def_eq, max_eq_left h0]]
    linarith

lemma sub_le_iff_add {x y z : ℝ} (hz : 0 ≤ z) : x ∸ y ≤ z ↔ x ≤ y + z := by
  rw [le_iff x y z hz]
  constructor <;> intro h <;> linarith

/-- `((c ∸ a) ∸ (c ∸ b)) ≤ b ∸ a`, the real form of (A2). -/
lemma tsub_tsub_le (a b c : ℝ) : (c ∸ a) ∸ (c ∸ b) ≤ b ∸ a := by
  by_cases hcb : c ≤ b
  · have hb0 : c ∸ b = 0 := (eq_zero_iff c b).mpr hcb
    have hleft : (c ∸ a) ∸ (c ∸ b) = c ∸ a := by
      rw [hb0, def_eq]
      have hsub : c ∸ a - 0 = c ∸ a := by ring
      rw [hsub]
      exact max_eq_left (nonneg c a)
    rw [hleft]
    by_cases hca : c ≤ a
    · rw [(eq_zero_iff c a).mpr hca]
      exact nonneg b a
    · push Not at hca
      have hca' : c ∸ a = c - a := by
        rw [def_eq, max_eq_left (show 0 ≤ c - a by linarith)]
      rw [hca']
      have hab : a < b := by linarith
      have hba : b ∸ a = b - a := by
        rw [def_eq, max_eq_left (show 0 ≤ b - a by linarith)]
      rw [hba]
      linarith
  · push Not at hcb
    by_cases hca : c ≤ a
    · have ha0 : c ∸ a = 0 := (eq_zero_iff c a).mpr hca
      rw [ha0, def_eq]
      have hsub : (0 : ℝ) - (c ∸ b) ≤ 0 := by linarith [nonneg c b]
      rw [max_eq_right hsub]
      exact nonneg b a
    · push Not at hca
      have hca' : c ∸ a = c - a := by
        rw [def_eq, max_eq_left (show 0 ≤ c - a by linarith)]
      have hcb' : c ∸ b = c - b := by
        rw [def_eq, max_eq_left (show 0 ≤ c - b by linarith)]
      rw [hca', hcb', def_eq]
      have hdiff : (c - a) - (c - b) = b - a := by ring
      rw [hdiff, def_eq]

lemma tsub_tsub_eq_min {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ∸ (x ∸ y) = min x y := by
  by_cases h : x ≤ y
  · have h0 : x ∸ y = 0 := (eq_zero_iff x y).mpr h
    rw [h0, def_eq]
    have hsub : x - 0 = x := by ring
    rw [hsub, max_eq_left hx]
    exact (min_eq_left h).symm
  · push Not at h
    have hxy : x ∸ y = x - y := by
      rw [def_eq, max_eq_left (show 0 ≤ x - y by linarith)]
    rw [hxy]
    have hr : x - (x - y) = y := by ring
    rw [def_eq, hr, max_eq_left hy]
    exact (min_eq_right (le_of_lt h)).symm

lemma neg_congr (x y : ℝ) : (1 - y) ∸ (1 - x) = x ∸ y := by
  have h : (1 - y) - (1 - x) = x - y := by ring
  rw [def_eq, def_eq, h]

lemma half_tsub {x : ℝ} (hx : 0 ≤ x) : x ∸ (x / 2) = x / 2 := by
  have h : x - x / 2 = x / 2 := by ring
  have h0 : 0 ≤ x / 2 := by linarith
  rw [def_eq, h, max_eq_left h0]

end tsubR

end ContinuousFOL
