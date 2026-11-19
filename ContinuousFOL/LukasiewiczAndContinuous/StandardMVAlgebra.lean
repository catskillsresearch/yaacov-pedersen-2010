/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: the standard MV-algebra on `[0, 1]`, used for Fact 4.1.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.MVAlgebra
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormEval
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormModels
public import ContinuousFOL.Introduction.TsubR
public import Mathlib.Topology.UnitInterval
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- The standard MV-sum on the unit interval: `x ⊕ y = min(x + y, 1)`. -/
def unitIAdd (x y : unitInterval) : unitInterval :=
  ⟨min ((x : ℝ) + y) 1, by
    have hx0 : 0 ≤ (x : ℝ) := x.2.1
    have hy0 : 0 ≤ (y : ℝ) := y.2.1
    exact ⟨le_min (add_nonneg hx0 hy0) zero_le_one, min_le_right _ _⟩⟩

lemma coe_unitIAdd (x y : unitInterval) :
    (unitIAdd x y : ℝ) = min ((x : ℝ) + y) 1 :=
  rfl

lemma coe_zero_unitI : ((0 : unitInterval) : ℝ) = 0 :=
  rfl

lemma coe_one_unitI : ((1 : unitInterval) : ℝ) = 1 :=
  rfl

lemma coe_symm (x : unitInterval) :
    (unitInterval.symm x : ℝ) = 1 - x :=
  unitInterval.coe_symm_eq x

/-- `¬(¬x ⊕ y)` on `[0, 1]` is truncated subtraction. -/
lemma coe_symm_unitIAdd_symm (x y : unitInterval) :
    (unitInterval.symm (unitIAdd (unitInterval.symm x) y) : ℝ) = (x : ℝ) ∸ (y : ℝ) := by
  rw [coe_symm, coe_unitIAdd, coe_symm, tsubR.def_eq]
  by_cases h : 1 - (x : ℝ) + (y : ℝ) ≤ 1
  · rw [min_eq_left h]
    have : 1 - (1 - (x : ℝ) + (y : ℝ)) = (x : ℝ) - y := by ring
    rw [this]
    -- `1 - x + y ≤ 1` iff `y ≤ x` iff `0 ≤ x - y`.
    have h' : 0 ≤ (x : ℝ) - y := by linarith
    rw [max_eq_left h']
  · have h' : 1 < 1 - (x : ℝ) + (y : ℝ) := lt_of_not_ge h
    rw [min_eq_right (le_of_lt h'), sub_self]
    have hneg : (x : ℝ) - y < 0 := by linarith
    exact (max_eq_right (le_of_lt hneg)).symm

/-- Associativity of `min(x + y, 1)` on `[0, 1]`. -/
lemma unitIAdd_assoc (x y z : unitInterval) :
    unitIAdd x (unitIAdd y z) = unitIAdd (unitIAdd x y) z := by
  apply Subtype.ext
  set a := (x : ℝ)
  set b := (y : ℝ)
  set c := (z : ℝ)
  have ha0 : 0 ≤ a := x.2.1
  have hb0 : 0 ≤ b := y.2.1
  have hc0 : 0 ≤ c := z.2.1
  change min (a + min (b + c) 1) 1 = min (min (a + b) 1 + c) 1
  by_cases hbc : b + c ≤ 1
  · rw [min_eq_left hbc]
    by_cases hab : a + b ≤ 1
    · rw [min_eq_left hab, add_assoc]
    · have hab' : 1 < a + b := lt_of_not_ge hab
      rw [min_eq_right (le_of_lt hab')]
      have hL : min (a + (b + c)) 1 = 1 := by
        apply min_eq_right
        linarith
      have hR : min (1 + c) 1 = 1 := min_eq_right (by linarith)
      rw [hL, hR]
  · have hbc' : 1 < b + c := lt_of_not_ge hbc
    rw [min_eq_right (le_of_lt hbc')]
    have hL : min (a + 1) 1 = 1 := min_eq_right (by linarith)
    rw [hL]
    by_cases hab : a + b ≤ 1
    · rw [min_eq_left hab]
      have : min (a + b + c) 1 = 1 := by
        apply min_eq_right
        linarith
      exact this.symm
    · have hab' : 1 < a + b := lt_of_not_ge hab
      rw [min_eq_right (le_of_lt hab')]
      have : min (1 + c) 1 = 1 := min_eq_right (by linarith)
      exact this.symm

/-- The join `(x ⊖ y) ⊕ y` is `max(x, y)` on `[0, 1]`. -/
lemma coe_symm_add_symm_add (x y : unitInterval) :
    (unitIAdd (unitInterval.symm (unitIAdd (unitInterval.symm x) y)) y : ℝ) =
      max (x : ℝ) (y : ℝ) := by
  have hx1 : (x : ℝ) ≤ 1 := x.2.2
  have hy1 : (y : ℝ) ≤ 1 := y.2.2
  rw [coe_unitIAdd, coe_symm_unitIAdd_symm, tsubR.def_eq]
  by_cases hxy : (x : ℝ) ≤ y
  · have : (x : ℝ) - y ≤ 0 := by linarith
    rw [max_eq_right this, zero_add, min_eq_left hy1, max_eq_right hxy]
  · have hxy' : (y : ℝ) < x := lt_of_not_ge hxy
    have : 0 ≤ (x : ℝ) - y := by linarith
    rw [max_eq_left this]
    have : min ((x : ℝ) - y + y) 1 = (x : ℝ) := by
      have : (x : ℝ) - y + y = x := by ring
      rw [this, min_eq_left hx1]
    rw [this, max_eq_left (le_of_lt hxy')]

/-- The standard MV-algebra on `[0, 1]`. -/
instance unitInterval.instMVAlgebra : MVAlgebra unitInterval where
  add := unitIAdd
  neg := unitInterval.symm
  zero := 0
  add_assoc := unitIAdd_assoc
  add_comm := by
    intro x y
    apply Subtype.ext
    simp [coe_unitIAdd, add_comm]
  add_zero := by
    intro x
    apply Subtype.ext
    rw [coe_unitIAdd, coe_zero_unitI, add_zero, min_eq_left x.2.2]
  neg_neg := unitInterval.symm_symm
  add_neg_zero := by
    intro x
    apply Subtype.ext
    rw [coe_unitIAdd, coe_symm, coe_zero_unitI, sub_zero]
    exact min_eq_right (le_add_of_nonneg_left x.2.1)
  add_absorp := by
    intro x y
    apply Subtype.ext
    rw [coe_symm_add_symm_add, coe_symm_add_symm_add, max_comm]

open MVAlgebra

lemma coe_msub (x y : unitInterval) :
    ((x ⊖ y : unitInterval) : ℝ) = (x : ℝ) ∸ (y : ℝ) :=
  coe_symm_unitIAdd_symm x y

lemma coe_mv_neg (x : unitInterval) :
    ((∼x : unitInterval) : ℝ) = 1 - x := by
  rw [show (∼x) = unitInterval.symm x from rfl, coe_symm]

lemma coe_mv_zero : ((0 : unitInterval) : ℝ) = 0 :=
  coe_zero_unitI

/-- Evaluation of a Łukasiewicz formula in an arbitrary MV-algebra. -/
def evalMV {ι A : Type*} [MVAlgebra A] (v : ι → A) : LukPropForm ι → A
  | .var i => v i
  | .tsub φ ψ => evalMV v φ ⊖ evalMV v ψ
  | .neg φ => ∼(evalMV v φ)

/-- On the standard algebra, MV-evaluation agrees with the real-valued evaluation
    used in the paper (Definition 2.1). -/
lemma evalMV_coe {ι : Type*} (v : ι → unitInterval) (φ : LukPropForm ι) :
    ((evalMV (A := unitInterval) v φ : unitInterval) : ℝ) =
    LukPropForm.eval (fun i => (v i : ℝ)) φ := by
  induction φ with
  | var i =>
    rfl
  | tsub φ ψ ihφ ihψ =>
    simp [evalMV, LukPropForm.eval, coe_msub, ihφ, ihψ]
  | neg φ ih =>
    simp [evalMV, LukPropForm.eval, coe_mv_neg, ih]

/-- A real assignment with values in `[0, 1]` lifts to the standard MV-algebra. -/
def liftVal {ι : Type*} (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) : ι → unitInterval :=
  fun i => ⟨v i, hv i⟩

lemma coe_liftVal {ι : Type*} (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (i : ι) :
    (liftVal v hv i : ℝ) = v i :=
  rfl

/-- Fact 4.1's semantic side, in MV-algebra form: `⊨ φ` iff `φ` evaluates to `0`
    under every assignment in the standard MV-algebra on `[0, 1]`. -/
lemma entails_empty_iff_evalMV {ι : Type*} (φ : LukPropForm ι) :
    LukPropForm.Entails ∅ φ ↔ ∀ v : ι → unitInterval, evalMV v φ = 0 := by
  constructor
  · intro h v
    have hv : ∀ i, 0 ≤ (v i : ℝ) ∧ (v i : ℝ) ≤ 1 := fun i => (v i).2
    have hmod : LukPropForm.Models (fun i => (v i : ℝ)) (∅ : Set (LukPropForm ι)) :=
      ⟨hv, fun _ hmem => by cases hmem⟩
    have heq := h _ hmod
    apply Subtype.ext
    rw [evalMV_coe, heq, coe_zero_unitI]
  · intro h v hv
    have hmod0 : ∀ i, 0 ≤ v i ∧ v i ≤ 1 := hv.1
    have heq0 := h (liftVal v hmod0)
    have hcoe := congrArg (fun x : unitInterval => (x : ℝ)) heq0
    rw [evalMV_coe] at hcoe
    have hv' : (fun i => (liftVal v hmod0 i : ℝ)) = v := by
      funext i
      rfl
    rw [hv', coe_zero_unitI] at hcoe
    exact hcoe

end ContinuousFOL
