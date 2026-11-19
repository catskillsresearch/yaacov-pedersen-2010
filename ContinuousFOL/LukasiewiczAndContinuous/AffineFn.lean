/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Affine functions on the unit cube, used for piecewise-linear evaluation
of propositional formulae.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

noncomputable section
open Classical
open Finset

namespace ContinuousFOL

/-- An affine map `(Fin n → ℝ) → ℝ`. -/
structure AffineFn (n : ℕ) where
  offset : ℝ
  weights : Fin n → ℝ
  deriving DecidableEq

namespace AffineFn

variable {n : ℕ}

def eval (a : AffineFn n) (x : Fin n → ℝ) : ℝ :=
  a.offset + ∑ i, a.weights i * x i

def const (c : ℝ) : AffineFn n :=
  ⟨c, fun _ => 0⟩

def proj (i : Fin n) : AffineFn n :=
  ⟨0, fun j => if j = i then 1 else 0⟩

def add (a b : AffineFn n) : AffineFn n :=
  ⟨a.offset + b.offset, fun i => a.weights i + b.weights i⟩

def smul (c : ℝ) (a : AffineFn n) : AffineFn n :=
  ⟨c * a.offset, fun i => c * a.weights i⟩

def neg (a : AffineFn n) : AffineFn n :=
  a.smul (-1)

def sub (a b : AffineFn n) : AffineFn n :=
  a.add b.neg

lemma eval_const (c : ℝ) (x : Fin n → ℝ) : (const c).eval x = c := by
  simp [eval, const]

lemma eval_proj (i : Fin n) (x : Fin n → ℝ) : (proj i).eval x = x i := by
  simp [eval, proj]

lemma eval_add (a b : AffineFn n) (x : Fin n → ℝ) :
    (a.add b).eval x = a.eval x + b.eval x := by
  calc
    (a.add b).eval x
        = (a.offset + b.offset) + ∑ i, (a.weights i + b.weights i) * x i := rfl
    _   = (a.offset + b.offset) + ∑ i, (a.weights i * x i + b.weights i * x i) := by
          simp [add_mul]
    _   = (a.offset + b.offset) + ((∑ i, a.weights i * x i) + (∑ i, b.weights i * x i)) := by
          rw [sum_add_distrib]
    _   = a.eval x + b.eval x := by
          simp [eval]; ring

lemma eval_smul (c : ℝ) (a : AffineFn n) (x : Fin n → ℝ) :
    (a.smul c).eval x = c * a.eval x := by
  calc
    (a.smul c).eval x
        = c * a.offset + ∑ i, (c * a.weights i) * x i := rfl
    _   = c * a.offset + ∑ i, c * (a.weights i * x i) := by
          simp [mul_assoc]
    _   = c * a.offset + c * ∑ i, a.weights i * x i := by
          rw [← mul_sum]
    _   = c * a.eval x := by
          simp [eval]; ring

lemma eval_neg (a : AffineFn n) (x : Fin n → ℝ) :
    a.neg.eval x = -a.eval x := by
  simp [neg, eval_smul]

lemma eval_sub (a b : AffineFn n) (x : Fin n → ℝ) :
    (a.sub b).eval x = a.eval x - b.eval x := by
  simp [sub, eval_add, eval_neg]
  ring

/-- Affine maps send affine combinations to affine combinations. -/
lemma eval_line (a : AffineFn n) (x y : Fin n → ℝ) (t : ℝ) :
    a.eval (fun i => x i + t * (y i - x i)) =
      a.eval x + t * (a.eval y - a.eval x) := by
  unfold eval
  have hterm : ∀ i, a.weights i * (x i + t * (y i - x i)) =
      a.weights i * x i + t * (a.weights i * y i - a.weights i * x i) := by
    intro i; ring
  simp_rw [hterm]
  rw [sum_add_distrib]
  have hscale :
      (∑ i, t * (a.weights i * y i - a.weights i * x i)) =
        t * ((∑ i, a.weights i * y i) - (∑ i, a.weights i * x i)) := by
    simp [mul_sub, sum_sub_distrib, mul_sum]
  rw [hscale]
  ring

lemma eval_convex (a : AffineFn n) (x y : Fin n → ℝ) (t : ℝ) :
    a.eval (fun i => (1 - t) * x i + t * y i) = (1 - t) * a.eval x + t * a.eval y := by
  have h :
      (fun i => (1 - t) * x i + t * y i) = fun i => x i + t * (y i - x i) := by
    funext i
    ring
  rw [h, eval_line]
  ring

lemma eval_affineCombo (a : AffineFn n) (s t : ℝ) (x y : Fin n → ℝ) (hst : s + t = 1) :
    a.eval (s • x + t • y) = s * a.eval x + t * a.eval y := by
  have hs : s = 1 - t := by linarith
  have hpt : (s • x + t • y) = fun i => (1 - t) * x i + t * y i := by
    funext i
    change s * x i + t * y i = (1 - t) * x i + t * y i
    rw [hs]
  rw [hpt, eval_convex, hs]

lemma continuous (a : AffineFn n) : Continuous a.eval := by
  have hsum : Continuous fun x : Fin n → ℝ => ∑ i, a.weights i * x i :=
    continuous_finsetSum Finset.univ fun i _ =>
      continuous_const.mul (continuous_apply i)
  exact continuous_const.add hsum

end AffineFn

end ContinuousFOL
