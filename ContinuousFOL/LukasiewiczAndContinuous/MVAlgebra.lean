/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: algebraic background for Fact 4.1 (Chang 1958; Rose–Rosser 1958).
An MV-algebra is a structure ⟨A, ⊕, ¬, 0⟩ satisfying Chang's axioms (MV1)–(MV6).
-/
module

public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- An MV-algebra in Chang's signature `⟨A, ⊕, ¬, 0⟩`.
    Axioms (MV1)–(MV6) follow Chang, *Algebraic analysis of many-valued logics*,
    Trans. Amer. Math. Soc. 88 (1958). -/
class MVAlgebra (A : Type*) where
  add : A → A → A
  neg : A → A
  zero : A
  add_assoc : ∀ x y z, add x (add y z) = add (add x y) z
  add_comm : ∀ x y, add x y = add y x
  add_zero : ∀ x, add x zero = x
  neg_neg : ∀ x, neg (neg x) = x
  /-- (MV5) `x ⊕ ¬0 = ¬0`. -/
  add_neg_zero : ∀ x, add x (neg zero) = neg zero
  /-- (MV6) `¬(¬x ⊕ y) ⊕ y = ¬(¬y ⊕ x) ⊕ x`. -/
  add_absorp : ∀ x y,
    add (neg (add (neg x) y)) y = add (neg (add (neg y) x)) x

namespace MVAlgebra

variable {A : Type*} [MVAlgebra A]

infixl:65 " ⨁ " => MVAlgebra.add
prefix:75 "∼" => MVAlgebra.neg

instance : Zero A :=
  ⟨MVAlgebra.zero⟩

@[simp] lemma zero_def : (0 : A) = MVAlgebra.zero := rfl

@[simp] lemma add_right_zero (x : A) : x ⨁ 0 = x :=
  MVAlgebra.add_zero x

lemma add_left_zero (x : A) : (0 : A) ⨁ x = x := by
  rw [add_comm, add_right_zero]

/-- The top element `1 := ¬0`. -/
instance : One A :=
  ⟨∼(0 : A)⟩

@[simp] lemma one_def : (1 : A) = ∼(0 : A) := rfl

@[simp] lemma neg_zero : ∼(0 : A) = 1 := rfl

@[simp] lemma neg_one : ∼(1 : A) = 0 := by
  simp [neg_neg]

/-- (MV5) in the form `x ⊕ 1 = 1`. -/
@[simp] lemma add_one (x : A) : x ⨁ 1 = 1 :=
  MVAlgebra.add_neg_zero x

lemma one_add (x : A) : (1 : A) ⨁ x = 1 := by
  rw [add_comm, add_one]

@[simp] lemma neg_neg_eq (x : A) : ∼∼x = x :=
  MVAlgebra.neg_neg x

/-- Truncated subtraction `x ⊖ y := ¬(¬x ⊕ y)`. On `[0,1]` this is `max(x - y, 0)`. -/
def msub (x y : A) : A :=
  ∼(∼x ⨁ y)

infixl:65 " ⊖ " => msub

lemma msub_def (x y : A) : x ⊖ y = ∼(∼x ⨁ y) := rfl

/-- MV-conjunction `x ⊙ y := ¬(¬x ⊕ ¬y)`. -/
def mul (x y : A) : A :=
  ∼(∼x ⨁ ∼y)

infixl:70 " ⊙ " => mul

lemma mul_def (x y : A) : x ⊙ y = ∼(∼x ⨁ ∼y) := rfl

lemma mul_comm (x y : A) : x ⊙ y = y ⊙ x := by
  simp [mul_def, add_comm]

/-- Chang's axiom in truncated-subtraction form: `(x ⊖ y) ⊕ y = (y ⊖ x) ⊕ x`. -/
lemma join_comm (x y : A) : (x ⊖ y) ⨁ y = (y ⊖ x) ⨁ x :=
  MVAlgebra.add_absorp x y

/-- The lattice join, `x ⊔ y := (x ⊖ y) ⊕ y`. Chang's axiom says this is commutative. -/
def join (x y : A) : A :=
  (x ⊖ y) ⨁ y

lemma join_comm' (x y : A) : join x y = join y x :=
  join_comm x y

/-- The natural order: `x ≤ y` iff `x ⊖ y = 0`. -/
def le (x y : A) : Prop :=
  x ⊖ y = 0

lemma le_iff_msub_eq_zero (x y : A) : le x y ↔ x ⊖ y = 0 :=
  Iff.rfl

end MVAlgebra

end ContinuousFOL
