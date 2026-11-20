/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: algebraic background for Fact 4.1 (Chang 1959). Identities in
MV-chains needed to build the ordered group of a chain: cancellation
(Mundici, *Introducing MV-algebras*, Lemma 1.28) and the symmetry of
`F(x, y, z) = (x ⊙ y) ⊕ ((x ⊕ y) ⊙ z)` in `y, z` (equation (11) of Prop. 1.30),
which is the second digit of the sum `x + y + z`.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.MVBasic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace MVAlgebra

/-- A nontrivial MV-algebra whose natural order is total. -/
class MVChain (A : Type*) [MVAlgebra A] : Prop where
  total : ∀ x y : A, le x y ∨ le y x
  zero_ne_one : (0 : A) ≠ 1

variable {A : Type*} [MVAlgebra A]

/-! ### Identities valid in every MV-algebra -/

/-- If `x ⊙ y = 0` then `(x ⊕ y) ⊙ ¬y = x`. -/
lemma add_mul_neg_cancel {x y : A} (h : x ⊙ y = 0) : (x ⨁ y) ⊙ ∼y = x := by
  have hM := mul_neg_add_comm (∼y) x
  rw [neg_neg_eq, ← neg_mul, h, neg_zero, mul_one] at hM
  rw [mul_comm, add_comm]
  exact hM

/-- If `x ⊕ y = 1` then `(x ⊙ y) ⊕ ¬y = x`. -/
lemma mul_add_neg_cancel {x y : A} (h : x ⨁ y = 1) : (x ⊙ y) ⨁ ∼y = x := by
  have h0 : ∼x ⊙ ∼y = 0 := by rw [← neg_add, h, neg_one]
  have h1 := congrArg (fun t => ∼t) (add_mul_neg_cancel h0)
  simp only [neg_mul, neg_neg_eq] at h1
  rw [mul_def]
  exact h1

/-- `¬y` is the unique solution of `x ⊕ y = 1`, `x ⊙ y = 0` (Lemma 1.3). -/
lemma eq_neg_of_add_mul {x y : A} (h₁ : x ⨁ y = 1) (h₂ : x ⊙ y = 0) : x = ∼y :=
  le_antisymm (le_neg_iff.mpr h₂) (neg_le_iff.mpr (by rw [add_comm]; exact h₁))

lemma add_eq_one_of_le {x y z : A} (h : x ⨁ z = 1) (hxy : le x y) : y ⨁ z = 1 :=
  one_le_iff.mp (h ▸ add_le_add_right' hxy z)

lemma mul_eq_zero_of_le {x y z : A} (h : y ⊙ z = 0) (hxy : le x y) : x ⊙ z = 0 :=
  le_zero_iff.mp (h ▸ mul_le_mul_right' hxy z)

/-! ### MV-chains -/

variable [MVChain A]

lemma add_eq_one_or_mul_eq_zero (x y : A) : x ⨁ y = 1 ∨ x ⊙ y = 0 := by
  rcases MVChain.total (∼y) x with h | h
  · left
    rw [add_comm]
    exact neg_le_iff.mp h
  · right
    exact le_neg_iff.mp h

lemma mul_eq_zero_of_add_ne_one {x y : A} (h : x ⨁ y ≠ 1) : x ⊙ y = 0 :=
  (add_eq_one_or_mul_eq_zero x y).resolve_left h

lemma zero_ne_one' : (0 : A) ≠ 1 := MVChain.zero_ne_one

/-- Lemma 1.28(iii): if `x ⊕ y = x ⊕ z < 1` then `y = z`. -/
lemma add_left_cancel' {x y z : A} (h : x ⨁ y = x ⨁ z) (h1 : x ⨁ y ≠ 1) : y = z := by
  have hy : y ⊙ x = 0 := mul_eq_zero_of_add_ne_one (by rw [add_comm]; exact h1)
  have hz : z ⊙ x = 0 := mul_eq_zero_of_add_ne_one (by rw [add_comm, ← h]; exact h1)
  rw [← add_mul_neg_cancel hy, ← add_mul_neg_cancel hz, add_comm y, add_comm z, h]

/-- Lemma 1.28(iv): if `x ⊙ y = x ⊙ z > 0` then `y = z`. -/
lemma mul_left_cancel' {x y z : A} (h : x ⊙ y = x ⊙ z) (h0 : x ⊙ y ≠ 0) : y = z := by
  apply neg_inj
  apply add_left_cancel' (x := ∼x)
  · rw [← neg_mul, ← neg_mul, h]
  · rw [← neg_mul]
    intro h'
    exact h0 (by rw [← neg_neg_eq (x ⊙ y), h', neg_one])

/-- Lemma 1.28(vii): if `x ⊕ y = 1` and `x ⊕ z < 1` then
    `(x ⊙ y) ⊕ z = (x ⊕ z) ⊙ y`. -/
lemma mul_add_eq_add_mul {x y z : A} (h₁ : x ⨁ y = 1) (h₂ : x ⨁ z ≠ 1) :
    (x ⊙ y) ⨁ z = (x ⨁ z) ⊙ y := by
  have hL : ∼y ⨁ ((x ⊙ y) ⨁ z) = x ⨁ z := by
    rw [MVAlgebra.add_assoc, add_comm (∼y), mul_add_neg_cancel h₁]
  have hxzy : (x ⨁ z) ⨁ y = 1 := by
    rw [← MVAlgebra.add_assoc, add_comm z, MVAlgebra.add_assoc, h₁, one_add]
  have hR : ∼y ⨁ ((x ⨁ z) ⊙ y) = x ⨁ z := by
    rw [add_comm, mul_add_neg_cancel hxzy]
  exact add_left_cancel' (hL.trans hR.symm) (by rw [hL]; exact h₂)

lemma meet_eq_or (x y : A) : meet x y = x ∨ meet x y = y := by
  rcases MVChain.total x y with h | h
  · exact Or.inl (meet_eq_left h)
  · exact Or.inr (meet_eq_right h)

/-! ### The second digit `F(x, y, z)` -/

/-- `F(x, y, z) = (x ⊙ y) ⊕ ((x ⊕ y) ⊙ z)`: the second digit of `x + y + z`. -/
def digit2 (x y z : A) : A :=
  (x ⊙ y) ⨁ ((x ⨁ y) ⊙ z)

/-- Equation (12). -/
lemma digit2_eq (x y z : A) : digit2 x y z = (x ⨁ y) ⊙ ((x ⊙ y) ⨁ z) := by
  unfold digit2
  rcases add_eq_one_or_mul_eq_zero x y with h | h
  · rw [h, one_mul, one_mul]
  · rw [h, add_left_zero, add_left_zero]

/-- Equation (13): `¬F(x, y, z) = F(¬x, ¬y, ¬z)`. -/
lemma neg_digit2 (x y z : A) : ∼(digit2 x y z) = digit2 (∼x) (∼y) (∼z) := by
  rw [digit2_eq, neg_mul, neg_add, neg_add, neg_mul, digit2]

lemma key_digit (x y z : A) (hxy : x ⨁ y = 1) (hxz : x ⨁ z = 1)
    (hxyz : x ⊙ y ⊙ z = 0) : (x ⊙ y) ⨁ z = (x ⊙ z) ⨁ y := by
  -- Case `x ⊙ y = 0` (and symmetrically `x ⊙ z = 0`).
  have caseA : ∀ y z : A, x ⨁ y = 1 → x ⨁ z = 1 → x ⊙ y = 0 →
      (x ⊙ y) ⨁ z = (x ⊙ z) ⨁ y := by
    intro y z hxy hxz h0
    have hx : x = ∼y := eq_neg_of_add_mul hxy h0
    have hz : z ⨁ ∼y = 1 := by rw [add_comm, ← hx]; exact hxz
    have := mul_add_neg_cancel hz
    rw [neg_neg_eq] at this
    rw [h0, add_left_zero, hx, mul_comm, this]
  -- Case `(x ⊙ y) ⊕ z = 1` (and symmetrically).
  have caseC : ∀ y z : A, x ⨁ y = 1 → x ⊙ y ⊙ z = 0 → (x ⊙ y) ⨁ z = 1 →
      (x ⊙ y) ⨁ z = (x ⊙ z) ⨁ y := by
    intro y z hxy h0 h1
    have hz : z = ∼(x ⊙ y) :=
      eq_neg_of_add_mul (by rw [add_comm]; exact h1) (by rw [mul_comm]; exact h0)
    rw [h1, hz, neg_mul]
    change 1 = meet x (∼y) ⨁ y
    rcases MVChain.total x (∼y) with hle | hle
    · rw [meet_eq_left hle, hxy]
    · rw [meet_eq_right hle, neg_add_self]
  by_cases h1 : x ⊙ y = 0
  · exact caseA y z hxy hxz h1
  by_cases h2 : x ⊙ z = 0
  · exact (caseA z y hxz hxy h2).symm
  by_cases h3 : (x ⊙ y) ⨁ z = 1
  · exact caseC y z hxy hxyz h3
  have hxzy : x ⊙ z ⊙ y = 0 := by
    rw [← mul_assoc, mul_comm z, mul_assoc]; exact hxyz
  by_cases h4 : (x ⊙ z) ⨁ y = 1
  · exact (caseC z y hxz hxzy h4).symm
  -- Generic case: cancel `x ⊙ _` using Lemma 1.28(vii) twice.
  have hzx : z ⨁ x = 1 := by rw [add_comm]; exact hxz
  have hyx : y ⨁ x = 1 := by rw [add_comm]; exact hxy
  have e1 := mul_add_eq_add_mul hzx (z := x ⊙ y) (by rw [add_comm]; exact h3)
  have e2 := mul_add_eq_add_mul hyx (z := x ⊙ z) (by rw [add_comm]; exact h4)
  have hL : x ⊙ ((x ⊙ y) ⨁ z) = (x ⊙ z) ⨁ (x ⊙ y) := by
    rw [mul_comm, add_comm (x ⊙ y), ← e1, mul_comm z]
  have hR : x ⊙ ((x ⊙ z) ⨁ y) = (x ⊙ z) ⨁ (x ⊙ y) := by
    rw [mul_comm, add_comm (x ⊙ z), ← e2, mul_comm y, add_comm]
  apply mul_left_cancel' (hL.trans hR.symm)
  rw [hL]
  intro h0
  exact h2 (le_zero_iff.mp (h0 ▸ le_add_right (x ⊙ z) (x ⊙ y)))

lemma digit2_symm_of_ne (x y z : A) (h : x ⨁ y ⨁ z ≠ 1) :
    digit2 x y z = digit2 x z y := by
  have hxy : x ⨁ y ≠ 1 := fun e => h (by rw [e, one_add])
  have hxz : x ⨁ z ≠ 1 := fun e => h (by
    rw [← MVAlgebra.add_assoc, add_comm y, MVAlgebra.add_assoc, e, one_add])
  have hxyz : x ⨁ z ⨁ y ≠ 1 := by
    rwa [← MVAlgebra.add_assoc, add_comm z, MVAlgebra.add_assoc]
  unfold digit2
  rw [mul_eq_zero_of_add_ne_one hxy, mul_eq_zero_of_add_ne_one hxz,
    mul_eq_zero_of_add_ne_one h, mul_eq_zero_of_add_ne_one hxyz]

/-- Equation (11): `F(x, y, z) = F(x, z, y)` in every MV-chain. -/
theorem digit2_symm (x y z : A) : digit2 x y z = digit2 x z y := by
  by_cases hA : x ⨁ y ⨁ z = 1
  swap
  · exact digit2_symm_of_ne x y z hA
  by_cases hB : ∼x ⨁ ∼y ⨁ ∼z = 1
  swap
  · apply neg_inj
    rw [neg_digit2, neg_digit2]
    exact digit2_symm_of_ne _ _ _ hB
  have hxyz : x ⊙ y ⊙ z = 0 := by
    rw [← neg_neg_eq (x ⊙ y ⊙ z), neg_mul, neg_mul, hB, neg_one]
  have hxzy : x ⊙ z ⊙ y = 0 := by
    rw [← mul_assoc, mul_comm z, mul_assoc]; exact hxyz
  -- Subcase analysis on `x ⊕ y` and `x ⊕ z`.
  have sub31 : ∀ y z : A, x ⨁ y = 1 → x ⨁ z ≠ 1 → digit2 x y z = digit2 x z y := by
    intro y z h1 h2
    unfold digit2
    rw [h1, one_mul, mul_eq_zero_of_add_ne_one h2, add_left_zero]
    exact mul_add_eq_add_mul h1 h2
  by_cases h1 : x ⨁ y = 1 <;> by_cases h2 : x ⨁ z = 1
  · unfold digit2
    rw [h1, h2, one_mul, one_mul]
    exact key_digit x y z h1 h2 hxyz
  · exact sub31 y z h1 h2
  · exact (sub31 z y h2 h1).symm
  · -- Both sums are below `1`: dualize.
    have n1 : ∼x ⨁ ∼y = 1 := by
      rw [← neg_mul, mul_eq_zero_of_add_ne_one h1, neg_zero]
    have n2 : ∼x ⨁ ∼z = 1 := by
      rw [← neg_mul, mul_eq_zero_of_add_ne_one h2, neg_zero]
    have n3 : ∼x ⊙ ∼y ⊙ ∼z = 0 := by
      rw [← neg_add, ← neg_add, hA, neg_one]
    apply neg_inj
    rw [neg_digit2, neg_digit2]
    unfold digit2
    rw [n1, n2, one_mul, one_mul]
    exact key_digit _ _ _ n1 n2 n3

end MVAlgebra

end ContinuousFOL
