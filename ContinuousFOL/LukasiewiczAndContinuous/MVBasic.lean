/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: algebraic background for Fact 4.1 (Chang 1958/1959). Basic theory of
MV-algebras from Chang's axioms: the natural order, the lattice operations,
distributivity of `⊕` over `∧`, prelinearity `(x ⊖ y) ∧ (y ⊖ x) = 0`, and
`x ∧ y = 0 → nx ∧ my = 0`. Proofs follow D. Mundici, *Introducing MV-algebras*,
Lemmas 1.2–1.4, Propositions 1.5–1.7 and Lemma 1.8.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.MVAlgebra

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace MVAlgebra

variable {A : Type*} [MVAlgebra A]

instance addAssoc : Std.Associative (MVAlgebra.add : A → A → A) :=
  ⟨fun x y z => (MVAlgebra.add_assoc x y z).symm⟩

instance addComm : Std.Commutative (MVAlgebra.add : A → A → A) :=
  ⟨MVAlgebra.add_comm⟩

lemma neg_inj {x y : A} (h : ∼x = ∼y) : x = y := by
  rw [← neg_neg_eq x, h, neg_neg_eq]

lemma neg_inj_iff {x y : A} : ∼x = ∼y ↔ x = y :=
  ⟨neg_inj, fun h => h ▸ rfl⟩

lemma one_eq_neg_zero : (1 : A) = ∼(0 : A) := rfl

/-- (MV9) `x ⊕ ¬x = 1`. -/
lemma add_neg_self (x : A) : x ⨁ ∼x = 1 := by
  have h := MVAlgebra.add_absorp x (1 : A)
  have e1 : (∼x ⨁ 1 : A) = 1 := add_one _
  have e2 : (∼(1 : A)) = 0 := neg_one
  rw [e1, e2, add_left_zero, add_left_zero] at h
  rw [add_comm]
  exact h.symm

lemma neg_add_self (x : A) : ∼x ⨁ x = 1 := by
  rw [add_comm, add_neg_self]

lemma msub_eq_mul (x y : A) : x ⊖ y = x ⊙ ∼y := by
  rw [msub_def, mul_def, neg_neg_eq]

lemma neg_add (x y : A) : ∼(x ⨁ y) = ∼x ⊙ ∼y := by
  rw [mul_def, neg_neg_eq, neg_neg_eq]

lemma neg_mul (x y : A) : ∼(x ⊙ y) = ∼x ⨁ ∼y := by
  rw [mul_def, neg_neg_eq]

lemma mul_assoc (x y z : A) : x ⊙ (y ⊙ z) = (x ⊙ y) ⊙ z := by
  simp only [mul_def, neg_neg_eq, MVAlgebra.add_assoc]

instance mulAssoc : Std.Associative (mul : A → A → A) :=
  ⟨fun x y z => (mul_assoc x y z).symm⟩

instance mulComm : Std.Commutative (mul : A → A → A) :=
  ⟨mul_comm⟩

lemma mul_one (x : A) : x ⊙ 1 = x := by
  rw [mul_def, neg_one, add_right_zero, neg_neg_eq]

lemma one_mul (x : A) : 1 ⊙ x = x := by
  rw [mul_comm, mul_one]

lemma mul_zero (x : A) : x ⊙ 0 = 0 := by
  rw [mul_def, neg_zero, add_one, neg_one]

lemma zero_mul (x : A) : 0 ⊙ x = 0 := by
  rw [mul_comm, mul_zero]

lemma mul_neg_self (x : A) : x ⊙ ∼x = 0 := by
  rw [mul_def, neg_neg_eq, neg_add_self, neg_one]

lemma neg_mul_self (x : A) : ∼x ⊙ x = 0 := by
  rw [mul_comm, mul_neg_self]

/-- The dual form of (MV6): `x ⊙ (¬x ⊕ y) = y ⊙ (¬y ⊕ x)`. -/
lemma mul_neg_add_comm (x y : A) : x ⊙ (∼x ⨁ y) = y ⊙ (∼y ⨁ x) := by
  have h := congrArg (fun t => ∼t) (MVAlgebra.add_absorp (∼x) (∼y))
  simp only [neg_neg_eq] at h
  have h1 : ∼(∼(x ⨁ ∼y) ⨁ ∼y) = (x ⨁ ∼y) ⊙ y := by rw [mul_def]
  have h2 : ∼(∼(y ⨁ ∼x) ⨁ ∼x) = (y ⨁ ∼x) ⊙ x := by rw [mul_def]
  change ∼(∼(x ⨁ ∼y) ⨁ ∼y) = ∼(∼(y ⨁ ∼x) ⨁ ∼x) at h
  rw [h1, h2] at h
  rw [mul_comm x, mul_comm y, add_comm (∼x), add_comm (∼y)]
  exact h.symm

/-! ### The natural order -/

lemma le_iff_add_eq_one {x y : A} : le x y ↔ ∼x ⨁ y = 1 := by
  rw [le_iff_msub_eq_zero, msub_def]
  constructor
  · intro h
    apply neg_inj
    rw [h, neg_one]
  · intro h
    rw [h, neg_one]

lemma le_iff_mul_eq_zero {x y : A} : le x y ↔ x ⊙ ∼y = 0 := by
  rw [le_iff_msub_eq_zero, msub_eq_mul]

lemma le_neg_iff {x y : A} : le x (∼y) ↔ x ⊙ y = 0 := by
  rw [le_iff_mul_eq_zero, neg_neg_eq]

lemma neg_le_iff {x y : A} : le (∼y) x ↔ y ⨁ x = 1 := by
  rw [le_iff_add_eq_one, neg_neg_eq]

lemma le_of_eq_add {x y z : A} (h : y = x ⨁ z) : le x y := by
  rw [le_iff_add_eq_one, h, MVAlgebra.add_assoc, neg_add_self, one_add]

lemma le_add_right (x z : A) : le x (x ⨁ z) :=
  le_of_eq_add rfl

lemma le_add_left (x z : A) : le x (z ⨁ x) := by
  rw [add_comm]
  exact le_add_right x z

lemma eq_add_msub {x y : A} (h : le x y) : y = x ⨁ (y ⊖ x) := by
  have hj := join_comm x y
  rw [(le_iff_msub_eq_zero x y).mp h, add_left_zero] at hj
  exact hj.trans (add_comm _ _)

lemma le_iff_exists {x y : A} : le x y ↔ ∃ z, y = x ⨁ z :=
  ⟨fun h => ⟨_, eq_add_msub h⟩, fun ⟨_, h⟩ => le_of_eq_add h⟩

lemma le_refl (x : A) : le x x := by
  rw [le_iff_add_eq_one, neg_add_self]

lemma le_trans {x y z : A} (h₁ : le x y) (h₂ : le y z) : le x z := by
  obtain ⟨a, ha⟩ := le_iff_exists.mp h₁
  obtain ⟨b, hb⟩ := le_iff_exists.mp h₂
  exact le_of_eq_add (z := a ⨁ b) (by rw [hb, ha, MVAlgebra.add_assoc])

lemma le_antisymm {x y : A} (h₁ : le x y) (h₂ : le y x) : x = y := by
  have hj := join_comm x y
  rw [(le_iff_msub_eq_zero x y).mp h₁, (le_iff_msub_eq_zero y x).mp h₂,
    add_left_zero, add_left_zero] at hj
  exact hj.symm

lemma zero_le (x : A) : le 0 x := le_of_eq_add (add_left_zero x).symm

lemma le_one (x : A) : le x 1 := by
  rw [le_iff_add_eq_one, add_one]

lemma le_zero_iff {x : A} : le x 0 ↔ x = 0 :=
  ⟨fun h => le_antisymm h (zero_le x), fun h => h ▸ le_refl _⟩

lemma one_le_iff {x : A} : le 1 x ↔ x = 1 :=
  ⟨fun h => le_antisymm (le_one x) h, fun h => h ▸ le_refl _⟩

lemma add_le_add_right' {x y : A} (h : le x y) (z : A) : le (x ⨁ z) (y ⨁ z) := by
  obtain ⟨a, ha⟩ := le_iff_exists.mp h
  exact le_of_eq_add (z := a) (by rw [ha]; ac_rfl)

lemma add_le_add_left' {x y : A} (h : le x y) (z : A) : le (z ⨁ x) (z ⨁ y) := by
  rw [add_comm z, add_comm z]
  exact add_le_add_right' h z

lemma add_le_add' {x y z w : A} (h₁ : le x y) (h₂ : le z w) : le (x ⨁ z) (y ⨁ w) :=
  le_trans (add_le_add_right' h₁ z) (add_le_add_left' h₂ y)

lemma neg_le_neg {x y : A} (h : le x y) : le (∼y) (∼x) := by
  rw [le_iff_add_eq_one] at h ⊢
  rw [neg_neg_eq, add_comm]
  exact h

lemma neg_le_neg_iff {x y : A} : le (∼y) (∼x) ↔ le x y :=
  ⟨fun h => by simpa [neg_neg_eq] using neg_le_neg h, neg_le_neg⟩

lemma mul_le_mul_right' {x y : A} (h : le x y) (z : A) : le (x ⊙ z) (y ⊙ z) := by
  rw [mul_def, mul_def]
  exact neg_le_neg (add_le_add_right' (neg_le_neg h) _)

lemma mul_le_mul_left' {x y : A} (h : le x y) (z : A) : le (z ⊙ x) (z ⊙ y) := by
  rw [mul_comm z, mul_comm z]
  exact mul_le_mul_right' h z

lemma mul_le_left (x y : A) : le (x ⊙ y) x := by
  have := mul_le_mul_left' (le_one y) x
  rwa [mul_one] at this

lemma mul_le_right (x y : A) : le (x ⊙ y) y := by
  rw [mul_comm]
  exact mul_le_left y x

lemma msub_le (x y : A) : le (x ⊖ y) x := by
  rw [msub_eq_mul]
  exact mul_le_left x _

/-- Residuation: `x ⊙ y ≤ z ↔ x ≤ ¬y ⊕ z`. -/
lemma mul_le_iff {x y z : A} : le (x ⊙ y) z ↔ le x (∼y ⨁ z) := by
  rw [le_iff_add_eq_one, le_iff_add_eq_one, neg_mul, MVAlgebra.add_assoc]

lemma le_add_iff {w x v : A} : le w (x ⨁ v) ↔ le (w ⊙ ∼x) v := by
  rw [mul_le_iff, neg_neg_eq]

lemma msub_le_msub_right {x z : A} (h : le x z) (y : A) : le (x ⊖ y) (z ⊖ y) := by
  rw [msub_def, msub_def]
  exact neg_le_neg (add_le_add_right' (neg_le_neg h) y)

lemma msub_msub (x a b : A) : (x ⊖ a) ⊖ b = x ⊖ (a ⨁ b) := by
  rw [msub_def, msub_def, msub_def, neg_neg_eq, MVAlgebra.add_assoc]

lemma msub_zero (x : A) : x ⊖ 0 = x := by
  rw [msub_def, add_right_zero, neg_neg_eq]

lemma zero_msub (x : A) : 0 ⊖ x = 0 := by
  rw [msub_def, neg_zero, one_add, neg_one]

lemma one_msub (x : A) : 1 ⊖ x = ∼x := by
  rw [msub_def, neg_one, add_left_zero]

/-! ### Lattice operations -/

lemma le_join_right (x y : A) : le y (join x y) :=
  le_add_left y _

lemma le_join_left (x y : A) : le x (join x y) := by
  rw [join_comm']
  exact le_join_right y x

lemma join_le {x y z : A} (hx : le x z) (hy : le y z) : le (join x y) z := by
  have hz : z = (z ⊖ y) ⨁ y := (eq_add_msub hy).trans (add_comm _ _)
  have h := add_le_add_right' (msub_le_msub_right hx y) y
  rw [← hz] at h
  exact h

/-- The lattice meet `x ∧ y := x ⊙ (¬x ⊕ y)`. -/
def meet (x y : A) : A :=
  x ⊙ (∼x ⨁ y)

lemma meet_comm (x y : A) : meet x y = meet y x :=
  mul_neg_add_comm x y

lemma meet_le_left (x y : A) : le (meet x y) x :=
  mul_le_left _ _

lemma meet_le_right (x y : A) : le (meet x y) y := by
  rw [meet_comm]
  exact meet_le_left y x

lemma meet_eq_neg_join (x y : A) : meet x y = ∼(join (∼x) (∼y)) := by
  rw [join, msub_def, neg_neg_eq, ← mul_def, meet_comm, meet, mul_comm, add_comm]

lemma le_meet {x y z : A} (hx : le z x) (hy : le z y) : le z (meet x y) := by
  rw [meet_eq_neg_join, ← neg_le_neg_iff, neg_neg_eq]
  exact join_le (neg_le_neg hx) (neg_le_neg hy)

lemma meet_eq_left {x y : A} (h : le x y) : meet x y = x := by
  rw [meet, le_iff_add_eq_one.mp h, mul_one]

lemma meet_eq_right {x y : A} (h : le y x) : meet x y = y := by
  rw [meet_comm, meet_eq_left h]

lemma meet_zero (x : A) : meet x 0 = 0 :=
  meet_eq_right (zero_le x)

lemma zero_meet (x : A) : meet 0 x = 0 :=
  meet_eq_left (zero_le x)

/-- Distributivity: `x ⊕ (y ∧ z) = (x ⊕ y) ∧ (x ⊕ z)` (Mundici, Prop. 1.6). -/
lemma add_meet (x y z : A) : x ⨁ meet y z = meet (x ⨁ y) (x ⨁ z) := by
  apply le_antisymm
  · exact le_meet (add_le_add_left' (meet_le_left y z) x)
      (add_le_add_left' (meet_le_right y z) x)
  · rw [le_add_iff]
    exact le_meet (le_add_iff.mp (meet_le_left _ _)) (le_add_iff.mp (meet_le_right _ _))

/-- Prelinearity (Mundici, Prop. 1.7): `(x ⊖ y) ∧ (y ⊖ x) = 0`. -/
theorem meet_msub_msub (x y : A) : meet (x ⊖ y) (y ⊖ x) = 0 := by
  rw [msub_eq_mul, msub_eq_mul]
  set b := y ⊙ ∼x with hb
  set w := ∼x ⨁ b with hw
  have hna : ∼(x ⊙ ∼y) = ∼x ⨁ y := by rw [neg_mul, neg_neg_eq]
  have hM1 : ∼y ⊙ (y ⨁ w) = w ⊙ (∼w ⨁ ∼y) := by
    have := mul_neg_add_comm (∼y) w
    rwa [neg_neg_eq] at this
  have hM2 : x ⊙ w = b ⊙ (∼b ⨁ x) := mul_neg_add_comm x b
  have hM3 : y ⊙ (∼y ⨁ ∼w) = ∼w ⊙ (∼∼w ⨁ y) := mul_neg_add_comm y (∼w)
  have hnw : ∼w = x ⊙ ∼b := by rw [hw, neg_add, neg_neg_eq]
  calc meet (x ⊙ ∼y) b
      = x ⊙ (∼y ⊙ (y ⨁ w)) := by
        rw [meet, hna, hw]
        rw [mul_assoc]
        congr 1
        ac_rfl
    _ = (x ⊙ w) ⊙ (∼w ⨁ ∼y) := by rw [hM1]; ac_rfl
    _ = ∼x ⊙ (∼b ⨁ x) ⊙ (y ⊙ (∼y ⨁ ∼w)) := by
        rw [hM2, hb]
        ac_rfl
    _ = ∼x ⊙ (∼b ⨁ x) ⊙ (∼w ⊙ (∼∼w ⨁ y)) := by rw [hM3]
    _ = (∼x ⊙ x) ⊙ ((∼b ⨁ x) ⊙ ∼b ⊙ (∼∼w ⨁ y)) := by
        rw [hnw]
        ac_rfl
    _ = 0 := by rw [neg_mul_self, zero_mul]

/-! ### Multiples -/

/-- `nsm n x = x ⊕ ⋯ ⊕ x` (`n` times). -/
def nsm : ℕ → A → A
  | 0, _ => 0
  | n + 1, x => nsm n x ⨁ x

lemma nsm_mono (x : A) {n m : ℕ} (h : n ≤ m) : le (nsm n x) (nsm m x) := by
  induction h with
  | refl => exact le_refl _
  | step _ ih => exact le_trans ih (le_add_right _ _)

lemma meet_add_eq_zero {a b y : A} (ha : meet a y = 0) (hb : meet b y = 0) :
    meet (a ⨁ b) y = 0 := by
  have h1 : le (meet (a ⨁ b) y) (meet (a ⨁ b) (a ⨁ y)) :=
    le_meet (meet_le_left _ _) (le_trans (meet_le_right _ _) (le_add_left y a))
  rw [← add_meet, hb, add_right_zero] at h1
  have h2 : le (meet (a ⨁ b) y) (meet a y) := le_meet h1 (meet_le_right _ _)
  rw [ha] at h2
  exact le_zero_iff.mp h2

lemma meet_nsm_left {x y : A} (h : meet x y = 0) (n : ℕ) : meet (nsm n x) y = 0 := by
  induction n with
  | zero => exact zero_meet y
  | succ n ih => exact meet_add_eq_zero ih h

/-- Mundici, Lemma 1.8: if `x ∧ y = 0` then `nx ∧ my = 0`. -/
lemma meet_nsm_nsm {x y : A} (h : meet x y = 0) (n m : ℕ) :
    meet (nsm n x) (nsm m y) = 0 := by
  have h1 := meet_nsm_left h n
  rw [meet_comm] at h1 ⊢
  exact meet_nsm_left h1 m

end MVAlgebra

end ContinuousFOL
