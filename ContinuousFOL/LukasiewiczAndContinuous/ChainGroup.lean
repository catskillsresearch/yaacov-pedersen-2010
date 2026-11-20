/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: algebraic background for Fact 4.1 (Chang 1959). The ordered abelian
group of an MV-chain `A`. Its elements are pairs `(n, a)` with `n : ℤ` and
`a ∈ A`, `a ≠ 1`, standing for "`n + a`". Addition carries when `a ⊕ b = 1`. The
order is lexicographic. `A` embeds in the interval `[0, u]`, `u = (1, 0)`, so that
`⊖` and `¬` go to `max (x - y) 0` and `u - x`. Consequence: a formula with a non-zero
value in an MV-chain has a non-zero value under some `[0, 1]`-assignment.
Associativity follows from the digit description of `a + b + c` and the symmetry of
the second digit (`MVAlgebra.digit2_symm`).
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.MVChain
public import ContinuousFOL.LukasiewiczAndContinuous.GroupEval
public import ContinuousFOL.LukasiewiczAndContinuous.StandardMVAlgebra

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace MVAlgebra

variable {A : Type*} [MVAlgebra A]

/-! ### Carry and fractional part of a sum -/

/-- The carry of `a + b`. -/
def carry (a b : A) : ℤ := if a ⨁ b = 1 then 1 else 0

/-- The fractional part of `a + b`. -/
def fsum (a b : A) : A := if a ⨁ b = 1 then a ⊙ b else a ⨁ b

lemma carry_of {a b : A} (h : a ⨁ b = 1) : carry a b = 1 := ite_eq_left h
lemma carry_of_not {a b : A} (h : a ⨁ b ≠ 1) : carry a b = 0 := ite_eq_right h
lemma fsum_of {a b : A} (h : a ⨁ b = 1) : fsum a b = a ⊙ b := ite_eq_left h
lemma fsum_of_not {a b : A} (h : a ⨁ b ≠ 1) : fsum a b = a ⨁ b := ite_eq_right h

lemma carry_comm (a b : A) : carry a b = carry b a := by
  unfold carry; rw [MVAlgebra.add_comm a b]

lemma fsum_comm (a b : A) : fsum a b = fsum b a := by
  unfold fsum; rw [MVAlgebra.add_comm a b, mul_comm a b]

lemma fsum_ne_one {a : A} (ha : a ≠ 1) (b : A) : fsum a b ≠ 1 := by
  by_cases h : a ⨁ b = 1
  · rw [fsum_of h]
    intro h1
    have hl := mul_le_left a b
    rw [h1] at hl
    exact ha (one_le_iff.mp hl)
  · rw [fsum_of_not h]; exact h

lemma neg_ne_one {a : A} (h : a ≠ 0) : ∼a ≠ 1 := fun h1 =>
  h (by rw [← neg_neg_eq a, h1, neg_one])

/-! ### Digits of a triple sum -/

/-- The three digits of `a + b + c`. -/
def digits (a b c : A) : A × A × A := (a ⨁ b ⨁ c, digit2 a b c, a ⊙ b ⊙ c)

/-- Integer part read off the digits. -/
def decK (t : A × A × A) : ℤ := if t.1 ≠ 1 then 0 else if t.2.1 ≠ 1 then 1 else 2

/-- Fractional part read off the digits. -/
def decR (t : A × A × A) : A := if t.1 ≠ 1 then t.1 else if t.2.1 ≠ 1 then t.2.1 else t.2.2

lemma dec_1 {a b c : A} (h : a ⨁ b ⨁ c ≠ 1) :
    decK (digits a b c) = 0 ∧ decR (digits a b c) = a ⨁ b ⨁ c :=
  ⟨ite_eq_left h, ite_eq_left h⟩

lemma dec_2 {a b c : A} (h : a ⨁ b ⨁ c = 1) (h2 : digit2 a b c ≠ 1) :
    decK (digits a b c) = 1 ∧ decR (digits a b c) = digit2 a b c := by
  have h' : ¬ (a ⨁ b ⨁ c ≠ 1) := not_not.mpr h
  exact ⟨(ite_eq_right h').trans (ite_eq_left h2), (ite_eq_right h').trans (ite_eq_left h2)⟩

lemma dec_3 {a b c : A} (h : a ⨁ b ⨁ c = 1) (h2 : digit2 a b c = 1) :
    decK (digits a b c) = 2 ∧ decR (digits a b c) = a ⊙ b ⊙ c := by
  have h' : ¬ (a ⨁ b ⨁ c ≠ 1) := not_not.mpr h
  have h2' : ¬ (digit2 a b c ≠ 1) := not_not.mpr h2
  exact ⟨(ite_eq_right h').trans (ite_eq_right h2'), (ite_eq_right h').trans (ite_eq_right h2')⟩

variable [MVChain A]

/-- Adding `a`, `b`, `c` from the left with carries gives the digits. -/
lemma fold_eq (a b c : A) :
    carry a b + carry (fsum a b) c = decK (digits a b c) ∧
      fsum (fsum a b) c = decR (digits a b c) := by
  by_cases hab : a ⨁ b = 1
  · have hd1 : a ⨁ b ⨁ c = 1 := by rw [hab, one_add]
    have hd2 : digit2 a b c = (a ⊙ b) ⨁ c := by rw [digit2, hab, one_mul]
    rw [carry_of hab, fsum_of hab]
    by_cases hc : (a ⊙ b) ⨁ c = 1
    · obtain ⟨k, r⟩ := dec_3 hd1 (hd2.trans hc)
      rw [carry_of hc, fsum_of hc, k, r]
      norm_num
    · obtain ⟨k, r⟩ := dec_2 hd1 (hd2 ▸ hc)
      rw [carry_of_not hc, fsum_of_not hc, k, r, hd2]
      norm_num
  · have h0 : a ⊙ b = 0 := mul_eq_zero_of_add_ne_one hab
    have hd2 : digit2 a b c = (a ⨁ b) ⊙ c := by rw [digit2, h0, add_left_zero]
    rw [carry_of_not hab, fsum_of_not hab]
    by_cases hc : a ⨁ b ⨁ c = 1
    · have hne : digit2 a b c ≠ 1 := by
        rw [hd2]
        intro h1
        have hl := mul_le_left (a ⨁ b) c
        rw [h1] at hl
        exact hab (one_le_iff.mp hl)
      obtain ⟨k, r⟩ := dec_2 hc hne
      rw [carry_of hc, fsum_of hc, k, r, hd2]
      norm_num
    · obtain ⟨k, r⟩ := dec_1 hc
      rw [carry_of_not hc, fsum_of_not hc, k, r]
      norm_num

omit [MVChain A] in
lemma digits_swap12 (a b c : A) : digits a b c = digits b a c := by
  have h2 : digit2 a b c = digit2 b a c := by
    unfold digit2; rw [mul_comm a b, MVAlgebra.add_comm a b]
  simp only [digits, Prod.mk.injEq]
  exact ⟨by ac_rfl, h2, by ac_rfl⟩

lemma digits_swap23 (a b c : A) : digits a b c = digits a c b := by
  simp only [digits, Prod.mk.injEq]
  exact ⟨by ac_rfl, digit2_symm a b c, by ac_rfl⟩

lemma digits_rot (a b c : A) : digits a b c = digits b c a := by
  rw [digits_swap12, digits_swap23]

end MVAlgebra

/-! ### The group -/

/-- The ordered abelian group of an MV-chain: `(n, a)` stands for `n + a`, `a ≠ 1`. -/
@[ext] structure ChainGroup (A : Type*) [MVAlgebra A] where
  n : ℤ
  a : A
  ha : a ≠ 1

namespace ChainGroup

open MVAlgebra

variable {A : Type*} [MVAlgebra A] [MVChain A]

instance : Add (ChainGroup A) :=
  ⟨fun g h => ⟨g.n + h.n + carry g.a h.a, fsum g.a h.a, fsum_ne_one g.ha h.a⟩⟩

instance : Zero (ChainGroup A) := ⟨⟨0, 0, zero_ne_one'⟩⟩

instance : Neg (ChainGroup A) :=
  ⟨fun g => if h : g.a = 0 then ⟨-g.n, 0, zero_ne_one'⟩ else ⟨-g.n - 1, ∼g.a, neg_ne_one h⟩⟩

omit [MVChain A] in
lemma add_n (g h : ChainGroup A) : (g + h).n = g.n + h.n + carry g.a h.a := rfl
omit [MVChain A] in
lemma add_a (g h : ChainGroup A) : (g + h).a = fsum g.a h.a := rfl
lemma zero_n : (0 : ChainGroup A).n = 0 := rfl
lemma zero_a : (0 : ChainGroup A).a = 0 := rfl

lemma add_assoc' (g h k : ChainGroup A) : g + h + k = g + (h + k) := by
  have e1 := fold_eq g.a h.a k.a
  have e2 := fold_eq h.a k.a g.a
  rw [← digits_rot] at e2
  ext
  · simp only [add_n, add_a]
    rw [carry_comm g.a (fsum h.a k.a)]
    linarith [e1.1, e2.1]
  · rw [add_a, add_a, add_a, add_a, fsum_comm g.a (fsum h.a k.a), e1.2, e2.2]

omit [MVChain A] in
lemma add_comm' (g h : ChainGroup A) : g + h = h + g := by
  ext
  · rw [add_n, add_n, carry_comm]; ring
  · rw [add_a, add_a, fsum_comm]

lemma zero_add' (g : ChainGroup A) : 0 + g = g := by
  have h : (0 : A) ⨁ g.a ≠ 1 := by rw [add_left_zero]; exact g.ha
  ext
  · rw [add_n, zero_n, zero_a, carry_of_not h]; ring
  · rw [add_a, zero_a, fsum_of_not h, add_left_zero]

lemma neg_add_cancel' (g : ChainGroup A) : -g + g = 0 := by
  by_cases h : g.a = 0
  · have e : -g = ⟨-g.n, 0, zero_ne_one'⟩ := dite_eq_left h
    have h' : (0 : A) ⨁ g.a ≠ 1 := by rw [add_left_zero]; exact g.ha
    rw [e]
    ext
    · rw [add_n, zero_n]; show -g.n + g.n + carry 0 g.a = 0
      rw [carry_of_not h']; ring
    · rw [add_a, zero_a]; show fsum 0 g.a = 0
      rw [fsum_of_not h', add_left_zero, h]
  · have e : -g = ⟨-g.n - 1, ∼g.a, neg_ne_one h⟩ := dite_eq_right h
    rw [e]
    ext
    · rw [add_n, zero_n]; show -g.n - 1 + g.n + carry (∼g.a) g.a = 0
      rw [carry_of (neg_add_self g.a)]; ring
    · rw [add_a, zero_a]; show fsum (∼g.a) g.a = 0
      rw [fsum_of (neg_add_self g.a), neg_mul_self]

instance : AddCommGroup (ChainGroup A) where
  add_assoc := add_assoc'
  zero_add := zero_add'
  add_zero g := by rw [add_comm', zero_add']
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := neg_add_cancel'
  add_comm := add_comm'

/-! ### The lexicographic order -/

instance : LE (ChainGroup A) := ⟨fun g h => g.n < h.n ∨ (g.n = h.n ∧ MVAlgebra.le g.a h.a)⟩

omit [MVChain A] in
lemma le_def' {g h : ChainGroup A} : g ≤ h ↔ g.n < h.n ∨ (g.n = h.n ∧ MVAlgebra.le g.a h.a) :=
  Iff.rfl

instance : LinearOrder (ChainGroup A) where
  le_refl g := Or.inr ⟨rfl, MVAlgebra.le_refl _⟩
  le_trans g h k h1 h2 := by
    rcases h1 with h1 | ⟨e1, l1⟩ <;> rcases h2 with h2 | ⟨e2, l2⟩
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr ⟨e1.trans e2, MVAlgebra.le_trans l1 l2⟩
  le_antisymm g h h1 h2 := by
    rcases h1 with h1 | ⟨e1, l1⟩ <;> rcases h2 with h2 | ⟨e2, l2⟩
    · exfalso; omega
    · exfalso; omega
    · exfalso; omega
    · exact ChainGroup.ext e1 (MVAlgebra.le_antisymm l1 l2)
  le_total g h := by
    rcases lt_trichotomy g.n h.n with e | e | e
    · exact Or.inl (Or.inl e)
    · rcases MVChain.total g.a h.a with l | l
      · exact Or.inl (Or.inr ⟨e, l⟩)
      · exact Or.inr (Or.inr ⟨e.symm, l⟩)
    · exact Or.inr (Or.inl e)
  toDecidableLE := Classical.decRel _

instance : IsOrderedAddMonoid (ChainGroup A) where
  add_le_add_left g h hle k := by
    rw [le_def', add_n, add_n, add_a, add_a]
    rcases hle with hlt | ⟨heq, hl⟩
    · by_cases h1 : g.a ⨁ k.a = 1 <;> by_cases h2 : h.a ⨁ k.a = 1
      · left; rw [carry_of h1, carry_of h2]; linarith
      · by_cases hn : g.n + 1 < h.n
        · left; rw [carry_of h1, carry_of_not h2]; linarith
        · right
          refine ⟨by rw [carry_of h1, carry_of_not h2]; omega, ?_⟩
          rw [fsum_of h1, fsum_of_not h2]
          exact MVAlgebra.le_trans (mul_le_right _ _) (le_add_left _ _)
      · left; rw [carry_of_not h1, carry_of h2]; linarith
      · left; rw [carry_of_not h1, carry_of_not h2]; linarith
    · by_cases h1 : g.a ⨁ k.a = 1 <;> by_cases h2 : h.a ⨁ k.a = 1
      · right
        refine ⟨by rw [carry_of h1, carry_of h2, heq], ?_⟩
        rw [fsum_of h1, fsum_of h2]
        exact mul_le_mul_right' hl k.a
      · exact absurd (add_eq_one_of_le h1 hl) h2
      · left; rw [carry_of_not h1, carry_of h2, heq]; linarith
      · right
        refine ⟨by rw [carry_of_not h1, carry_of_not h2, heq], ?_⟩
        rw [fsum_of_not h1, fsum_of_not h2]
        exact add_le_add_right' hl k.a

/-! ### The embedding of `A` into `[0, u]` -/

/-- The strong unit `u = 1 + 0`. -/
def unit : ChainGroup A := ⟨1, 0, zero_ne_one'⟩

lemma unit_pos : (0 : ChainGroup A) < unit := by
  refine lt_of_le_of_ne (Or.inl (by show (0 : ℤ) < 1; norm_num)) ?_
  intro h
  have := congrArg ChainGroup.n h
  change (0 : ℤ) = 1 at this
  omega

/-- The embedding `x ↦ x` for `x ≠ 1`, and `1 ↦ u`. -/
def emb (x : A) : ChainGroup A := if hx : x = 1 then unit else ⟨0, x, hx⟩

lemma emb_one : emb (1 : A) = unit := dite_eq_left rfl

lemma emb_of_ne {x : A} (hx : x ≠ 1) : emb x = ⟨0, x, hx⟩ := dite_eq_right hx

lemma emb_zero : emb (0 : A) = 0 := emb_of_ne zero_ne_one'

lemma emb_mono {x y : A} (h : MVAlgebra.le x y) : emb x ≤ emb y := by
  by_cases hy : y = 1
  · subst hy
    by_cases hx : x = 1
    · subst hx; exact _root_.le_refl _
    · rw [emb_of_ne hx, emb_one]
      exact Or.inl (by show (0 : ℤ) < 1; norm_num)
  · have hx : x ≠ 1 := by
      intro hx; rw [hx] at h; exact hy (one_le_iff.mp h)
    rw [emb_of_ne hx, emb_of_ne hy]
    exact Or.inr ⟨rfl, h⟩

lemma emb_nonneg (x : A) : 0 ≤ emb x := by
  rw [← emb_zero]; exact emb_mono (MVAlgebra.zero_le x)

lemma emb_le_unit (x : A) : emb x ≤ unit := by
  rw [← emb_one]; exact emb_mono (le_one x)

lemma emb_eq_zero {x : A} (h : emb x = 0) : x = 0 := by
  by_cases hx : x = 1
  · rw [hx, emb_one] at h
    have := congrArg ChainGroup.n h
    change (1 : ℤ) = 0 at this
    omega
  · rw [emb_of_ne hx] at h
    exact congrArg ChainGroup.a h

/-- Sums without overflow are exact. -/
lemma emb_add_exact {a b : A} (h : a ⊙ b = 0) : emb a + emb b = emb (a ⨁ b) := by
  by_cases ha : a = 1
  · subst ha
    have hb : b = 0 := by rwa [MVAlgebra.one_mul] at h
    subst hb
    rw [emb_zero, _root_.add_zero, add_right_zero]
  by_cases hb : b = 1
  · subst hb
    have ha0 : a = 0 := by rwa [MVAlgebra.mul_one] at h
    subst ha0
    rw [emb_zero, _root_.zero_add, add_left_zero]
  rw [emb_of_ne ha, emb_of_ne hb]
  by_cases hab : a ⨁ b = 1
  · rw [hab, emb_one]
    ext
    · show 0 + 0 + carry a b = 1
      rw [carry_of hab]; norm_num
    · show fsum a b = 0
      rw [fsum_of hab, h]
  · rw [emb_of_ne hab]
    ext
    · show 0 + 0 + carry a b = 0
      rw [carry_of_not hab]; norm_num
    · show fsum a b = a ⨁ b
      rw [fsum_of_not hab]

lemma emb_msub (x y : A) : emb (x ⊖ y) = max (emb x - emb y) 0 := by
  rcases MVChain.total x y with h | h
  · rw [show x ⊖ y = 0 from h, emb_zero, max_eq_right (sub_nonpos.mpr (emb_mono h))]
  · have h0 : (x ⊖ y) ⊙ y = 0 := by
      rw [msub_eq_mul, ← MVAlgebra.mul_assoc, neg_mul_self, MVAlgebra.mul_zero]
    have hs : emb (x ⊖ y) + emb y = emb x := by
      rw [emb_add_exact h0, MVAlgebra.add_comm, ← eq_add_msub h]
    rw [← eq_sub_of_add_eq hs, max_eq_left (emb_nonneg _)]

lemma emb_neg (x : A) : emb (∼x) = unit - emb x := by
  rw [← one_msub, emb_msub, emb_one, max_eq_left (sub_nonneg.mpr (emb_le_unit x))]

lemma evalG_emb {ι : Type*} (v : ι → A) (φ : LukPropForm ι) :
    LukPropForm.evalG unit (emb ∘ v) φ = emb (evalMV v φ) := by
  induction φ with
  | var i => rfl
  | tsub φ ψ ihφ ihψ =>
    simp only [LukPropForm.evalG, evalMV, ihφ, ihψ]
    rw [emb_msub]
  | neg φ ih =>
    simp only [LukPropForm.evalG, evalMV, ih]
    rw [emb_neg]

end ChainGroup

open MVAlgebra in
/-- A formula with a non-zero value in an MV-chain has a non-zero value under some
    `[0, 1]`-assignment. -/
theorem exists_real_of_evalMV_chain_ne_zero {ι A : Type*} [MVAlgebra A] [MVChain A]
    (v : ι → A) (φ : LukPropForm ι) (h : evalMV v φ ≠ 0) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i ∧ w i ≤ 1) ∧ LukPropForm.eval w φ ≠ 0 :=
  LukPropForm.exists_real_of_evalG_ne_zero ChainGroup.unit ChainGroup.unit_pos
    (ChainGroup.emb ∘ v) (fun _ => ⟨ChainGroup.emb_nonneg _, ChainGroup.emb_le_unit _⟩) φ
    (by rw [ChainGroup.evalG_emb]; exact fun h' => h (ChainGroup.emb_eq_zero h'))

end ContinuousFOL
