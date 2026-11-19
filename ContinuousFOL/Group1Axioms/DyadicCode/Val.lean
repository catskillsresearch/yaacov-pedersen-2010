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
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

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

/-- Truncated addition via `¬(¬a ∸ b)`, evaluating to `min(a.val + b.val, 1)`. -/
def add (a b : DyadicCode) : DyadicCode := .neg (.tsub (.neg a) b)

lemma val_add {a b : DyadicCode} (h : a.val + b.val ≤ 1) :
    (add a b).val = a.val + b.val := by
  have ha := val_mem_Icc a
  have hb := val_mem_Icc b
  simp only [add, val]
  have hnonneg : 0 ≤ 1 - a.val - b.val := by linarith
  simp [tsubR, hnonneg]
  ring

/-- `k · 2⁻ⁿ` as a dyadic code (for `k ≤ 2ⁿ`). -/
def mulPow2Neg : ℕ → ℕ → DyadicCode
  | 0, _ => zero
  | k + 1, n => add (mulPow2Neg k n) (pow2Neg n)

lemma val_mulPow2Neg (k n : ℕ) (hk : k ≤ 2 ^ n) :
    (mulPow2Neg k n).val = k * (2 : ℝ) ^ (-(n : ℤ)) := by
  induction k with
  | zero => simp [mulPow2Neg]
  | succ k ih =>
    have hk' : k ≤ 2 ^ n := Nat.le_of_succ_le hk
    have hsum : (mulPow2Neg k n).val + (pow2Neg n).val ≤ 1 := by
      rw [ih hk', val_pow2Neg]
      have hk1 : (k + 1 : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast hk
      have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-(n : ℤ)) :=
        zpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
      calc
        (k : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) + (2 : ℝ) ^ (-(n : ℤ))
            = (k + 1 : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) := by ring
          _ ≤ ((2 : ℝ) ^ n) * (2 : ℝ) ^ (-(n : ℤ)) := mul_le_mul_of_nonneg_right hk1 hpos
          _ = 1 := by
              rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
              simp
    rw [mulPow2Neg, val_add hsum, ih hk', val_pow2Neg]
    push_cast
    ring

/-- The set of dyadic numbers \(\mathbb{D}\) from Remark 3.4: numbers of the form
    \(k / 2^n\) where \(k, n < \omega\) and \(k \le 2^n\). -/
def dyadics : Set ℝ :=
  { x | ∃ (k n : ℕ), k ≤ 2 ^ n ∧ x = (k : ℝ) / (2 : ℝ) ^ n }

lemma exists_val_eq_div (d : DyadicCode) :
    ∃ k n : ℕ, k ≤ 2 ^ n ∧ d.val = (k : ℝ) / (2 : ℝ) ^ n := by
  induction d with
  | one =>
    exact ⟨1, 0, by simp, by simp⟩
  | neg d ih =>
    obtain ⟨k, n, hk, hval⟩ := ih
    refine ⟨2 ^ n - k, n, Nat.sub_le _ _, ?_⟩
    have hcast : ((2 ^ n - k : ℕ) : ℝ) = (2 : ℝ) ^ n - (k : ℝ) := by
      rw [Nat.cast_sub hk, Nat.cast_pow, Nat.cast_ofNat]
    simp only [val, hval, hcast, sub_div]
    have : (2 : ℝ) ^ n / (2 : ℝ) ^ n = 1 :=
      div_self (pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0))
    linarith
  | half d ih =>
    obtain ⟨k, n, hk, hval⟩ := ih
    refine ⟨k, n + 1,
      hk.trans (Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) n.le_succ), ?_⟩
    simp only [val, hval, pow_succ, div_div, mul_comm]
  | tsub a b iha ihb =>
    obtain ⟨k, n, hk, ha⟩ := iha
    obtain ⟨l, m, hl, hb⟩ := ihb
    set N := max n m
    have hn : n ≤ N := Nat.le_max_left _ _
    have hm : m ≤ N := Nat.le_max_right _ _
    set k' := k * 2 ^ (N - n) with hk'_def
    set l' := l * 2 ^ (N - m) with hl'_def
    have h2N : (0 : ℝ) < (2 : ℝ) ^ N := pow_pos (by norm_num) _
    have ha' : a.val = (k' : ℝ) / (2 : ℝ) ^ N := by
      have hpow : (2 : ℝ) ^ N = (2 : ℝ) ^ n * (2 : ℝ) ^ (N - n) := by
        rw [← pow_add, Nat.add_sub_of_le hn]
      rw [ha, hpow, hk'_def, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    have hb' : b.val = (l' : ℝ) / (2 : ℝ) ^ N := by
      have hpow : (2 : ℝ) ^ N = (2 : ℝ) ^ m * (2 : ℝ) ^ (N - m) := by
        rw [← pow_add, Nat.add_sub_of_le hm]
      rw [hb, hpow, hl'_def, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      field_simp
    have hk'le : k' ≤ 2 ^ N := by
      have : k * 2 ^ (N - n) ≤ 2 ^ n * 2 ^ (N - n) := Nat.mul_le_mul_right _ hk
      simpa [k', ← pow_add, Nat.add_sub_of_le hn] using this
    by_cases hkl : k' ≤ l'
    · refine ⟨0, N, Nat.zero_le _, ?_⟩
      have hab : a.val ≤ b.val := by
        rw [ha', hb']
        exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hkl) h2N.le
      simp only [val, Nat.cast_zero, zero_div]
      exact (tsubR.eq_zero_iff _ _).mpr hab
    · have hle : l' ≤ k' := le_of_lt (lt_of_not_ge hkl)
      refine ⟨k' - l', N, (Nat.sub_le _ _).trans hk'le, ?_⟩
      have hval : a.val - b.val = ((k' - l' : ℕ) : ℝ) / (2 : ℝ) ^ N := by
        rw [ha', hb', Nat.cast_sub hle, sub_div]
      have hab : b.val ≤ a.val := by
        rw [ha', hb']
        exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hle) h2N.le
      simp only [val]
      rw [tsubR, max_eq_left (sub_nonneg.mpr hab), hval]

lemma val_mulPow2Neg_div (k n : ℕ) (hk : k ≤ 2 ^ n) :
    (mulPow2Neg k n).val = (k : ℝ) / (2 : ℝ) ^ n := by
  rw [val_mulPow2Neg k n hk, zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- Remark 3.4: on any truth assignment \(v\), the set \(\mathcal{D}\) generated from
    \(1\) by the operations \(\neg\), \(\dot{-}\), and \(\frac{1}{2}\) satisfies
    \(\{v(d) : d \in \mathcal{D}\} = \mathbb{D}\).
    The map `val` is the (assignment-independent) value of a code in \(\mathcal{D}\);
    see `Formula.eval_dyadic` and `CLPropForm.eval_dyadic`. -/
theorem val_range_eq_dyadics : Set.range val = dyadics := by
  ext x
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨k, n, hk, hval⟩ := exists_val_eq_div d
    exact ⟨k, n, hk, hval⟩
  · rintro ⟨k, n, hk, rfl⟩
    exact ⟨mulPow2Neg k n, val_mulPow2Neg_div k n hk⟩

/-- The dyadic numbers are dense in `[0, 1]`. -/
lemma dense_in_Icc {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y) :
    ∃ d : DyadicCode, x < d.val ∧ d.val < y := by
  have hpos : 0 < y - x := sub_pos.mpr hxy
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((2 : ℝ)⁻¹) ^ n < y - x :=
    exists_pow_lt_of_lt_one hpos (by norm_num)
  have hn' : (2 : ℝ) ^ (-(n : ℤ)) < y - x := by
    convert hn using 1
    simp [← zpow_natCast]
  set k : ℕ := ⌊x * (2 : ℝ) ^ n⌋₊ + 1 with hk_def
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hx_nonneg_mul : 0 ≤ x * (2 : ℝ) ^ n := mul_nonneg hx (le_of_lt hpow_pos)
  have h2n : (2 : ℝ) ^ (-(n : ℤ)) = ((2 : ℝ) ^ n)⁻¹ := by
    simp [← zpow_natCast]
  have hx_lt : x < (k : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) := by
    have hlt : x * (2 : ℝ) ^ n < k := by
      simpa [hk_def] using Nat.lt_floor_add_one (x * (2 : ℝ) ^ n)
    rw [h2n, ← div_eq_mul_inv]
    exact (lt_div_iff₀ hpow_pos).2 hlt
  have hk_le : (k : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) ≤ x + (2 : ℝ) ^ (-(n : ℤ)) := by
    have hfloor : (k : ℝ) ≤ x * (2 : ℝ) ^ n + 1 := by
      have : (⌊x * (2 : ℝ) ^ n⌋₊ : ℝ) ≤ x * (2 : ℝ) ^ n := Nat.floor_le hx_nonneg_mul
      simp only [hk_def]
      push_cast
      linarith
    rw [h2n, ← div_eq_mul_inv]
    have : (k : ℝ) / (2 : ℝ) ^ n ≤ x + ((2 : ℝ) ^ n)⁻¹ := by
      rw [div_le_iff₀ hpow_pos, add_mul, inv_mul_cancel₀ hpow_pos.ne']
      linarith
    simpa [div_eq_mul_inv] using this
  have hval_lt_y : (k : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) < y :=
    lt_of_le_of_lt hk_le (by linarith)
  have hk_pow : k ≤ 2 ^ n := by
    have hlt1 : (k : ℝ) * (2 : ℝ) ^ (-(n : ℤ)) < 1 := lt_of_lt_of_le hval_lt_y hy
    rw [h2n, ← div_eq_mul_inv] at hlt1
    have : (k : ℝ) < (2 : ℝ) ^ n := (div_lt_one hpow_pos).1 hlt1
    exact_mod_cast this.le
  refine ⟨mulPow2Neg k n, ?_, ?_⟩
  · simpa [val_mulPow2Neg k n hk_pow] using hx_lt
  · simpa [val_mulPow2Neg k n hk_pow] using hval_lt_y

end DyadicCode

end ContinuousFOL
