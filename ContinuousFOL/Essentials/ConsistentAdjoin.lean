/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.5; vision.md page 17
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.Completeness.ProvableTsubOfInconsistentAdjoin
public import ContinuousFOL.Essentials.ProvableBoundSubst
public import ContinuousFOL.Group1Axioms.DyadicCode.Val
public import ContinuousFOL.Group1Axioms.CLPropForm.Dyadic
public import ContinuousFOL.Group1Axioms.CLPropForm.IterSub
public import ContinuousFOL.Group1Axioms.DyadicCode.Pow2Neg

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

lemma CLPropForm.eval_dyadic {I : Type*} (v : I → ℝ) (a : I) (d : DyadicCode) :
    (CLPropForm.dyadic (.var a) d).eval v = d.val := by
  induction d with
  | one => simp [CLPropForm.dyadic, CLPropForm.one, CLPropForm.eval, DyadicCode.val, tsubR]
  | neg d ih => simp [CLPropForm.dyadic, CLPropForm.eval, DyadicCode.val, ih]
  | tsub d e ihd ihe => simp [CLPropForm.dyadic, CLPropForm.eval, DyadicCode.val, ihd, ihe]
  | half d ih => simp [CLPropForm.dyadic, CLPropForm.eval, DyadicCode.val, ih]

lemma CLPropForm.toFormula_dyadic {I : Type*} {L : Signature} (f : I → Formula L) (a : I)
    (ha : f a = Formula.defaultAtom L) (d : DyadicCode) :
    (CLPropForm.dyadic (.var a) d).toFormula f = Formula.dyadic L d := by
  induction d with
  | one => simp [CLPropForm.dyadic, CLPropForm.one, CLPropForm.toFormula, Formula.dyadic,
      Formula.one, ha]
  | neg d ih => simp [CLPropForm.dyadic, CLPropForm.toFormula, Formula.dyadic, ih]
  | tsub d e ihd ihe =>
    simp [CLPropForm.dyadic, CLPropForm.toFormula, Formula.dyadic, ihd, ihe]
  | half d ih => simp [CLPropForm.dyadic, CLPropForm.toFormula, Formula.dyadic, ih]

lemma CLPropForm.eval_iterSub {I : Type*} (v : I → ℝ) (ψ φ : CLPropForm I) (k : ℕ) :
    (CLPropForm.iterSub ψ φ k).eval v = iterSubR (ψ.eval v) (φ.eval v) k := by
  induction k with
  | zero => simp [CLPropForm.iterSub, iterSubR]
  | succ k ih => simp [CLPropForm.iterSub, iterSubR, CLPropForm.eval, ih]

lemma CLPropForm.toFormula_iterSub {I : Type*} {L : Signature} (f : I → Formula L)
    (ψ φ : CLPropForm I) (k : ℕ) :
    (CLPropForm.iterSub ψ φ k).toFormula f =
      Formula.iterSub (ψ.toFormula f) (φ.toFormula f) k := by
  induction k with
  | zero => simp [CLPropForm.iterSub, Formula.iterSub]
  | succ k ih => simp [CLPropForm.iterSub, Formula.iterSub, CLPropForm.toFormula, ih]

/-- Real form of the Lemma 8.5(i) schema: if `4mc < 1` then
    `((½ ∸ (1 ∸ m a)) ∸ 2m (a ∸ c)) = 0`. -/
lemma approx_schema_real (m : ℕ) {a c : ℝ} (ha : 0 ≤ a) (hc : 4 * ((m : ℝ) * c) < 1) :
    iterSubR ((1 / 2 : ℝ) ∸ iterSubR 1 a m) (a ∸ c) (2 * m) = 0 := by
  rw [iterSubR_eq zero_le_one ha m, iterSubR_eq (tsubR.nonneg _ _) (tsubR.nonneg _ _)]
  simp only [tsubR.def_eq]
  apply max_eq_right
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hcast : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
  rw [hcast]
  rcases le_total a c with hac | hac
  · have hp : (m : ℝ) * a ≤ (m : ℝ) * c := mul_le_mul_of_nonneg_left hac hm
    have h1 : max (1 - (m : ℝ) * a) 0 = 1 - (m : ℝ) * a := max_eq_left (by linarith)
    have h2 : max (a - c) 0 = 0 := max_eq_right (by linarith)
    rw [h1, h2, max_eq_right (by linarith)]
    simp
  · have hp : (m : ℝ) * c ≤ (m : ℝ) * a := mul_le_mul_of_nonneg_left hac hm
    have hma : 0 ≤ (m : ℝ) * a := mul_nonneg hm ha
    have h2 : max (a - c) 0 = a - c := max_eq_left (by linarith)
    rw [h2]
    have hexp : 2 * (m : ℝ) * (a - c) = 2 * ((m : ℝ) * a) - 2 * ((m : ℝ) * c) := by ring
    rw [hexp]
    have hb : 1 - (m : ℝ) * a ≤ max (1 - (m : ℝ) * a) 0 := le_max_left _ _
    have hM : max (1 / 2 - max (1 - (m : ℝ) * a) 0) 0 ≤
        2 * ((m : ℝ) * a) - 2 * ((m : ℝ) * c) :=
      max_le (by linarith) (by linarith)
    linarith

/-- CL schema for Lemma 8.5(i):
    `⊢ ((½ ∸ (1 ∸ mφ)) ∸ 2m(φ ∸ 2^{-(m+2)}))`. -/
lemma ProvableQ.approx_schema {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) (m : ℕ) :
    ProvableQ Γ (Formula.iterSub
      (.tsub (.half (Formula.one L)) (Formula.iterSub (Formula.one L) φ m))
      (.tsub φ (Formula.pow2Neg L (m + 2))) (2 * m)) := by
  let one' : CLPropForm (Fin 2) := CLPropForm.one (.var 1)
  let T : CLPropForm (Fin 2) := CLPropForm.iterSub
    (.tsub (.half one') (CLPropForm.iterSub one' (.var 0) m))
    (.tsub (.var 0) (CLPropForm.dyadic (.var 1) (.pow2Neg (m + 2)))) (2 * m)
  have h := CLPropForm.toFormula_provable_of_valid (Γ := Γ) ![φ, Formula.defaultAtom L] T (by
    intro v hv
    obtain ⟨h0, _⟩ := hv 0
    have hone : one'.eval v = 1 := by simp [one', CLPropForm.one, CLPropForm.eval, tsubR]
    simp only [T, CLPropForm.eval_iterSub, CLPropForm.eval, hone, CLPropForm.eval_dyadic,
      DyadicCode.val_pow2Neg]
    have hc : 4 * ((m : ℝ) * (2 : ℝ) ^ (-((m + 2 : ℕ) : ℤ))) < 1 := by
      rw [zpow_neg, zpow_natCast]
      have hlt : (4 * m : ℝ) < 2 ^ (m + 2) := by
        have := Nat.lt_two_pow_self (n := m)
        have h' : (m : ℝ) < 2 ^ m := by exact_mod_cast this
        rw [pow_add]; norm_num; linarith
      have hpos : (0 : ℝ) < 2 ^ (m + 2) := by positivity
      rw [← mul_assoc, ← div_eq_mul_inv, div_lt_one hpos]
      exact hlt
    have := approx_schema_real m h0 hc
    simpa [one_div] using this)
  have hform : T.toFormula ![φ, Formula.defaultAtom L] =
      Formula.iterSub (.tsub (.half (Formula.one L)) (Formula.iterSub (Formula.one L) φ m))
        (.tsub φ (Formula.pow2Neg L (m + 2))) (2 * m) := by
    have hone : one'.toFormula ![φ, Formula.defaultAtom L] = Formula.one L := by
      simp [one', CLPropForm.one, CLPropForm.toFormula, Formula.one]
    simp only [T, CLPropForm.toFormula_iterSub, CLPropForm.toFormula, hone,
      CLPropForm.toFormula_dyadic ![φ, Formula.defaultAtom L] 1 rfl, Formula.pow2Neg]
    rfl
  rw [hform] at h
  exact h

/-- CL: `⊢ (1 ∸ ½) ∸ ½`. -/
lemma ProvableQ.one_sub_two_halves {L : Signature} (Γ : Set (Formula L)) :
    ProvableQ Γ (Formula.iterSub (Formula.one L) (.half (Formula.one L)) 2) := by
  have h := CLPropForm.toFormula_provable_of_valid (Γ := Γ) ![Formula.defaultAtom L]
    (CLPropForm.iterSub (CLPropForm.one (.var 0)) (.half (CLPropForm.one (.var 0))) 2) (by
      intro v _
      simp [CLPropForm.iterSub, CLPropForm.one, CLPropForm.eval, tsubR]
      norm_num)
  simpa [CLPropForm.iterSub, Formula.iterSub, CLPropForm.one, CLPropForm.toFormula,
    Formula.one] using h

/-- Lemma 8.5: Closure properties of consistent sets. -/
theorem consistent_adjoin_approx {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) (φ : Formula L)
    (happrox : ∀ n : ℕ, ProvableQ Γ (.tsub φ (Formula.pow2Neg L n))) :
    ConsistentQ (Γ ∪ {φ}) := by
  by_contra hincons
  have h1 : ProvableQ (Γ ∪ {φ}) (Formula.one L) := (inconsistent_iff_provable_one _).mp hincons
  obtain ⟨m, hm⟩ := (deduction_theorem Γ (Formula.one L) φ).mp h1
  have hD0 := ProvableQ.cancel_iterSub (happrox (m + 2)) (2 * m)
    (ProvableQ.approx_schema Γ φ m)
  have hD : ProvableQ Γ (.half (Formula.one L)) := ProvableQ.mp hm hD0
  exact (inconsistent_iff_provable_one Γ).mpr
    (ProvableQ.cancel_iterSub hD 2 (ProvableQ.one_sub_two_halves Γ)) hcons

lemma ProvableQ.one_of_iterSub_one {L : Signature} {Γ : Set (Formula L)} {θ : Formula L}
    (hθ : ProvableQ Γ θ) (n : ℕ)
    (h : ProvableQ Γ (Formula.iterSub (Formula.one L) θ n)) :
    ProvableQ Γ (Formula.one L) := by
  induction n with
  | zero => simpa [Formula.iterSub] using h
  | succ n ih =>
    exact ih (by simpa [Formula.iterSub] using ProvableQ.mp hθ h)

theorem consistent_adjoin_comparable {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) (φ ψ : Formula L) :
    ConsistentQ (Γ ∪ {.tsub φ ψ}) ∨ ConsistentQ (Γ ∪ {.tsub ψ φ}) := by
  by_cases hleft : ConsistentQ (Γ ∪ {.tsub φ ψ})
  · exact Or.inl hleft
  · refine Or.inr ?_
    by_contra hright
    have hswap : ProvableQ Γ (.tsub ψ φ) := by
      have h1 : ProvableQ (Γ ∪ {.tsub φ ψ}) (Formula.one L) :=
        (inconsistent_iff_provable_one _).mp hleft
      obtain ⟨n, hn⟩ := (deduction_theorem Γ (Formula.one L) (.tsub φ ψ)).mp h1
      exact ProvableQ.mp hn (ProvableQ.swap_one_iter Γ ψ φ n)
    have h1 : ProvableQ (Γ ∪ {.tsub ψ φ}) (Formula.one L) :=
      (inconsistent_iff_provable_one _).mp hright
    obtain ⟨n, hn⟩ := (deduction_theorem Γ (Formula.one L) (.tsub ψ φ)).mp h1
    exact (inconsistent_iff_provable_one Γ).mpr
      (ProvableQ.one_of_iterSub_one hswap n hn) hcons

end ContinuousFOL
