/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Theorem 8.1; vision.md page 16
-/
module

public import ContinuousFOL.Group2Axioms.ProvableQ
public import ContinuousFOL.Group2Axioms.ProvableMetricQ
public import ContinuousFOL.LanguageAndSemantics.FormulaIterSub
public import ContinuousFOL.Essentials.ProvableQMono
public import Mathlib.Data.Finset.Basic
public import ContinuousFOL.Essentials.InconsistentIffProvableOne
public import ContinuousFOL.BlackBox.LukWeakCompleteness
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Iterated truncated subtraction on `ℝ`. -/
def iterSubR (b a : ℝ) : ℕ → ℝ
  | 0 => b
  | n + 1 => iterSubR b a n ∸ a

lemma iterSubR_eq {b a : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) (k : ℕ) :
    iterSubR b a k = max (b - (k : ℝ) * a) 0 := by
  induction k with
  | zero =>
    simp [iterSubR, max_eq_left hb]
  | succ k ih =>
    rw [iterSubR, ih, tsubR.def_eq]
    by_cases h : b ≤ (k : ℝ) * a
    · have hnonpos : b - (k : ℝ) * a ≤ 0 := by linarith
      rw [max_eq_right hnonpos]
      have hsub : (0 : ℝ) - a ≤ 0 := by linarith
      rw [max_eq_right hsub]
      have htail : b - ((k + 1 : ℕ) : ℝ) * a ≤ 0 := by
        push_cast
        linarith
      exact (max_eq_right htail).symm
    · push Not at h
      have hpos : 0 ≤ b - (k : ℝ) * a := by linarith
      rw [max_eq_left hpos]
      have hdiff : b - (k : ℝ) * a - a = b - ((k + 1 : ℕ) : ℝ) * a := by
        push_cast
        ring
      rw [hdiff]

lemma tsubR_zero {x : ℝ} (hx : 0 ≤ x) : x ∸ 0 = x := by
  rw [tsubR.def_eq]
  have : x - 0 = x := by ring
  rw [this, max_eq_left hx]

/-- Real form of the deduction-theorem schema. -/
lemma deduction_schema_real {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (n m : ℕ) :
    (iterSubR b a (n + m) ∸ iterSubR (b ∸ c) a n) ∸ iterSubR c a m = 0 := by
  have hna0 : 0 ≤ (n : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha
  have hma0 : 0 ≤ (m : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha
  have hsplit : ((n + m : ℕ) : ℝ) * a = (n : ℝ) * a + (m : ℝ) * a := by
    push_cast
    ring
  have hbsub : 0 ≤ b ∸ c := tsubR.nonneg _ _
  rw [iterSubR_eq hb ha (n + m), iterSubR_eq hbsub ha n, iterSubR_eq hc ha m,
    tsubR.eq_zero_iff]
  set na := (n : ℝ) * a
  set ma := (m : ℝ) * a
  have hsum : ((n + m : ℕ) : ℝ) * a = na + ma := by simpa [na, ma] using hsplit
  have hL0 : 0 ≤ max (b - (na + ma)) 0 := le_max_right _ _
  by_cases hbc : b ≤ c
  · have hM : max ((b ∸ c) - na) 0 = 0 := by
      rw [(tsubR.eq_zero_iff b c).mpr hbc]
      exact max_eq_right (by linarith)
    rw [hM, hsum, tsubR_zero hL0]
    exact max_le_max (by linarith) le_rfl
  · push Not at hbc
    have hbc' : b ∸ c = b - c := by
      rw [tsubR.def_eq, max_eq_left (by linarith)]
    rw [hbc']
    by_cases hna : b - c ≤ na
    · have hM : max (b - c - na) 0 = 0 := max_eq_right (by linarith)
      rw [hM, hsum, tsubR_zero hL0]
      exact max_le_max (by linarith) le_rfl
    · push Not at hna
      have hM : max (b - c - na) 0 = b - c - na := max_eq_left (by linarith)
      rw [hM, hsum]
      by_cases htail : b - (na + ma) ≤ 0
      · have hL : max (b - (na + ma)) 0 = 0 := max_eq_right htail
        rw [hL]
        have : (0 : ℝ) ∸ (b - c - na) = 0 := by
          rw [tsubR.def_eq, max_eq_right (by linarith)]
        rw [this]
        exact le_max_right _ _
      · push Not at htail
        have hL : max (b - (na + ma)) 0 = b - (na + ma) := max_eq_left (by linarith)
        rw [hL]
        have hdiff : b - (na + ma) - (b - c - na) = c - ma := by ring
        rw [tsubR.def_eq, hdiff]

/-- Instantiate a propositional Łukasiewicz formula by first-order formulae. -/
def LukPropForm.toFormula {I : Type*} {L : Signature} (f : I → Formula L) :
    LukPropForm I → Formula L
  | .var i => f i
  | .tsub φ ψ => .tsub (toFormula f φ) (toFormula f ψ)
  | .neg φ => .neg (toFormula f φ)

lemma LukPropForm.toFormula_provable {I : Type*} {L : Signature} (f : I → Formula L)
    {φ : LukPropForm I} (h : LukPropForm.Provable ∅ φ) :
    ProvableQ (∅ : Set (Formula L)) (φ.toFormula f) := by
  induction h with
  | ax hax =>
    cases hax with
    | A1 φ ψ =>
      simpa [LukPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := (∅ : Set (Formula L))) (.A1 (φ.toFormula f) (ψ.toFormula f)))
    | A2 φ ψ χ =>
      simpa [LukPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := (∅ : Set (Formula L)))
          (.A2 (φ.toFormula f) (ψ.toFormula f) (χ.toFormula f)))
    | A3 φ ψ =>
      simpa [LukPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := (∅ : Set (Formula L)))
          (.A3 (φ.toFormula f) (ψ.toFormula f)))
    | A4 φ ψ =>
      simpa [LukPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := (∅ : Set (Formula L)))
          (.A4 (φ.toFormula f) (ψ.toFormula f)))
  | hyp hmem =>
    simp at hmem
  | mp _ _ ih₁ ih₂ =>
    exact ProvableQ.mp ih₁ ih₂

namespace LukPropForm

def iterSub {I : Type*} (ψ φ : LukPropForm I) : ℕ → LukPropForm I
  | 0 => ψ
  | n + 1 => .tsub (iterSub ψ φ n) φ

/-- Schema `((β ⊖_{n+m} α) ∸ ((β ∸ γ) ⊖_n α)) ∸ (γ ⊖_m α)`. -/
def deductionSchema (n m : ℕ) : LukPropForm (Fin 3) :=
  let α : LukPropForm (Fin 3) := .var 0
  let β : LukPropForm (Fin 3) := .var 1
  let γ : LukPropForm (Fin 3) := .var 2
  .tsub (.tsub (iterSub β α (n + m)) (iterSub (.tsub β γ) α n)) (iterSub γ α m)

lemma eval_iterSub {I : Type*} (v : I → ℝ) (ψ φ : LukPropForm I) (k : ℕ) :
    (iterSub ψ φ k).eval v = iterSubR (ψ.eval v) (φ.eval v) k := by
  induction k with
  | zero => simp [iterSub, iterSubR]
  | succ k ih => simp [iterSub, iterSubR, eval, ih]

lemma toFormula_iterSub {I : Type*} {L : Signature} (f : I → Formula L)
    (ψ φ : LukPropForm I) (k : ℕ) :
    (iterSub ψ φ k).toFormula f =
      Formula.iterSub (ψ.toFormula f) (φ.toFormula f) k := by
  induction k with
  | zero => simp [iterSub, Formula.iterSub]
  | succ k ih => simp [iterSub, Formula.iterSub, LukPropForm.toFormula, ih]

lemma deductionSchema_entails (n m : ℕ) : Entails ∅ (deductionSchema n m) := by
  intro v hv
  have ha : 0 ≤ v 0 ∧ v 0 ≤ 1 := hv.1 0
  have hb : 0 ≤ v 1 ∧ v 1 ≤ 1 := hv.1 1
  have hc : 0 ≤ v 2 ∧ v 2 ≤ 1 := hv.1 2
  have hreal := deduction_schema_real (a := v 0) (b := v 1) (c := v 2) ha.1 hb.1 hc.1 n m
  simpa [deductionSchema, eval, eval_iterSub] using hreal

lemma deductionSchema_provable (n m : ℕ) : Provable ∅ (deductionSchema n m) :=
  (luk_weak_completeness (deductionSchema n m)).mp (deductionSchema_entails n m)

end LukPropForm

lemma ProvableQ.deduction_schema {L : Signature} (Γ : Set (Formula L))
    (β γ α : Formula L) (n m : ℕ) :
    ProvableQ Γ (.tsub
      (.tsub (Formula.iterSub β α (n + m)) (Formula.iterSub (.tsub β γ) α n))
      (Formula.iterSub γ α m)) := by
  have h0 := LukPropForm.toFormula_provable
    (L := L) (f := fun i : Fin 3 => if i = 0 then α else if i = 1 then β else γ)
    (LukPropForm.deductionSchema_provable n m)
  have hform :
      (LukPropForm.deductionSchema n m).toFormula
        (fun i : Fin 3 => if i = 0 then α else if i = 1 then β else γ) =
      .tsub (.tsub (Formula.iterSub β α (n + m)) (Formula.iterSub (.tsub β γ) α n))
        (Formula.iterSub γ α m) := by
    simp only [LukPropForm.deductionSchema, LukPropForm.toFormula, LukPropForm.toFormula_iterSub]
    simp
  rw [hform] at h0
  exact h0.mono (by simp)

lemma ProvableQ.cancel_iterSub {L : Signature} {Γ : Set (Formula L)} {φ ψ : Formula L}
    (hψ : ProvableQ Γ ψ) (n : ℕ) (h : ProvableQ Γ (Formula.iterSub φ ψ n)) :
    ProvableQ Γ φ := by
  induction n generalizing φ with
  | zero =>
    simpa [Formula.iterSub] using h
  | succ n ih =>
    have hstep : ProvableQ Γ (Formula.iterSub φ ψ n) := by
      simpa [Formula.iterSub] using ProvableQ.mp hψ h
    exact ih hstep

/-- Theorem 8.1 (Weak Deduction Theorem). -/
theorem deduction_theorem {L : Signature} (Γ : Set (Formula L)) (φ ψ : Formula L) :
    ProvableQ (Γ ∪ {ψ}) φ ↔ ∃ n : ℕ, ProvableQ Γ (Formula.iterSub φ ψ n) := by
  constructor
  · intro h
    induction h with
    | @ax xs ψax hax =>
      exact ⟨0, by simpa [Formula.iterSub] using (ProvableQ.ax (Γ := Γ) hax)⟩
    | @hyp θ hmem =>
      rcases (Set.mem_union θ Γ {ψ}).mp hmem with hΓ | hψ
      · exact ⟨0, by simpa [Formula.iterSub] using ProvableQ.hyp hΓ⟩
      · have hθeq : θ = ψ := by simpa [Set.mem_singleton_iff] using hψ
        exact ⟨1, by
          simpa [hθeq, Formula.iterSub] using (ProvableQ.imp_refl (Γ := Γ) θ)⟩
    | @mp α β hα himp ihα ihimp =>
      obtain ⟨n, hn⟩ := ihα
      obtain ⟨m, hm⟩ := ihimp
      have hsch := ProvableQ.deduction_schema (Γ := Γ) β α ψ m n
      have hstep : ProvableQ Γ
          (.tsub (Formula.iterSub β ψ (m + n)) (Formula.iterSub (.tsub β α) ψ m)) :=
        ProvableQ.mp hn (by simpa [Nat.add_comm] using hsch)
      exact ⟨m + n, ProvableQ.mp hm hstep⟩
  · rintro ⟨n, hn⟩
    exact ProvableQ.cancel_iterSub (.hyp (Set.mem_union_right _ (Set.mem_singleton _))) n
      (hn.mono (by intro θ hθ; exact Set.mem_union_left _ hθ))

lemma ProvableMetricQ.of_provableQ {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} {φ : Formula LM.toSignature}
    (h : ProvableQ Γ φ) : ProvableMetricQ Γ φ := by
  induction h with
  | @ax xs ψ hax => exact .ax (xs := xs) (.base hax)
  | hyp hmem => exact .hyp hmem
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

lemma ProvableMetricQ.mono {LM : MetricSignature}
    {Γ Γ' : Set (Formula LM.toSignature)} (hsub : Γ ⊆ Γ')
    {φ : Formula LM.toSignature} (h : ProvableMetricQ Γ φ) : ProvableMetricQ Γ' φ := by
  induction h with
  | ax hax => exact .ax hax
  | hyp hmem => exact .hyp (hsub hmem)
  | mp h₁ h₂ ih₁ ih₂ => exact .mp ih₁ ih₂

lemma ProvableMetricQ.compact {LM : MetricSignature} {Γ : Set (Formula LM.toSignature)} :
    ∀ {φ : Formula LM.toSignature}, ProvableMetricQ Γ φ →
      ∃ Γ₀ : Finset (Formula LM.toSignature),
        (↑Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ ∧ ProvableMetricQ (↑Γ₀) φ := by
  intro φ h
  induction h with
  | ax hax => exact ⟨∅, by simp [Finset.coe_empty], .ax hax⟩
  | hyp hmem =>
    refine ⟨{_}, ?_, .hyp (Finset.mem_singleton_self _)⟩
    simpa [Finset.coe_singleton] using Set.singleton_subset_iff.mpr hmem
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, h₁s, hp₁⟩ := ih₁
    obtain ⟨Γ₂, h₂s, hp₂⟩ := ih₂
    refine ⟨Γ₁ ∪ Γ₂, ?_, .mp (hp₁.mono ?_) (hp₂.mono ?_)⟩
    · simpa [Finset.coe_union] using Set.union_subset h₁s h₂s
    · simp [Finset.coe_union]
    · simp [Finset.coe_union]

lemma ProvableMetricQ.cancel_iterSub {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} {φ ψ : Formula LM.toSignature}
    (hψ : ProvableMetricQ Γ ψ) (n : ℕ)
    (h : ProvableMetricQ Γ (Formula.iterSub φ ψ n)) : ProvableMetricQ Γ φ := by
  induction n generalizing φ with
  | zero => simpa [Formula.iterSub] using h
  | succ n ih =>
    exact ih (by simpa [Formula.iterSub] using ProvableMetricQ.mp hψ h)

theorem deduction_theorem_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ ψ : Formula LM.toSignature) :
    ProvableMetricQ (Γ ∪ {ψ}) φ ↔
      ∃ n : ℕ, ProvableMetricQ Γ (Formula.iterSub φ ψ n) := by
  constructor
  · intro h
    induction h with
    | ax hax =>
      exact ⟨0, by simpa [Formula.iterSub] using (ProvableMetricQ.ax (Γ := Γ) hax)⟩
    | @hyp θ hmem =>
      rcases (Set.mem_union θ Γ {ψ}).mp hmem with hΓ | hsing
      · exact ⟨0, by simpa [Formula.iterSub] using ProvableMetricQ.hyp hΓ⟩
      · have hθeq : θ = ψ := by simpa [Set.mem_singleton_iff] using hsing
        exact ⟨1, by
          simpa [hθeq, Formula.iterSub] using
            (ProvableMetricQ.of_provableQ (ProvableQ.imp_refl (Γ := Γ) θ))⟩
    | @mp α β _hα _himp ihα ihimp =>
      obtain ⟨n, hn⟩ := ihα
      obtain ⟨m, hm⟩ := ihimp
      have hsch := ProvableMetricQ.of_provableQ
        (ProvableQ.deduction_schema (Γ := Γ) β α ψ m n)
      have hstep : ProvableMetricQ Γ
          (.tsub (Formula.iterSub β ψ (m + n)) (Formula.iterSub (.tsub β α) ψ m)) :=
        ProvableMetricQ.mp hn (by simpa [Nat.add_comm] using hsch)
      exact ⟨m + n, ProvableMetricQ.mp hm hstep⟩
  · rintro ⟨n, hn⟩
    exact ProvableMetricQ.cancel_iterSub
      (.hyp (Set.mem_union_right _ (Set.mem_singleton _))) n
      (hn.mono (by intro θ hθ; exact Set.mem_union_left _ hθ))

end ContinuousFOL
