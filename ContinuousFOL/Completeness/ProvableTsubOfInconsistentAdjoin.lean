/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8/§9 auxiliary for strong completeness; vision.md page 23–24
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.Essentials.DeductionTheorem
public import ContinuousFOL.Essentials.InconsistentIffProvableOne

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

lemma iterSubR_sub_zero {b : ℝ} (hb : 0 ≤ b) (n : ℕ) : iterSubR b 0 n = b := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterSubR, ih, tsubR_zero hb]

/-- `(β ∸ α) ∸ (1 ⊖_n (α ∸ β))` is the zero formula on `[0, 1]`. -/
lemma swap_one_iter_real {a b : ℝ} (ha0 : 0 ≤ a) (_ha1 : a ≤ 1) (_hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (n : ℕ) : (b ∸ a) ∸ iterSubR 1 (a ∸ b) n = 0 := by
  rw [tsubR.eq_zero_iff]
  by_cases h : a ≤ b
  · have hab : a ∸ b = 0 := (tsubR.eq_zero_iff a b).mpr h
    rw [hab, iterSubR_sub_zero zero_le_one]
    have hba1 : b ∸ a ≤ 1 := by
      rw [tsubR.def_eq]
      exact max_le (by linarith) zero_le_one
    exact hba1
  · push Not at h
    have hba : b ∸ a = 0 := (tsubR.eq_zero_iff b a).mpr (le_of_lt h)
    rw [hba, iterSubR_eq zero_le_one (tsubR.nonneg a b)]
    exact le_max_right _ _

namespace LukPropForm

/-- `(β ∸ α) ∸ (1 ⊖_n (α ∸ β))`, with `1 = ¬(δ ∸ δ)`. -/
def swapOneIter (n : ℕ) : LukPropForm (Fin 3) :=
  let α : LukPropForm (Fin 3) := .var 0
  let β : LukPropForm (Fin 3) := .var 1
  let one : LukPropForm (Fin 3) := .neg (.tsub (.var 2) (.var 2))
  .tsub (.tsub β α) (iterSub one (.tsub α β) n)

lemma swapOneIter_entails (n : ℕ) : Entails ∅ (swapOneIter n) := by
  intro v hv
  have ha := hv.1 0
  have hb := hv.1 1
  have hreal := swap_one_iter_real ha.1 ha.2 hb.1 hb.2 n
  simpa [swapOneIter, eval, eval_iterSub] using hreal

lemma swapOneIter_provable (n : ℕ) : Provable ∅ (swapOneIter n) :=
  (luk_weak_completeness (swapOneIter n)).mp (swapOneIter_entails n)

end LukPropForm

lemma ProvableQ.swap_one_iter {L : Signature} (Γ : Set (Formula L))
    (β α : Formula L) (n : ℕ) :
    ProvableQ Γ (.tsub (.tsub β α) (Formula.iterSub (Formula.one L) (.tsub α β) n)) := by
  let f : Fin 3 → Formula L := fun i =>
    if i = 0 then α else if i = 1 then β else Formula.defaultAtom L
  have h0 := LukPropForm.toFormula_provable f (LukPropForm.swapOneIter_provable n)
  have hform :
      (LukPropForm.swapOneIter n).toFormula f =
        .tsub (.tsub β α) (Formula.iterSub (Formula.one L) (.tsub α β) n) := by
    simp only [LukPropForm.swapOneIter, LukPropForm.toFormula, LukPropForm.toFormula_iterSub,
      Formula.one, Formula.defaultAtom, f]
    simp
  rw [hform] at h0
  exact h0.mono (by simp)

/-- Auxiliary lemma (cf. proof of Lemma 8.5): if `Γ ∪ {p ∸ φ}` is inconsistent,
    then `Γ ⊢_Q φ ∸ p`. -/
lemma provable_tsub_of_inconsistent_adjoin {L : Signature} (Γ : Set (Formula L))
    (φ : Formula L) (p : DyadicCode)
    (hincons : ¬ ConsistentQ (Γ ∪ {.tsub (Formula.dyadic L p) φ})) :
    ProvableQ Γ (.tsub φ (Formula.dyadic L p)) := by
  have h1 : ProvableQ (Γ ∪ {.tsub (Formula.dyadic L p) φ}) (Formula.one L) :=
    (inconsistent_iff_provable_one _).mp hincons
  obtain ⟨n, hn⟩ :=
    (deduction_theorem Γ (Formula.one L) (.tsub (Formula.dyadic L p) φ)).mp h1
  exact ProvableQ.mp hn
    (ProvableQ.swap_one_iter Γ φ (Formula.dyadic L p) n)

lemma provable_tsub_of_inconsistent_adjoin_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) (p : DyadicCode)
    (hincons : ¬ ConsistentMetricQ (Γ ∪ {.tsub (Formula.dyadic LM.toSignature p) φ})) :
    ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p)) := by
  -- Metric inconsistency is `¬ ∃ φ, ¬ ProvableMetricQ`, equivalently `⊢ 1`,
  -- by the same ex-falso transport used for `ProvableQ`.
  have hone : ProvableMetricQ (Γ ∪ {.tsub (Formula.dyadic LM.toSignature p) φ})
      (Formula.one LM.toSignature) := by
    classical
    by_contra hnot
    exact hincons ⟨Formula.one LM.toSignature, hnot⟩
  obtain ⟨n, hn⟩ :=
    (deduction_theorem_metric Γ (Formula.one LM.toSignature)
      (.tsub (Formula.dyadic LM.toSignature p) φ)).mp hone
  exact ProvableMetricQ.mp hn
    (ProvableMetricQ.of_provableQ
      (ProvableQ.swap_one_iter Γ φ (Formula.dyadic LM.toSignature p) n))

end ContinuousFOL
