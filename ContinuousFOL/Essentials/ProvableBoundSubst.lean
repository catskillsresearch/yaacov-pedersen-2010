/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.3; vision.md page 16–17
-/
module

public import ContinuousFOL.Essentials.GeneralizationTheorem
public import ContinuousFOL.SubstitutionAndCompletions.FormulaBoundSubst
public import ContinuousFOL.SubstitutionAndCompletions.BoundSubstitutionLemma
public import ContinuousFOL.BlackBox.CLFiniteStrongCompleteness
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Empty-Γ generalization. -/
lemma ProvableQ.generalize0 {L : Signature} {φ : Formula L} (x : Var)
    (h : ProvableQ (∅ : Set (Formula L)) φ) :
    ProvableQ ∅ (.sup x φ) :=
  generalization_theorem ∅ φ x (fun _ hmem => False.elim hmem) h

/-- Syllogism on `∸`. -/
lemma ProvableQ.tsub_trans {L : Signature} {Γ : Set (Formula L)} {α β γ : Formula L}
    (hαβ : ProvableQ Γ (.tsub α β)) (hβγ : ProvableQ Γ (.tsub β γ)) :
    ProvableQ Γ (.tsub α γ) :=
  ProvableQ.imp_trans (Γ := Γ) (φ := γ) (ψ := β) (χ := α) hβγ hαβ

/-- Empty-Γ: from `⊢ ψ ∸ φ` get `⊢_sup ψ ∸_sup φ`. -/
lemma ProvableQ.sup_cong0 {L : Signature} (x : Var) {φ ψ : Formula L}
    (h : ProvableQ (∅ : Set (Formula L)) (.tsub ψ φ)) :
    ProvableQ ∅ (.tsub (.sup x ψ) (.sup x φ)) := by
  have hgen := ProvableQ.generalize0 (L := L) x h
  exact ProvableQ.mp hgen (ProvableQ.ax0 (.A7 x φ ψ))

/-- Instantiate a continuous propositional formula by first-order formulae. -/
def CLPropForm.toFormula {I : Type*} {L : Signature} (f : I → Formula L) :
    CLPropForm I → Formula L
  | .var i => f i
  | .tsub φ ψ => .tsub (toFormula f φ) (toFormula f ψ)
  | .neg φ => .neg (toFormula f φ)
  | .half φ => .half (toFormula f φ)

/-- CL-provable formulae instantiate to `⊢_Q` theorems (group 1 ⊆ (A1)–(A6)). -/
lemma CLPropForm.toFormula_provable {I : Type*} {L : Signature} {Γ : Set (Formula L)}
    (f : I → Formula L) {φ : CLPropForm I} (h : CLPropForm.Provable ∅ φ) :
    ProvableQ Γ (φ.toFormula f) := by
  induction h with
  | ax hax =>
    cases hax with
    | A1 φ ψ =>
      simpa [CLPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := Γ) (.A1 (φ.toFormula f) (ψ.toFormula f)))
    | A2 φ ψ χ =>
      simpa [CLPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := Γ) (.A2 (φ.toFormula f) (ψ.toFormula f) (χ.toFormula f)))
    | A3 φ ψ =>
      simpa [CLPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := Γ) (.A3 (φ.toFormula f) (ψ.toFormula f)))
    | A4 φ ψ =>
      simpa [CLPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := Γ) (.A4 (φ.toFormula f) (ψ.toFormula f)))
    | A5 φ =>
      simpa [CLPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := Γ) (.A5 (φ.toFormula f)))
    | A6 φ =>
      simpa [CLPropForm.toFormula] using
        (ProvableQ.ax0 (Γ := Γ) (.A6 (φ.toFormula f)))
  | hyp hmem =>
    simp at hmem
  | mp _ _ ih₁ ih₂ =>
    exact ProvableQ.mp ih₁ ih₂

/-- A CL tautology (`⊨^{CL} φ`) instantiates to a `⊢_Q` theorem, via Fact 4.5 with `Σ = ∅`. -/
lemma CLPropForm.toFormula_provable_of_valid {I : Type*} {L : Signature}
    {Γ : Set (Formula L)} (f : I → Formula L) (φ : CLPropForm I)
    (hv : ∀ v : I → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ 1) → φ.eval v = 0) :
    ProvableQ Γ (φ.toFormula f) := by
  have hent : CLPropForm.Entails ((∅ : Finset (CLPropForm I)) : Set (CLPropForm I)) φ :=
    fun v hv' => hv v hv'.1
  have hprov := (cl_finite_strong_completeness ∅ φ).mp hent
  rw [Finset.coe_empty] at hprov
  exact CLPropForm.toFormula_provable f hprov

/-- CL: `(α → β) → (¬β → ¬α)`. -/
lemma ProvableQ.contraposition_schema {L : Signature} {Γ : Set (Formula L)}
    (α β : Formula L) :
    ProvableQ Γ (.tsub (.tsub (.neg α) (.neg β)) (.tsub β α)) := by
  have h := CLPropForm.toFormula_provable_of_valid (Γ := Γ) ![α, β]
    (.tsub (.tsub (.neg (.var 0)) (.neg (.var 1))) (.tsub (.var 1) (.var 0))) (by
      intro v _
      simp only [CLPropForm.eval, tsubR, max_def]
      split_ifs <;> linarith)
  exact h

lemma ProvableQ.neg_tsub {L : Signature} {Γ : Set (Formula L)} {α β : Formula L}
    (h : ProvableQ Γ (.tsub β α)) :
    ProvableQ Γ (.tsub (.neg α) (.neg β)) :=
  ProvableQ.mp h (ProvableQ.contraposition_schema (Γ := Γ) α β)

/-- CL: `⊢ ½α ∸ α`. -/
lemma ProvableQ.half_le {L : Signature} {Γ : Set (Formula L)} (α : Formula L) :
    ProvableQ Γ (.tsub (.half α) α) := by
  have h := CLPropForm.toFormula_provable_of_valid (Γ := Γ) ![α]
    (.tsub (.half (.var 0)) (.var 0)) (by
      intro v hv
      obtain ⟨h0, _⟩ := hv 0
      simp only [CLPropForm.eval, tsubR, max_def]
      split_ifs <;> linarith)
  exact h

/-- CL: `⊢ (½β ∸ ½α) ∸ ½(β ∸ α)`. -/
lemma ProvableQ.half_tsub_cong {L : Signature} {Γ : Set (Formula L)} (α β : Formula L) :
    ProvableQ Γ (.tsub (.tsub (.half β) (.half α)) (.half (.tsub β α))) := by
  have h := CLPropForm.toFormula_provable_of_valid (Γ := Γ) ![α, β]
    (.tsub (.tsub (.half (.var 1)) (.half (.var 0))) (.half (.tsub (.var 1) (.var 0)))) (by
      intro v _
      simp only [CLPropForm.eval, tsubR, max_def]
      split_ifs <;> linarith)
  exact h

/-- From `⊢ β ∸ α` get `⊢ ½β ∸ ½α`. -/
lemma ProvableQ.half_mono {L : Signature} {Γ : Set (Formula L)} {α β : Formula L}
    (h : ProvableQ Γ (.tsub β α)) :
    ProvableQ Γ (.tsub (.half β) (.half α)) :=
  ProvableQ.mp (ProvableQ.mp h (ProvableQ.half_le (Γ := Γ) (.tsub β α)))
    (ProvableQ.half_tsub_cong (Γ := Γ) α β)

/-- CL: `((((β' ∸ α') ∸ (β ∸ α)) ∸ (β' ∸ β)) ∸ (α ∸ α'))`.
    After MP with `α ∸ α'` and `β' ∸ β`, yields `⊢ (β' ∸ α') ∸ (β ∸ α)`. -/
lemma ProvableQ.tsub_cong_schema {L : Signature} {Γ : Set (Formula L)}
    (α α' β β' : Formula L) :
    ProvableQ Γ
      (.tsub (.tsub (.tsub (.tsub β' α') (.tsub β α)) (.tsub β' β)) (.tsub α α')) := by
  have h := CLPropForm.toFormula_provable_of_valid (Γ := Γ) ![α, α', β, β']
    (.tsub (.tsub (.tsub (.tsub (.var 3) (.var 1)) (.tsub (.var 2) (.var 0)))
      (.tsub (.var 3) (.var 2))) (.tsub (.var 0) (.var 1))) (by
      intro v _
      simp only [CLPropForm.eval, tsubR, max_def]
      split_ifs <;> linarith)
  exact h

/-- `y ∉ allVars φ` ⇒ free-subst of `y` for `x` is correct. -/
lemma Formula.freeSubstCorrect_var_of_not_mem_allVars {L : Signature}
    (φ : Formula L) (x y : Var) (hy : y ∉ φ.allVars) :
    φ.FreeSubstCorrect (.var y) x := by
  induction φ with
  | rel _ _ =>
    simp [Formula.FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    exact ⟨ihα (fun h => hy (Finset.mem_union_left _ h)),
      ihβ (fun h => hy (Finset.mem_union_right _ h))⟩
  | neg α ih =>
    exact ih (by simpa [Formula.allVars] using hy)
  | half α ih =>
    exact ih (by simpa [Formula.allVars] using hy)
  | sup z α ih =>
    unfold Formula.FreeSubstCorrect
    by_cases hz : z = x
    · simp [hz]
    · simp [hz]
      refine ⟨?_, ih (fun h => hy (Finset.mem_insert_of_mem h))⟩
      intro _hx hyvar
      have : z = y := by simpa [Term.vars] using hyvar
      exact hy (by simp [Formula.allVars, this])

lemma Term.subst_of_not_mem_vars {L : Signature} (s t : Term L) (x : Var)
    (hx : x ∉ s.vars) : s.subst t x = s := by
  induction s with
  | var z =>
    have hz : z ≠ x := by rintro rfl; simp [Term.vars] at hx
    simp [Term.subst, hz]
  | func f args ih =>
    simp only [Term.subst]
    congr 1
    funext i
    exact ih i (fun h => hx (by
      simp only [Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, h⟩))

lemma Term.not_mem_vars_subst_var {L : Signature} (s : Term L) {x y : Var} (hyx : y ≠ x) :
    x ∉ (s.subst (.var y) x).vars := by
  induction s with
  | var z =>
    by_cases hz : z = x
    · simp [Term.subst, hz, Term.vars, Ne.symm hyx]
    · simp [Term.subst, hz, Term.vars, Ne.symm hz]
  | func f args ih =>
    simp only [Term.subst, Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and,
      not_exists]
    exact fun i => ih i

lemma Term.subst_var_cancel {L : Signature} (s : Term L) {x y : Var} (hy : y ∉ s.vars) :
    (s.subst (.var y) x).subst (.var x) y = s := by
  induction s with
  | var z =>
    have hzy : z ≠ y := by rintro rfl; simp [Term.vars] at hy
    by_cases hz : z = x
    · subst hz; simp [Term.subst]
    · simp [Term.subst, hz, hzy]
  | func f args ih =>
    simp only [Term.subst]
    congr 1
    funext i
    exact ih i (fun h => hy (by
      simp only [Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, h⟩))

namespace Formula

variable {L : Signature}

lemma freeSubst_of_not_mem_freeVars (φ : Formula L) (t : Term L) (x : Var)
    (hx : x ∉ φ.freeVars) : φ.freeSubst t x = φ := by
  induction φ with
  | rel P args =>
    simp only [freeSubst]
    congr 1
    funext i
    exact Term.subst_of_not_mem_vars _ _ _ (fun h => hx (by
      simp only [freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, h⟩))
  | tsub α β ihα ihβ =>
    simp only [freeVars, Finset.mem_union, not_or] at hx
    simp [freeSubst, ihα hx.1, ihβ hx.2]
  | neg α ih =>
    simp only [freeVars] at hx
    simp [freeSubst, ih hx]
  | half α ih =>
    simp only [freeVars] at hx
    simp [freeSubst, ih hx]
  | sup z α ih =>
    by_cases hz : z = x
    · simp [freeSubst, hz]
    · have hxα : x ∉ α.freeVars := fun h => hx (Finset.mem_erase.mpr ⟨Ne.symm hz, h⟩)
      simp [freeSubst, hz, ih hxα]

lemma not_mem_freeVars_freeSubst_var (φ : Formula L) {x y : Var} (hyx : y ≠ x) :
    x ∉ (φ.freeSubst (.var y) x).freeVars := by
  induction φ with
  | rel P args =>
    simp only [freeSubst, freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and,
      not_exists]
    exact fun i => Term.not_mem_vars_subst_var _ hyx
  | tsub α β ihα ihβ =>
    simp only [freeSubst, freeVars, Finset.mem_union, not_or]
    exact ⟨ihα, ihβ⟩
  | neg α ih => simpa only [freeSubst, freeVars] using ih
  | half α ih => simpa only [freeSubst, freeVars] using ih
  | sup z α ih =>
    by_cases hz : z = x
    · simp [freeSubst, freeVars, hz]
    · simp only [freeSubst, eq_false hz, ↓reduceIte, freeVars, Finset.mem_erase, not_and]
      exact fun _ => ih

lemma freeSubstCorrect_of_not_mem_freeVars (φ : Formula L) (t : Term L) (x : Var)
    (hx : x ∉ φ.freeVars) : φ.FreeSubstCorrect t x := by
  induction φ with
  | rel _ _ => simp [FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    simp only [freeVars, Finset.mem_union, not_or] at hx
    exact ⟨ihα hx.1, ihβ hx.2⟩
  | neg α ih => exact ih (by simpa [freeVars] using hx)
  | half α ih => exact ih (by simpa [freeVars] using hx)
  | sup z α ih =>
    unfold FreeSubstCorrect
    by_cases hz : z = x
    · simp [hz]
    · have hxα : x ∉ α.freeVars := fun h => hx (Finset.mem_erase.mpr ⟨Ne.symm hz, h⟩)
      simp only [eq_false hz, ↓reduceIte]
      exact ⟨fun h => absurd h hxα, ih hxα⟩

lemma freeSubstCorrect_var_of_not_mem_boundVars (φ : Formula L) (z w : Var)
    (hz : z ∉ φ.boundVars) : φ.FreeSubstCorrect (.var z) w := by
  induction φ with
  | rel _ _ => simp [FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    simp only [boundVars, Finset.mem_union, not_or] at hz
    exact ⟨ihα hz.1, ihβ hz.2⟩
  | neg α ih => exact ih (by simpa [boundVars] using hz)
  | half α ih => exact ih (by simpa [boundVars] using hz)
  | sup u α ih =>
    simp only [boundVars, Finset.mem_insert, not_or] at hz
    unfold FreeSubstCorrect
    by_cases hu : u = w
    · simp [hu]
    · simp only [eq_false hu, ↓reduceIte]
      refine ⟨fun _ h => ?_, ih hz.2⟩
      have : u = z := by simpa [Term.vars] using h
      exact hz.1 this.symm

lemma freeSubst_var_cancel (φ : Formula L) {x y : Var} (hxy : x ≠ y)
    (hy : y ∉ φ.freeVars) (hc : φ.FreeSubstCorrect (.var y) x) :
    (φ.freeSubst (.var y) x).freeSubst (.var x) y = φ := by
  induction φ with
  | rel P args =>
    simp only [freeSubst]
    congr 1
    funext i
    exact Term.subst_var_cancel _ (fun h => hy (by
      simp only [freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, h⟩))
  | tsub α β ihα ihβ =>
    simp only [freeVars, Finset.mem_union, not_or] at hy
    obtain ⟨hcα, hcβ⟩ := hc
    simp only [freeSubst, ihα hy.1 hcα, ihβ hy.2 hcβ]
  | neg α ih =>
    simp only [freeSubst, ih (by simpa [freeVars] using hy) hc]
  | half α ih =>
    simp only [freeSubst, ih (by simpa [freeVars] using hy) hc]
  | sup z α ih =>
    by_cases hzx : z = x
    · have hzy : z ≠ y := hzx ▸ hxy
      have hyα : y ∉ α.freeVars := fun h => hy (Finset.mem_erase.mpr ⟨Ne.symm hzy, h⟩)
      have h1 : (Formula.sup z α).freeSubst (.var y) x = .sup z α := by
        simp [freeSubst, hzx]
      rw [h1]
      simp [freeSubst, hzy, freeSubst_of_not_mem_freeVars α _ y hyα]
    · have hc' := hc
      simp only [FreeSubstCorrect, eq_false hzx, ↓reduceIte] at hc'
      by_cases hzy : z = y
      · have hxα : x ∉ α.freeVars := fun h => hc'.1 h (by simp [Term.vars, hzy])
        have h1 : (Formula.sup z α).freeSubst (.var y) x = .sup z α := by
          simp [freeSubst, hzx, freeSubst_of_not_mem_freeVars α _ x hxα]
        rw [h1]
        simp [freeSubst, hzy]
      · have hyα : y ∉ α.freeVars := fun h => hy (Finset.mem_erase.mpr ⟨Ne.symm hzy, h⟩)
        simp [freeSubst, hzx, hzy, ih hyα hc'.2]

lemma not_mem_boundVars_boundSubst (φ : Formula L) {x y : Var} (hyx : y ≠ x) :
    x ∉ (φ.boundSubst y x).boundVars := by
  induction φ with
  | rel _ _ => simp [boundSubst, boundVars]
  | tsub α β ihα ihβ =>
    simp only [boundSubst, boundVars, Finset.mem_union, not_or]
    exact ⟨ihα, ihβ⟩
  | neg α ih => simpa only [boundSubst, boundVars] using ih
  | half α ih => simpa only [boundSubst, boundVars] using ih
  | sup z α ih =>
    by_cases hz : z = x
    · simp only [boundSubst, eq_true hz, ↓reduceIte, boundVars, Formula.boundVars_freeSubst,
        Finset.mem_insert, not_or]
      exact ⟨Ne.symm hyx, ih⟩
    · simp only [boundSubst, eq_false hz, ↓reduceIte, boundVars, Finset.mem_insert, not_or]
      exact ⟨Ne.symm hz, ih⟩

lemma not_mem_freeVars_boundSubst (φ : Formula L) {x y : Var} (hy : y ∉ φ.allVars) :
    y ∉ (φ.boundSubst y x).freeVars := by
  induction φ with
  | rel P args => simpa [boundSubst, freeVars, allVars] using hy
  | tsub α β ihα ihβ =>
    simp only [allVars, Finset.mem_union, not_or] at hy
    simp only [boundSubst, freeVars, Finset.mem_union, not_or]
    exact ⟨ihα hy.1, ihβ hy.2⟩
  | neg α ih => simpa only [boundSubst, freeVars] using ih (by simpa [allVars] using hy)
  | half α ih => simpa only [boundSubst, freeVars] using ih (by simpa [allVars] using hy)
  | sup z α ih =>
    simp only [allVars, Finset.mem_insert, not_or] at hy
    by_cases hz : z = x
    · simp [boundSubst, eq_true hz, ↓reduceIte, freeVars]
    · simp only [boundSubst, eq_false hz, ↓reduceIte, freeVars, Finset.mem_erase, not_and]
      exact fun _ => ih hy.2

lemma boundSubst_freeSubstCorrect (φ : Formula L) {x y : Var} (hy : y ∉ φ.allVars) :
    (φ.boundSubst y x).FreeSubstCorrect (.var y) x := by
  induction φ with
  | rel _ _ => simp [boundSubst, FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    simp only [allVars, Finset.mem_union, not_or] at hy
    simp only [boundSubst, FreeSubstCorrect]
    exact ⟨ihα hy.1, ihβ hy.2⟩
  | neg α ih =>
    simp only [boundSubst, FreeSubstCorrect]
    exact ih (by simpa [allVars] using hy)
  | half α ih =>
    simp only [boundSubst, FreeSubstCorrect]
    exact ih (by simpa [allVars] using hy)
  | sup z α ih =>
    simp only [allVars, Finset.mem_insert, not_or] at hy
    by_cases hz : z = x
    · have hyx : y ≠ x := hz ▸ hy.1
      simp only [boundSubst, eq_true hz, ↓reduceIte]
      unfold FreeSubstCorrect
      simp only [eq_false hyx, ↓reduceIte]
      exact ⟨fun h => absurd h (not_mem_freeVars_freeSubst_var _ hyx),
        freeSubstCorrect_of_not_mem_freeVars _ _ _ (not_mem_freeVars_freeSubst_var _ hyx)⟩
    · simp only [boundSubst, eq_false hz, ↓reduceIte]
      unfold FreeSubstCorrect
      simp only [eq_false hz, ↓reduceIte]
      refine ⟨fun _ h => ?_, ih hy.2⟩
      have : z = y := by simpa [Term.vars] using h
      exact hy.1 this.symm

end Formula

/-- Lemma 8.3, binder-`x` case (paper steps 1–6 via (A8), Gen, (A7), (A9), (A2)). -/
lemma ProvableQ.sup_rename_step {L : Signature} (α α' : Formula L) (x y : Var)
    (hyx : y ≠ x) (hyfree : y ∉ α'.freeVars) (hcorr : α'.FreeSubstCorrect (.var y) x)
    (hxb : x ∉ α'.boundVars)
    (h₁ : ProvableQ (∅ : Set (Formula L)) (.tsub α α'))
    (h₂ : ProvableQ (∅ : Set (Formula L)) (.tsub α' α)) :
    ProvableQ ∅ (.tsub (.sup x α) (.sup y (α'.freeSubst (.var y) x))) ∧
    ProvableQ ∅ (.tsub (.sup y (α'.freeSubst (.var y) x)) (.sup x α)) := by
  have hxβ : x ∉ (α'.freeSubst (.var y) x).freeVars :=
    Formula.not_mem_freeVars_freeSubst_var α' hyx
  constructor
  · have hcancel : (α'.freeSubst (.var y) x).freeSubst (.var x) y = α' :=
      Formula.freeSubst_var_cancel α' (Ne.symm hyx) hyfree hcorr
    have hcorrβ : (α'.freeSubst (.var y) x).FreeSubstCorrect (.var x) y :=
      Formula.freeSubstCorrect_var_of_not_mem_boundVars _ x y
        (by rw [Formula.boundVars_freeSubst]; exact hxb)
    have s1 : ProvableQ (∅ : Set (Formula L))
        (.tsub α' (.sup y (α'.freeSubst (.var y) x))) := by
      have := ProvableQ.ax0 (Γ := (∅ : Set (Formula L)))
        (.A8 y (.var x) (α'.freeSubst (.var y) x) hcorrβ)
      rwa [hcancel] at this
    have s2 := ProvableQ.sup_cong0 x s1
    have s3 : ProvableQ (∅ : Set (Formula L))
        (.tsub (.sup x (.sup y (α'.freeSubst (.var y) x))) (.sup y (α'.freeSubst (.var y) x))) :=
      ProvableQ.ax0 (.A9 x _ (by simp [Formula.freeVars, hxβ]))
    have s4 := ProvableQ.sup_cong0 x h₁
    exact ProvableQ.tsub_trans (ProvableQ.tsub_trans s4 s2) s3
  · have s1 : ProvableQ (∅ : Set (Formula L)) (.tsub (α'.freeSubst (.var y) x) (.sup x α')) :=
      ProvableQ.ax0 (.A8 x (.var y) α' hcorr)
    have s2 := ProvableQ.sup_cong0 y s1
    have s3 : ProvableQ (∅ : Set (Formula L)) (.tsub (.sup y (.sup x α')) (.sup x α')) :=
      ProvableQ.ax0 (.A9 y _ (by simp [Formula.freeVars, hyfree]))
    have s4 := ProvableQ.sup_cong0 x h₂
    exact ProvableQ.tsub_trans (ProvableQ.tsub_trans s2 s3) s4

/-- Lemma 8.3: Provable equivalence of bound variable renaming `φ` and `φ{y/x}`. -/
theorem provable_bound_subst {L : Signature} (φ : Formula L) (x y : Var)
    (hy : y ∉ φ.allVars) :
    ProvableQ ∅ (.tsub φ (φ.boundSubst y x)) ∧
    ProvableQ ∅ (.tsub (φ.boundSubst y x) φ) := by
  induction φ with
  | rel _P _args =>
    simp only [Formula.boundSubst]
    exact ⟨ProvableQ.imp_refl _, ProvableQ.imp_refl _⟩
  | tsub α β ihα ihβ =>
    have hyα : y ∉ α.allVars := fun h => hy (Finset.mem_union_left _ h)
    have hyβ : y ∉ β.allVars := fun h => hy (Finset.mem_union_right _ h)
    obtain ⟨hα₁, hα₂⟩ := ihα hyα
    obtain ⟨hβ₁, hβ₂⟩ := ihβ hyβ
    -- Here `.tsub α β` is the formula `α ∸ β` (not implication order).
    simp only [Formula.boundSubst]
    constructor
    · -- ⊢ (α ∸ β) ∸ (α' ∸ β')
      let α' := α.boundSubst y x
      let β' := β.boundSubst y x
      -- Paper schema with (α_paper,β_paper) := (β',α'):
      have seed := ProvableQ.tsub_cong_schema (Γ := (∅ : Set (Formula L))) β' β α' α
      have step1 : ProvableQ ∅
          (.tsub (.tsub (.tsub α β) (.tsub α' β')) (.tsub α α')) :=
        ProvableQ.mp hβ₂ seed
      exact ProvableQ.mp hα₁ step1
    · -- ⊢ (α' ∸ β') ∸ (α ∸ β)
      let α' := α.boundSubst y x
      let β' := β.boundSubst y x
      have seed := ProvableQ.tsub_cong_schema (Γ := (∅ : Set (Formula L))) β β' α α'
      have step1 : ProvableQ ∅
          (.tsub (.tsub (.tsub α' β') (.tsub α β)) (.tsub α' α)) :=
        ProvableQ.mp hβ₁ seed
      exact ProvableQ.mp hα₂ step1
  | neg α ih =>
    have hyα : y ∉ α.allVars := by simpa [Formula.allVars] using hy
    obtain ⟨h₁, h₂⟩ := ih hyα
    simp only [Formula.boundSubst]
    exact ⟨ProvableQ.neg_tsub h₂, ProvableQ.neg_tsub h₁⟩
  | half α ih =>
    have hyα : y ∉ α.allVars := by simpa [Formula.allVars] using hy
    obtain ⟨h₁, h₂⟩ := ih hyα
    simp only [Formula.boundSubst]
    exact ⟨ProvableQ.half_mono h₁, ProvableQ.half_mono h₂⟩
  | sup z α ih =>
    have hyα : y ∉ α.allVars := fun h => hy (by simp [Formula.allVars, h])
    obtain ⟨h₁, h₂⟩ := ih hyα
    simp only [Formula.boundSubst]
    split_ifs with hz
    · -- Binder `x`: paper steps 1–6 (A8/Gen/A7/A2/A9).
      rw [hz]
      have hyx : y ≠ x := fun h => hy (by simp [Formula.allVars, h, hz])
      exact ProvableQ.sup_rename_step α (α.boundSubst y x) x y hyx
        (Formula.not_mem_freeVars_boundSubst α hyα)
        (Formula.boundSubst_freeSubstCorrect α hyα)
        (Formula.not_mem_boundVars_boundSubst α hyx) h₁ h₂
    · exact ⟨ProvableQ.sup_cong0 z h₁, ProvableQ.sup_cong0 z h₂⟩

end ContinuousFOL
