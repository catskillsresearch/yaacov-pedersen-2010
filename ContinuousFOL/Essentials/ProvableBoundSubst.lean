/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.3; vision.md page 16–17
-/
module

public import ContinuousFOL.Essentials.GeneralizationTheorem
public import ContinuousFOL.SubstitutionAndCompletions.FormulaBoundSubst

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

/-- CL: `(α → β) → (¬β → ¬α)`. -/
lemma ProvableQ.contraposition_schema {L : Signature} {Γ : Set (Formula L)}
    (α β : Formula L) :
    ProvableQ Γ (.tsub (.tsub (.neg α) (.neg β)) (.tsub β α)) := by
  sorry

lemma ProvableQ.neg_tsub {L : Signature} {Γ : Set (Formula L)} {α β : Formula L}
    (h : ProvableQ Γ (.tsub β α)) :
    ProvableQ Γ (.tsub (.neg α) (.neg β)) :=
  ProvableQ.mp h (ProvableQ.contraposition_schema (Γ := Γ) α β)

/-- CL: `⊢ ½α ∸ α`. -/
lemma ProvableQ.half_le {L : Signature} {Γ : Set (Formula L)} (α : Formula L) :
    ProvableQ Γ (.tsub (.half α) α) := by
  sorry

/-- CL: `⊢ (½β ∸ ½α) ∸ ½(β ∸ α)`. -/
lemma ProvableQ.half_tsub_cong {L : Signature} {Γ : Set (Formula L)} (α β : Formula L) :
    ProvableQ Γ (.tsub (.tsub (.half β) (.half α)) (.half (.tsub β α))) := by
  sorry

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
  sorry

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
    · -- Binder `x`: paper steps 1–6 (A8/Gen/A7/A2/A9); remainder pending.
      subst hz
      sorry
    · exact ⟨ProvableQ.sup_cong0 z h₁, ProvableQ.sup_cong0 z h₂⟩

end ContinuousFOL
