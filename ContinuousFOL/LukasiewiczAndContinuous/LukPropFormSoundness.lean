/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 soundness of Łukasiewicz propositional logic; vision.md page 5
-/
module

public import ContinuousFOL.Group1Axioms.LukPropForm.Provable
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormModels

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

lemma axiom_eval_zero {I : Type*} {φ : LukPropForm I} (h : IsAxiom φ)
    (v₀ : I → ℝ) (hv : ∀ i, 0 ≤ v₀ i ∧ v₀ i ≤ 1) :
    eval v₀ φ = 0 := by
  cases h with
  | A1 φ ψ =>
    have hx := (eval_mem_Icc v₀ hv φ).1
    have hy := (eval_mem_Icc v₀ hv ψ).1
    simp only [eval]
    exact (tsubR.eq_zero_iff _ _).mpr (tsubR.tsub_le_self hx hy)
  | A2 φ ψ χ =>
    simp only [eval]
    exact (tsubR.eq_zero_iff _ _).mpr
      (tsubR.tsub_tsub_le (eval v₀ φ) (eval v₀ ψ) (eval v₀ χ))
  | A3 φ ψ =>
    have hφ := eval_mem_Icc v₀ hv φ
    have hψ := eval_mem_Icc v₀ hv ψ
    simp only [eval]
    have hmin :
        eval v₀ φ ∸ (eval v₀ φ ∸ eval v₀ ψ) =
          eval v₀ ψ ∸ (eval v₀ ψ ∸ eval v₀ φ) := by
      rw [tsubR.tsub_tsub_eq_min hφ.1 hψ.1, tsubR.tsub_tsub_eq_min hψ.1 hφ.1, min_comm]
    exact (tsubR.eq_zero_iff _ _).mpr (le_of_eq hmin)
  | A4 φ ψ =>
    simp only [eval]
    rw [tsubR.neg_congr (eval v₀ φ) (eval v₀ ψ)]
    exact (tsubR.eq_zero_iff _ _).mpr le_rfl

/-- Soundness: if `Σ ⊢^L φ`, then `Σ ⊨^L φ`. This is the easy half of Fact 4.1
    (and of Fact 4.2, once consistency is related to unprovability of `1`). -/
lemma soundness {I : Type*} {hypSet : Set (LukPropForm I)} {goal : LukPropForm I}
    (h : Provable hypSet goal) : Entails hypSet goal := by
  induction h with
  | ax hax =>
    intro v₀ hv
    exact axiom_eval_zero hax v₀ hv.1
  | hyp hmem =>
    intro v₀ hv
    exact hv.2 _ hmem
  | mp hφ himp ihφ ihimp =>
    rename_i φ ψ
    intro v₀ hv
    have hφ0 := ihφ v₀ hv
    have himp0 := ihimp v₀ hv
    have hle : eval v₀ ψ ≤ eval v₀ φ :=
      (tsubR.eq_zero_iff _ _).mp (by simp [eval] at himp0 ⊢; exact himp0)
    have hnonneg := (eval_mem_Icc v₀ hv.1 ψ).1
    exact le_antisymm (hle.trans (le_of_eq hφ0)) hnonneg


end LukPropForm

end ContinuousFOL
