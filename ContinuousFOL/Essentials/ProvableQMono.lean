/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 finiteness of proofs; vision.md page 16
-/
module

public import ContinuousFOL.Group2Axioms.ProvableQ
public import Mathlib.Data.Finset.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Monotonicity and finiteness of `ProvableQ`. -/
lemma ProvableQ.mono {L : Signature} {Γ Γ' : Set (Formula L)} (hsub : Γ ⊆ Γ')
    {φ : Formula L} (h : ProvableQ Γ φ) : ProvableQ Γ' φ := by
  induction h with
  | ax hax => exact .ax hax
  | hyp hmem => exact .hyp (hsub hmem)
  | mp h₁ h₂ ih₁ ih₂ => exact .mp ih₁ ih₂

lemma ProvableQ.compact {L : Signature} {Γ : Set (Formula L)} :
    ∀ {φ : Formula L}, ProvableQ Γ φ →
      ∃ Γ₀ : Finset (Formula L), (↑Γ₀ : Set (Formula L)) ⊆ Γ ∧ ProvableQ (↑Γ₀) φ := by
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

end ContinuousFOL
