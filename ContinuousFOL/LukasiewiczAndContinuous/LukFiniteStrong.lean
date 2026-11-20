/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §4, finite strong completeness for Łukasiewicz logic, from Fact 4.1
(`LukPropForm.entails_empty_iff_provable`), the weak deduction theorem and
semantic iteration. Induction on the finite premise set: `Σ ∪ {ψ} ⊨ φ` gives
`Σ ⊨ φ ∸ nψ`, hence `Σ ⊢ φ ∸ nψ`, hence `Σ ∪ {ψ} ⊢ φ`.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukChang
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormSemanticIteration
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormDeduction

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

/-- Finite strong completeness for Łukasiewicz logic: `Σ ⊨ φ → Σ ⊢ φ`, `Σ` finite. -/
theorem provable_of_entails_finset {I : Type*} (hypSet : Finset (LukPropForm I)) :
    ∀ φ : LukPropForm I, Entails (↑hypSet : Set (LukPropForm I)) φ →
      Provable (↑hypSet : Set (LukPropForm I)) φ := by
  induction hypSet using Finset.induction_on with
  | empty =>
    intro φ h
    rw [Finset.coe_empty] at h ⊢
    exact provable_of_entails_empty φ h
  | insert ψ Γ₀ _ ih =>
    intro φ h
    rw [Finset.coe_insert, Set.insert_eq, Set.union_comm] at h ⊢
    obtain ⟨n, hn⟩ := semantic_iteration Γ₀ φ ψ h
    exact (deduction_theorem (↑Γ₀) φ ψ).mpr ⟨n, ih _ hn⟩

end LukPropForm

end ContinuousFOL
