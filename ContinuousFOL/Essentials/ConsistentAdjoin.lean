/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.5; vision.md page 17
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.Completeness.ProvableTsubOfInconsistentAdjoin

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Lemma 8.5: Closure properties of consistent sets. -/
theorem consistent_adjoin_approx {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) (φ : Formula L)
    (happrox : ∀ n : ℕ, ProvableQ Γ (.tsub φ (Formula.pow2Neg L n))) :
    ConsistentQ (Γ ∪ {φ}) := by
  sorry

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
