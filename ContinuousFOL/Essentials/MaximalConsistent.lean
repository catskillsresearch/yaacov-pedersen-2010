/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Definition 8.8 / Lemmas 8.6, 8.11–8.12 / Theorem 8.10; vision.md pages 18–20
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.LanguageAndSemantics.FormulaRank
public import ContinuousFOL.LanguageAndSemantics.FormulaEquiv
public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeSubst
public import ContinuousFOL.Essentials.ConsistentAdjoin
public import ContinuousFOL.Essentials.InconsistentIffProvableOne
public import ContinuousFOL.Essentials.ProvableQMono
public import ContinuousFOL.Group1Axioms.DyadicCode.Val
public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Basic
public import Mathlib.Order.Zorn

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Definition 8.8: Maximal consistent set of formulae in continuous first-order logic. -/
structure MaximalConsistent {L : Signature} (Δ : Set (Formula L)) : Prop where
  consistent : ConsistentQ Δ
  archimedean : ∀ φ, (∀ n : ℕ, ProvableQ Δ (.tsub φ (Formula.pow2Neg L n))) → φ ∈ Δ
  comparable  : ∀ φ ψ, Formula.tsub φ ψ ∈ Δ ∨ Formula.tsub ψ φ ∈ Δ

namespace MaximalConsistent

/-- Remark 8.9: Deductive closure of maximal consistent sets. -/
lemma mem_iff_provable {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (φ : Formula L) :
    φ ∈ Δ ↔ ProvableQ Δ φ := by
  sorry

end MaximalConsistent

/-- Lemma 8.11: Instantiation inside maximal consistent sets after bound renaming. -/
theorem maximal_consistent_sup_instantiate {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (t : Term L) (x : Var) (φ : Formula L) (p : DyadicCode)
    (hmem : Formula.tsub (.sup x φ) (Formula.dyadic L p) ∈ Δ) :
    ∃ φ' : Formula L, (φ ≡ᶠ φ') ∧ φ'.rank = φ.rank ∧
      Formula.FreeSubstCorrect φ' t x ∧
      Formula.tsub (φ'.freeSubst t x) (Formula.dyadic L p) ∈ Δ := by
  sorry

/-- Lemma 8.12: Dedekind cut equality of dyadic lower and upper bounds in `Δ`. -/
theorem maximal_consistent_sup_eq_inf {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (φ : Formula L) :
    sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ Formula.tsub (Formula.dyadic L p) φ ∈ Δ} =
    sInf {r : ℝ | ∃ q : DyadicCode, r = q.val ∧ Formula.tsub φ (Formula.dyadic L q) ∈ Δ} := by
  sorry

/-- Lemma 8.6: Maximal elements of `E(Γ)` coincide with `MaximalConsistent`. -/
theorem maximal_in_consistent_extensions_iff {L : Signature} {Γ Δ : Set (Formula L)}
    (hΓ : ConsistentQ Γ) :
    Maximal (fun Γ' => Γ ⊆ Γ' ∧ ConsistentQ Γ') Δ ↔ (Γ ⊆ Δ ∧ MaximalConsistent Δ) := by
  constructor
  · rintro ⟨⟨hsub, hcons⟩, hmax⟩
    refine ⟨hsub, ⟨hcons, ?_, ?_⟩⟩
    · intro φ happrox
      have hcons' := consistent_adjoin_approx hcons φ happrox
      have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hcons'⟩ Set.subset_union_left
      exact heq (Set.mem_union_right _ (Set.mem_singleton φ))
    · intro φ ψ
      rcases consistent_adjoin_comparable hcons φ ψ with hc₁ | hc₂
      · left
        have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hc₁⟩ Set.subset_union_left
        exact heq (Set.mem_union_right _ (Set.mem_singleton _))
      · right
        have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hc₂⟩ Set.subset_union_left
        exact heq (Set.mem_union_right _ (Set.mem_singleton _))
  · rintro ⟨hsub, hmc⟩
    refine ⟨⟨hsub, hmc.consistent⟩, ?_⟩
    rintro Γ' ⟨hΓ'sub, hΓ'cons⟩ hΔΓ' φ hφ
    apply hmc.archimedean
    intro n
    sorry

/-- Theorem 8.10: Lindenbaum's Lemma via Zorn's Lemma. -/
theorem exists_maximal_consistent {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) :
    ∃ Δ : Set (Formula L), Γ ⊆ Δ ∧ MaximalConsistent Δ := by
  let E : Set (Set (Formula L)) := {Γ' | Γ ⊆ Γ' ∧ ConsistentQ Γ'}
  have hchain : ∀ c ⊆ E, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ E, ∀ s ∈ c, s ⊆ ub := by
    intro c hcE hch ⟨s₀, hs₀⟩
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · exact Set.Subset.trans (hcE hs₀).1 (Set.subset_sUnion_of_mem hs₀)
    · rw [← not_iff_not, inconsistent_iff_provable_one]
      intro hprov
      obtain ⟨Γ₀, hΓ₀sub, hΓ₀prov⟩ := hprov.compact
      have hmem_s₀ : (s₀ : Set (Formula L)) ∈ c := hs₀
      have hdir : DirectedOn (· ⊆ ·) c := hch.directedOn
      have hex : ∃ t ∈ c, (↑Γ₀ : Set (Formula L)) ⊆ t := by
        induction Γ₀ using Finset.induction with
        | empty => exact ⟨s₀, hs₀, Set.empty_subset _⟩
        | @insert ψ S _ ih =>
          obtain ⟨t₁, ht₁c, ht₁sub⟩ := ih
          have hψ : ψ ∈ ⋃₀ c := hΓ₀sub (by simp)
          obtain ⟨t₂, ht₂c, hψt₂⟩ := Set.mem_sUnion.mp hψ
          obtain ⟨t₃, ht₃c, h₁₃, h₂₃⟩ := hdir t₁ ht₁c t₂ ht₂c
          refine ⟨t₃, ht₃c, ?_⟩
          rw [Finset.coe_insert]
          exact Set.insert_subset (h₂₃ hψt₂) (Set.Subset.trans ht₁sub h₁₃)
      obtain ⟨t, htc, htsub⟩ := hex
      have ht_incons : ¬ ConsistentQ t := by
        rw [inconsistent_iff_provable_one]
        exact hΓ₀prov.mono htsub
      exact ht_incons (hcE htc).2
  have hΓE : Γ ∈ E := ⟨Set.Subset.rfl, hcons⟩
  obtain ⟨Δ, hΓΔ, hmax⟩ := zorn_subset_nonempty E hchain Γ hΓE
  exact ⟨Δ, (maximal_in_consistent_extensions_iff hcons).mp hmax⟩

end ContinuousFOL
