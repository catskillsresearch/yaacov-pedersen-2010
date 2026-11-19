/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Theorem 9.4; vision.md page 21–23
-/
module

public import ContinuousFOL.Completeness.ExistsHenkinExtension
public import ContinuousFOL.Completeness.TermPreStructureEvalEqSup
public import ContinuousFOL.Essentials.MaximalConsistent
public import ContinuousFOL.LanguageAndSemantics.ModelsPre
public import ContinuousFOL.Group1Axioms.DyadicCode.Zero

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Theorem 9.4: Every consistent `Γ` extends to a maximal consistent Henkin complete `Δ`
    satisfied by a term pre-structure `(𝔐, σ) ⊨_Q Δ`. -/
theorem henkin_model_existence {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) :
    ∃ (Lc : Signature) (ext : SignatureExtension L Lc) (Δ : Set (Formula Lc))
      (M : PreStructure Lc) (σ : Var → M.Carrier),
      MaximalConsistent Δ ∧ HenkinComplete Δ ∧
      (ext.mapFormula '' Γ) ⊆ Δ ∧ ModelsPre M σ Δ := by
  obtain ⟨Lc, ext, Γc, hhenk, hcons_ext⟩ := exists_henkin_extension L
  obtain ⟨Δ, hsub, hmc⟩ := exists_maximal_consistent (hcons_ext Γ hcons)
  have hhenkΔ : HenkinComplete Δ := by
    intro φ x p q hpq
    obtain ⟨c, hc, hmem⟩ := hhenk Γ φ x p q hpq
    exact ⟨c, hc, hsub hmem⟩
  refine ⟨Lc, ext, Δ, termPreStructure Δ, idTermAssign Lc, hmc, hhenkΔ, ?_, ?_⟩
  · exact Set.Subset.trans Set.subset_union_left hsub
  · intro φ hφ
    rw [termPreStructure_eval_eq_sup hmc hhenkΔ φ, maximal_consistent_sup_eq_inf hmc φ]
    have h0 : Formula.tsub φ (Formula.dyadic Lc .zero) ∈ Δ := by
      sorry
    have hnonneg : ∀ r ∈ {r : ℝ | ∃ q : DyadicCode, r = q.val ∧
        Formula.tsub φ (Formula.dyadic Lc q) ∈ Δ}, 0 ≤ r := by
      rintro _ ⟨q, rfl, _⟩; exact (q.val_mem_Icc).1
    apply le_antisymm
    · exact le_trans (csInf_le ⟨0, hnonneg⟩ ⟨.zero, DyadicCode.val_zero.symm, h0⟩) (by simp)
    · exact le_csInf ⟨0, .zero, DyadicCode.val_zero.symm, h0⟩ hnonneg

end ContinuousFOL
