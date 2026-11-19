/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 consistency via 1; vision.md page 16–17
Hilbert steps follow Rose–Rosser, Fragments of many-valued statement calculi (1958), §2–§3.
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.Group2Axioms.BaseAxiomSchema
public import ContinuousFOL.Group2Axioms.FormulaGenList
public import ContinuousFOL.LanguageAndSemantics.FormulaOne

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Empty-generalization axiom instance. -/
lemma ProvableQ.ax0 {L : Signature} {Γ : Set (Formula L)} {ψ : Formula L}
    (h : BaseAxiomSchema ψ) : ProvableQ Γ ψ :=
  .ax (xs := []) h

/-- Łukasiewicz implication `φ → ψ` as `ψ ∸ φ` (0 = true). -/
abbrev Imp {L : Signature} (φ ψ : Formula L) : Formula L := .tsub ψ φ

/-- Łukasiewicz disjunction `φ ∨ ψ` as `(φ → ψ) → ψ`. -/
abbrev OrF {L : Signature} (φ ψ : Formula L) : Formula L := Imp (Imp φ ψ) ψ

/-- From `⊢ φ` and `⊢ φ → ψ` get `⊢ ψ`. -/
lemma ProvableQ.imp_mp {L : Signature} {Γ : Set (Formula L)} {φ ψ : Formula L}
    (hφ : ProvableQ Γ φ) (himp : ProvableQ Γ (Imp φ ψ)) : ProvableQ Γ ψ :=
  ProvableQ.mp hφ himp

/-- Syllogism (Rose–Rosser 2.1): A2 is `(φ → ψ) → ((ψ → χ) → (φ → χ))`. -/
lemma ProvableQ.imp_trans {L : Signature} {Γ : Set (Formula L)} {φ ψ χ : Formula L}
    (hab : ProvableQ Γ (Imp φ ψ)) (hbc : ProvableQ Γ (Imp ψ χ)) :
    ProvableQ Γ (Imp φ χ) :=
  ProvableQ.imp_mp hbc (ProvableQ.imp_mp hab (ProvableQ.ax0 (.A2 φ ψ χ)))

/-- Rose–Rosser (2.4): `⊢ φ → (ψ ∨ φ)`. -/
lemma ProvableQ.imp_or_swap {L : Signature} {Γ : Set (Formula L)} (φ ψ : Formula L) :
    ProvableQ Γ (Imp φ (OrF ψ φ)) :=
  ProvableQ.ax0 (.A1 φ (Imp ψ φ))

/-- Rose–Rosser (2.5): `⊢ φ → (φ ∨ ψ)`. -/
lemma ProvableQ.imp_or {L : Signature} {Γ : Set (Formula L)} (φ ψ : Formula L) :
    ProvableQ Γ (Imp φ (OrF φ ψ)) :=
  ProvableQ.imp_trans (ProvableQ.imp_or_swap (Γ := Γ) φ ψ)
    (ProvableQ.ax0 (.A3 ψ φ))

/-- Rose–Rosser (2.6): `⊢ (φ → (ψ → χ)) → (ψ → (φ → χ))`. -/
lemma ProvableQ.imp_perm_schema {L : Signature} {Γ : Set (Formula L)} (φ ψ χ : Formula L) :
    ProvableQ Γ (Imp (Imp φ (Imp ψ χ)) (Imp ψ (Imp φ χ))) := by
  -- Y: (φ → (ψ → χ)) → ((ψ ∨ χ) → (φ → χ))
  have y : ProvableQ Γ (Imp (Imp φ (Imp ψ χ)) (Imp (OrF ψ χ) (Imp φ χ))) :=
    ProvableQ.ax0 (.A2 φ (Imp ψ χ) χ)
  -- X: ((ψ ∨ χ) → (φ → χ)) → (ψ → (φ → χ))
  have x : ProvableQ Γ (Imp (Imp (OrF ψ χ) (Imp φ χ)) (Imp ψ (Imp φ χ))) :=
    ProvableQ.imp_mp (ProvableQ.imp_or (Γ := Γ) ψ χ)
      (ProvableQ.ax0 (.A2 ψ (OrF ψ χ) (Imp φ χ)))
  exact ProvableQ.imp_trans y x

/-- Permute antecedents: from `⊢ φ → (ψ → χ)` get `⊢ ψ → (φ → χ)`. -/
lemma ProvableQ.imp_perm {L : Signature} {Γ : Set (Formula L)} {φ ψ χ : Formula L}
    (h : ProvableQ Γ (Imp φ (Imp ψ χ))) : ProvableQ Γ (Imp ψ (Imp φ χ)) :=
  ProvableQ.imp_mp h (ProvableQ.imp_perm_schema (Γ := Γ) φ ψ χ)

/-- Rose–Rosser (2.10): `⊢ φ → φ`. -/
lemma ProvableQ.imp_refl {L : Signature} {Γ : Set (Formula L)} (φ : Formula L) :
    ProvableQ Γ (Imp φ φ) := by
  -- (φ → (ψ → φ)) → (ψ → (φ → φ)); discharge antecedent by A1; ψ any theorem.
  let ψ : Formula L := Imp φ (Imp φ φ)
  have hweak : ProvableQ Γ (Imp ψ (Imp φ φ)) :=
    ProvableQ.imp_mp (ProvableQ.ax0 (.A1 φ ψ))
      (ProvableQ.imp_perm_schema (Γ := Γ) φ ψ φ)
  exact ProvableQ.imp_mp (ProvableQ.ax0 (.A1 φ φ)) hweak

/-- `⊢ ¬φ → (φ → ψ)` (Łukasiewicz ex-falso seed). -/
lemma ProvableQ.not_imp_imp {L : Signature} {Γ : Set (Formula L)} (φ ψ : Formula L) :
    ProvableQ Γ (Imp (.neg φ) (Imp φ ψ)) :=
  ProvableQ.imp_trans
    (ProvableQ.ax0 (.A1 (.neg φ) (.neg ψ)))
    (ProvableQ.ax0 (.A4 ψ φ))

/-- `⊢ φ ∸ 1`, i.e. `⊢ 1 → φ`. -/
lemma ProvableQ.tsub_one {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) :
    ProvableQ Γ (Formula.tsub φ (Formula.one L)) := by
  -- 1 = ¬(α → α); get ¬(α→α) → ((α→α) → φ), permute, MP with identity.
  let α : Formula L := Formula.defaultAtom L
  let idα : Formula L := Imp α α
  have hseed : ProvableQ Γ (Imp (.neg idα) (Imp idα φ)) :=
    ProvableQ.not_imp_imp (Γ := Γ) idα φ
  have hperm : ProvableQ Γ (Imp idα (Imp (.neg idα) φ)) :=
    ProvableQ.imp_perm hseed
  have hid : ProvableQ Γ idα := ProvableQ.imp_refl (Γ := Γ) α
  have h : ProvableQ Γ (Imp (.neg idα) φ) := ProvableQ.imp_mp hid hperm
  simpa [Formula.one, Imp, idα, α] using h

/-- Consistency criterion via `1`: `Γ` is inconsistent iff `Γ ⊢_Q 1`. -/
lemma inconsistent_iff_provable_one {L : Signature} (Γ : Set (Formula L)) :
    ¬ ConsistentQ Γ ↔ ProvableQ Γ (Formula.one L) := by
  constructor
  · intro h
    have : ∀ φ : Formula L, ProvableQ Γ φ := fun φ =>
      Classical.byContradiction fun hφ => h ⟨φ, hφ⟩
    exact this (Formula.one L)
  · intro h1
    refine not_exists.mpr fun φ hφ => hφ ?_
    exact ProvableQ.imp_mp h1 (ProvableQ.tsub_one Γ φ)

end ContinuousFOL
