/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: algebraic half of Fact 4.1 (Chang 1958). The Lindenbaum algebra of
Łukasiewicz formulae is the quotient by provable equivalence, and the zero
class is exactly the theorems: `mk φ = 0 ↔ ⊢ φ`.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormDeduction
public import Mathlib.Order.Setoid.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

/-- Provable equivalence: `φ ≡ ψ` iff `⊢ φ → ψ` and `⊢ ψ → φ`. -/
def ProvableEq {ι : Type*} (φ ψ : LukPropForm ι) : Prop :=
  Provable ∅ (Imp φ ψ) ∧ Provable ∅ (Imp ψ φ)

lemma ProvableEq.refl {ι : Type*} (φ : LukPropForm ι) : ProvableEq φ φ :=
  ⟨imp_refl (Γ := ∅) φ, imp_refl (Γ := ∅) φ⟩

lemma ProvableEq.symm {ι : Type*} {φ ψ : LukPropForm ι}
    (h : ProvableEq φ ψ) : ProvableEq ψ φ :=
  ⟨h.2, h.1⟩

lemma ProvableEq.trans {ι : Type*} {φ ψ χ : LukPropForm ι}
    (h₁ : ProvableEq φ ψ) (h₂ : ProvableEq ψ χ) : ProvableEq φ χ :=
  ⟨imp_trans h₁.1 h₂.1, imp_trans h₂.2 h₁.2⟩

lemma ProvableEq.equivalence {ι : Type*} : Equivalence (@ProvableEq ι) :=
  ⟨ProvableEq.refl, ProvableEq.symm, ProvableEq.trans⟩

instance provableEqSetoid (ι : Type*) : Setoid (LukPropForm ι) where
  r := ProvableEq
  iseqv := ProvableEq.equivalence

/-- Any two theorems are provably equivalent, by weakening (A1). -/
lemma ProvableEq.of_provable {ι : Type*} {φ ψ : LukPropForm ι}
    (hφ : Provable ∅ φ) (hψ : Provable ∅ ψ) : ProvableEq φ ψ := by
  refine ⟨?_, ?_⟩
  · exact imp_mp hψ (ax0 (.A1 ψ φ))
  · exact imp_mp hφ (ax0 (.A1 φ ψ))

lemma ProvableEq.of_left_theorem {ι : Type*} {φ ψ : LukPropForm ι}
    (hφ : Provable ∅ φ) (h : ProvableEq φ ψ) : Provable ∅ ψ :=
  imp_mp hφ h.1

/-- Identity: `⊢ φ ∸ φ`. -/
lemma provable_tsub_self {ι : Type*} (φ : LukPropForm ι) :
    Provable ∅ (φ.tsub φ) :=
  imp_refl (Γ := ∅) φ

/-- A parameterized form of `mk φ = 0 ↔ ⊢ φ`, using `ψ ∸ ψ` as a tautological zero. -/
lemma ProvableEq.iff_provable {ι : Type*} {φ ψ : LukPropForm ι} :
    ProvableEq φ (ψ.tsub ψ) ↔ Provable ∅ φ := by
  constructor
  · intro h
    exact ProvableEq.of_left_theorem (provable_tsub_self ψ) h.symm
  · intro hφ
    exact ProvableEq.of_provable hφ (provable_tsub_self ψ)

/-- Right-antitonicity of `∸`, from (A2): `(α → β) → ((φ ∸ β) → (φ ∸ α))`. -/
lemma imp_tsub_right {ι : Type*} {Γ : Set (LukPropForm ι)} (φ α β : LukPropForm ι) :
    Provable Γ (Imp (Imp α β) (Imp (φ.tsub β) (φ.tsub α))) :=
  ax0 (.A2 α β φ)

/-- (A4) itself, in implication form: `(¬φ → ¬ψ) → (ψ → φ)`.
    (Because `Imp α β = β ∸ α`, the paper's `(φ ∸ ψ) ∸ (¬ψ ∸ ¬φ)` is this converse
    contraposition, not `(φ → ψ) → (¬ψ → ¬φ)`.) -/
lemma imp_contrapose_conv {ι : Type*} {Γ : Set (LukPropForm ι)} (φ ψ : LukPropForm ι) :
    Provable Γ (Imp (Imp (.neg φ) (.neg ψ)) (Imp ψ φ)) :=
  ax0 (.A4 φ ψ)

/-- `⊢ ¬φ → (φ → ψ)` (Łukasiewicz ex-falso seed). -/
lemma not_imp_imp {ι : Type*} {Γ : Set (LukPropForm ι)} (φ ψ : LukPropForm ι) :
    Provable Γ (Imp (.neg φ) (Imp φ ψ)) :=
  imp_trans (ax0 (.A1 (.neg φ) (.neg ψ))) (ax0 (.A4 ψ φ))

lemma ProvableEq.tsub_congr_left {ι : Type*} {φ φ' α : LukPropForm ι}
    (h : ProvableEq φ φ') : ProvableEq (φ.tsub α) (φ'.tsub α) :=
  ⟨imp_mp h.1 (imp_tsub_left φ φ' α), imp_mp h.2 (imp_tsub_left φ' φ α)⟩

lemma ProvableEq.tsub_congr_right {ι : Type*} {φ α α' : LukPropForm ι}
    (h : ProvableEq α α') : ProvableEq (φ.tsub α) (φ.tsub α') :=
  ⟨imp_mp h.2 (imp_tsub_right φ α' α), imp_mp h.1 (imp_tsub_right φ α α')⟩

lemma ProvableEq.tsub_congr {ι : Type*} {φ φ' α α' : LukPropForm ι}
    (hφ : ProvableEq φ φ') (hα : ProvableEq α α') :
    ProvableEq (φ.tsub α) (φ'.tsub α') :=
  (hφ.tsub_congr_left).trans (hα.tsub_congr_right)

end LukPropForm

open LukPropForm

/-- The Lindenbaum algebra of Łukasiewicz formulae over the variable type `ι`. -/
abbrev LukLind (ι : Type*) :=
  Quotient (LukPropForm.provableEqSetoid ι)

namespace LukLind

def mk {ι : Type*} (φ : LukPropForm ι) : LukLind ι :=
  Quotient.mk _ φ

lemma mk_eq_iff {ι : Type*} {φ ψ : LukPropForm ι} :
    (mk φ : LukLind ι) = mk ψ ↔ ProvableEq φ ψ :=
  Quotient.eq

/-- Every tautology represents the same class. -/
lemma mk_eq_of_provable {ι : Type*} {φ ψ : LukPropForm ι}
    (hφ : Provable ∅ φ) (hψ : Provable ∅ ψ) : (mk φ : LukLind ι) = mk ψ :=
  (mk_eq_iff).2 (ProvableEq.of_provable hφ hψ)

lemma mk_tsub_self {ι : Type*} (φ ψ : LukPropForm ι) :
    (mk (φ.tsub φ) : LukLind ι) = mk (ψ.tsub ψ) :=
  mk_eq_of_provable (provable_tsub_self φ) (provable_tsub_self ψ)

/-- `mk φ` is the class of tautologies iff `⊢ φ`. -/
theorem mk_eq_id_iff {ι : Type*} (φ ψ : LukPropForm ι) :
    mk φ = mk (ψ.tsub ψ) ↔ Provable ∅ φ := by
  rw [mk_eq_iff]
  exact ProvableEq.iff_provable

variable {ι : Type*} [Inhabited (LukPropForm ι)]

/-- Zero is the class of theorems. The representative is `default ∸ default`. -/
instance : Zero (LukLind ι) :=
  ⟨mk ((default : LukPropForm ι).tsub default)⟩

lemma zero_def : (0 : LukLind ι) = mk ((default : LukPropForm ι).tsub default) :=
  rfl

lemma zero_eq_mk_tsub_self (φ : LukPropForm ι) :
    (0 : LukLind ι) = mk (φ.tsub φ) := by
  rw [zero_def]
  exact mk_tsub_self (default : LukPropForm ι) φ

/-- The defining property of the Lindenbaum zero: `mk φ = 0` if and only if `⊢ φ`. -/
theorem mk_eq_zero_iff (φ : LukPropForm ι) :
    (mk φ : LukLind ι) = 0 ↔ Provable ∅ φ := by
  constructor
  · intro h
    have hmk : (mk φ : LukLind ι) = mk ((default : LukPropForm ι).tsub default) := by
      rwa [zero_def] at h
    exact ProvableEq.of_left_theorem (provable_tsub_self (default : LukPropForm ι))
      (mk_eq_iff.mp hmk.symm)
  · intro hφ
    rw [zero_eq_mk_tsub_self φ]
    exact mk_eq_of_provable hφ (provable_tsub_self φ)

end LukLind

end ContinuousFOL
