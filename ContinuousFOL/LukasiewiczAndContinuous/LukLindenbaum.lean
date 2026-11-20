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

/-- From (A2) and ex-falso: `((φ → ψ) → χ) → (¬φ → χ)`. -/
lemma imp_neg_ante {ι : Type*} {Γ : Set (LukPropForm ι)} (φ ψ χ : LukPropForm ι) :
    Provable Γ (Imp (Imp (Imp φ ψ) χ) (Imp (.neg φ) χ)) :=
  imp_mp (not_imp_imp (Γ := Γ) φ ψ) (ax0 (.A2 (.neg φ) (Imp φ ψ) χ))

/-- From permutation and (A4): `ψ → ((¬φ → ¬ψ) → φ)`. -/
lemma imp_contrapose_ante {ι : Type*} {Γ : Set (LukPropForm ι)} (φ ψ : LukPropForm ι) :
    Provable Γ (Imp ψ (Imp (Imp (.neg φ) (.neg ψ)) φ)) :=
  imp_mp (imp_contrapose_conv (Γ := Γ) φ ψ)
    (imp_perm_schema (Imp (.neg φ) (.neg ψ)) ψ φ)

/-- Double-negation elimination: `⊢ ¬¬φ → φ`. -/
lemma dn_elim {ι : Type*} {Γ : Set (LukPropForm ι)} (φ : LukPropForm ι) :
    Provable Γ (Imp (.neg (.neg φ)) φ) := by
  -- Any (A1) instance can play the role of `ψ` in `imp_contrapose_ante`.
  let weak : LukPropForm ι := Imp φ (Imp φ φ)
  have hseed : Provable Γ (Imp (Imp (.neg φ) (.neg weak)) φ) :=
    imp_mp (ax0 (.A1 φ φ)) (imp_contrapose_ante (Γ := Γ) φ weak)
  exact imp_mp hseed (imp_neg_ante (Γ := Γ) (.neg φ) (.neg weak) φ)

/-- Double-negation introduction: `⊢ φ → ¬¬φ`. -/
lemma dn_intro {ι : Type*} {Γ : Set (LukPropForm ι)} (φ : LukPropForm ι) :
    Provable Γ (Imp φ (.neg (.neg φ))) :=
  imp_mp (dn_elim (Γ := Γ) (.neg φ)) (imp_contrapose_conv (.neg (.neg φ)) φ)

lemma ProvableEq.neg_neg {ι : Type*} (φ : LukPropForm ι) :
    ProvableEq (.neg (.neg φ)) φ :=
  ⟨dn_elim (Γ := ∅) φ, dn_intro (Γ := ∅) φ⟩

/-- Direct contraposition: `(φ → ψ) → (¬ψ → ¬φ)`. -/
lemma imp_contrapose {ι : Type*} {Γ : Set (LukPropForm ι)} (φ ψ : LukPropForm ι) :
    Provable Γ (Imp (Imp φ ψ) (Imp (.neg ψ) (.neg φ))) := by
  -- From `φ → ψ` and DN, get `¬¬φ → ¬¬ψ`, then (A4) yields `¬ψ → ¬φ`.
  have h : Provable Γ
      (Imp (Imp (.neg (.neg φ)) (.neg (.neg ψ))) (Imp (.neg ψ) (.neg φ))) :=
    imp_contrapose_conv (Γ := Γ) (.neg φ) (.neg ψ)
  -- suffix: (φ → ψ) → ((¬¬φ → φ) → (¬¬φ → ψ)), then to (¬¬φ → ¬¬ψ) via intro.
  have h₁ : Provable Γ (Imp (Imp φ ψ) (Imp (Imp (.neg (.neg φ)) φ) (Imp (.neg (.neg φ)) ψ))) :=
    imp_suffix φ ψ (.neg (.neg φ))
  have h₂ : Provable Γ (Imp (Imp φ ψ) (Imp (.neg (.neg φ)) ψ)) :=
    imp_mp (dn_elim (Γ := Γ) φ) (imp_perm h₁)
  have h₃ : Provable Γ
      (Imp (Imp (.neg (.neg φ)) ψ) (Imp (.neg (.neg φ)) (.neg (.neg ψ)))) :=
    imp_mp (dn_intro (Γ := Γ) ψ) (imp_suffix ψ (.neg (.neg ψ)) (.neg (.neg φ)))
  exact imp_trans (imp_trans h₂ h₃) h

lemma ProvableEq.neg_congr {ι : Type*} {φ ψ : LukPropForm ι}
    (h : ProvableEq φ ψ) : ProvableEq (.neg φ) (.neg ψ) :=
  ⟨imp_mp h.2 (imp_contrapose (Γ := ∅) ψ φ),
    imp_mp h.1 (imp_contrapose (Γ := ∅) φ ψ)⟩

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

/-- Subtracting a theorem does nothing: if `⊢ α` then `β ∸ α ≡ β`. -/
lemma ProvableEq.tsub_of_theorem {ι : Type*} {β α : LukPropForm ι}
    (hα : Provable ∅ α) : ProvableEq (β.tsub α) β := by
  refine ⟨?_, ?_⟩
  · -- `⊢ α → ((β ∸ α) → β)`, from `⊢ α → (α ∨ β)`.
    exact imp_mp hα (imp_or (Γ := ∅) α β)
  · -- `⊢ β → (α → β)` is (A1).
    exact ax0 (.A1 β α)

/-- Every formula implies a theorem: `⊢ φ → (ψ ∸ ψ)`. -/
lemma imp_theorem {ι : Type*} {Γ : Set (LukPropForm ι)} (φ ψ : LukPropForm ι) :
    Provable Γ (Imp φ (ψ.tsub ψ)) :=
  imp_mp (imp_refl (Γ := Γ) ψ) (ax0 (.A1 (ψ.tsub ψ) φ))

/-- MV-addition at the formula level: `φ ⊕ ψ := ¬(ψ → ¬φ) = ¬(¬φ ∸ ψ)`. -/
def mvadd {ι : Type*} (φ ψ : LukPropForm ι) : LukPropForm ι :=
  LukPropForm.neg ((LukPropForm.neg φ).tsub ψ)

lemma ProvableEq.mvadd_congr {ι : Type*} {φ φ' ψ ψ' : LukPropForm ι}
    (hφ : ProvableEq φ φ') (hψ : ProvableEq ψ ψ') :
    ProvableEq (mvadd φ ψ) (mvadd φ' ψ') := by
  simpa [mvadd] using (hφ.neg_congr.tsub_congr hψ).neg_congr

/-- `φ ⊕ 0 ≡ φ`, where `0` is any theorem. -/
lemma ProvableEq.mvadd_tsub_self {ι : Type*} (φ ψ : LukPropForm ι) :
    ProvableEq (mvadd φ (ψ.tsub ψ)) φ := by
  simpa [mvadd] using
    ((ProvableEq.tsub_of_theorem (β := LukPropForm.neg φ) (provable_tsub_self ψ)).neg_congr).trans
      (ProvableEq.neg_neg φ)

/-- `φ ⊕ 1 ≡ 1`, where `1 = ¬0` and `0` is any theorem. -/
lemma ProvableEq.mvadd_neg_tsub_self {ι : Type*} (φ ψ : LukPropForm ι) :
    ProvableEq (mvadd φ (LukPropForm.neg (ψ.tsub ψ))) (LukPropForm.neg (ψ.tsub ψ)) := by
  -- `⊢ φ → 0`, so by contraposition `⊢ ¬0 → ¬φ`, i.e. `⊢ ¬φ ∸ ¬0`.
  have h : Provable ∅ ((LukPropForm.neg φ).tsub (LukPropForm.neg (ψ.tsub ψ))) :=
    imp_mp (imp_theorem (Γ := ∅) φ ψ) (imp_contrapose (Γ := ∅) φ (ψ.tsub ψ))
  simpa [mvadd] using
    (ProvableEq.of_provable h (provable_tsub_self ψ)).neg_congr

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

def neg {ι : Type*} : LukLind ι → LukLind ι :=
  Quotient.lift (fun φ => mk (LukPropForm.neg φ)) fun _φ _ψ h =>
    (mk_eq_iff).2 (ProvableEq.neg_congr h)

def add {ι : Type*} : LukLind ι → LukLind ι → LukLind ι :=
  Quotient.lift₂ (fun φ ψ => mk (mvadd φ ψ)) fun _φ _ψ _φ' _ψ' hφ hψ =>
    (mk_eq_iff).2 (ProvableEq.mvadd_congr hφ hψ)

lemma neg_mk {ι : Type*} (φ : LukPropForm ι) : neg (mk φ) = mk (LukPropForm.neg φ) :=
  rfl

lemma add_mk {ι : Type*} (φ ψ : LukPropForm ι) : add (mk φ) (mk ψ) = mk (mvadd φ ψ) :=
  rfl

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

lemma add_zero (x : LukLind ι) : add x 0 = x := by
  refine Quotient.inductionOn x fun φ => ?_
  change add (mk φ) (mk ((default : LukPropForm ι).tsub default)) = mk φ
  rw [add_mk]
  exact (mk_eq_iff).2 (ProvableEq.mvadd_tsub_self φ (default : LukPropForm ι))

omit [Inhabited (LukPropForm ι)] in
lemma neg_neg (x : LukLind ι) : neg (neg x) = x := by
  refine Quotient.inductionOn x fun φ => ?_
  change neg (neg (mk φ)) = mk φ
  rw [neg_mk, neg_mk]
  exact (mk_eq_iff).2 (ProvableEq.neg_neg φ)

lemma add_neg_zero (x : LukLind ι) : add x (neg 0) = neg 0 := by
  refine Quotient.inductionOn x fun φ => ?_
  change add (mk φ) (neg (mk ((default : LukPropForm ι).tsub default))) =
    neg (mk ((default : LukPropForm ι).tsub default))
  rw [neg_mk, add_mk]
  exact (mk_eq_iff).2 (ProvableEq.mvadd_neg_tsub_self φ (default : LukPropForm ι))

end LukLind

end ContinuousFOL
