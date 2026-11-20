/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: algebraic half of Fact 4.1 (Chang 1958). The Lindenbaum algebra of
Łukasiewicz formulae relative to a premise set `Γ` is the quotient by provable
equivalence over `Γ`. It is an MV-algebra, and its zero class is exactly the
formulae provable from `Γ`: `mk φ = 0 ↔ Γ ⊢ φ`.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormDeduction
public import ContinuousFOL.LukasiewiczAndContinuous.StandardMVAlgebra
public import Mathlib.Order.Setoid.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

/-- Provable equivalence over `Γ`: `φ ≡ ψ` iff `Γ ⊢ φ → ψ` and `Γ ⊢ ψ → φ`. -/
def ProvableEq {ι : Type*} (Γ : Set (LukPropForm ι)) (φ ψ : LukPropForm ι) : Prop :=
  Provable Γ (Imp φ ψ) ∧ Provable Γ (Imp ψ φ)

section Hilbert

variable {ι : Type*} {Γ : Set (LukPropForm ι)}

lemma ProvableEq.refl (φ : LukPropForm ι) : ProvableEq Γ φ φ :=
  ⟨imp_refl φ, imp_refl φ⟩

lemma ProvableEq.symm {φ ψ : LukPropForm ι}
    (h : ProvableEq Γ φ ψ) : ProvableEq Γ ψ φ :=
  ⟨h.2, h.1⟩

lemma ProvableEq.trans {φ ψ χ : LukPropForm ι}
    (h₁ : ProvableEq Γ φ ψ) (h₂ : ProvableEq Γ ψ χ) : ProvableEq Γ φ χ :=
  ⟨imp_trans h₁.1 h₂.1, imp_trans h₂.2 h₁.2⟩

lemma ProvableEq.equivalence : Equivalence (ProvableEq Γ) :=
  ⟨ProvableEq.refl, ProvableEq.symm, ProvableEq.trans⟩

/-- Any two formulae provable from `Γ` are provably equivalent, by weakening (A1). -/
lemma ProvableEq.of_provable {φ ψ : LukPropForm ι}
    (hφ : Provable Γ φ) (hψ : Provable Γ ψ) : ProvableEq Γ φ ψ := by
  refine ⟨?_, ?_⟩
  · exact imp_mp hψ (ax0 (.A1 ψ φ))
  · exact imp_mp hφ (ax0 (.A1 φ ψ))

lemma ProvableEq.of_left_theorem {φ ψ : LukPropForm ι}
    (hφ : Provable Γ φ) (h : ProvableEq Γ φ ψ) : Provable Γ ψ :=
  imp_mp hφ h.1

/-- Identity: `⊢ φ ∸ φ`. -/
lemma provable_tsub_self (φ : LukPropForm ι) :
    Provable Γ (φ.tsub φ) :=
  imp_refl φ

/-- A parameterized form of `mk φ = 0 ↔ Γ ⊢ φ`, using `ψ ∸ ψ` as a tautological zero. -/
lemma ProvableEq.iff_provable {φ ψ : LukPropForm ι} :
    ProvableEq Γ φ (ψ.tsub ψ) ↔ Provable Γ φ := by
  constructor
  · intro h
    exact ProvableEq.of_left_theorem (provable_tsub_self ψ) h.symm
  · intro hφ
    exact ProvableEq.of_provable hφ (provable_tsub_self ψ)

/-- Right-antitonicity of `∸`, from (A2): `(α → β) → ((φ ∸ β) → (φ ∸ α))`. -/
lemma imp_tsub_right (φ α β : LukPropForm ι) :
    Provable Γ (Imp (Imp α β) (Imp (φ.tsub β) (φ.tsub α))) :=
  ax0 (.A2 α β φ)

/-- (A4) itself, in implication form: `(¬φ → ¬ψ) → (ψ → φ)`.
    (Because `Imp α β = β ∸ α`, the paper's `(φ ∸ ψ) ∸ (¬ψ ∸ ¬φ)` is this converse
    contraposition, not `(φ → ψ) → (¬ψ → ¬φ)`.) -/
lemma imp_contrapose_conv (φ ψ : LukPropForm ι) :
    Provable Γ (Imp (Imp (.neg φ) (.neg ψ)) (Imp ψ φ)) :=
  ax0 (.A4 φ ψ)

/-- `⊢ ¬φ → (φ → ψ)` (Łukasiewicz ex-falso seed). -/
lemma not_imp_imp (φ ψ : LukPropForm ι) :
    Provable Γ (Imp (.neg φ) (Imp φ ψ)) :=
  imp_trans (ax0 (.A1 (.neg φ) (.neg ψ))) (ax0 (.A4 ψ φ))

/-- From (A2) and ex-falso: `((φ → ψ) → χ) → (¬φ → χ)`. -/
lemma imp_neg_ante (φ ψ χ : LukPropForm ι) :
    Provable Γ (Imp (Imp (Imp φ ψ) χ) (Imp (.neg φ) χ)) :=
  imp_mp (not_imp_imp (Γ := Γ) φ ψ) (ax0 (.A2 (.neg φ) (Imp φ ψ) χ))

/-- From permutation and (A4): `ψ → ((¬φ → ¬ψ) → φ)`. -/
lemma imp_contrapose_ante (φ ψ : LukPropForm ι) :
    Provable Γ (Imp ψ (Imp (Imp (.neg φ) (.neg ψ)) φ)) :=
  imp_mp (imp_contrapose_conv (Γ := Γ) φ ψ)
    (imp_perm_schema (Imp (.neg φ) (.neg ψ)) ψ φ)

/-- Double-negation elimination: `⊢ ¬¬φ → φ`. -/
lemma dn_elim (φ : LukPropForm ι) :
    Provable Γ (Imp (.neg (.neg φ)) φ) := by
  -- Any (A1) instance can play the role of `ψ` in `imp_contrapose_ante`.
  let weak : LukPropForm ι := Imp φ (Imp φ φ)
  have hseed : Provable Γ (Imp (Imp (.neg φ) (.neg weak)) φ) :=
    imp_mp (ax0 (.A1 φ φ)) (imp_contrapose_ante (Γ := Γ) φ weak)
  exact imp_mp hseed (imp_neg_ante (Γ := Γ) (.neg φ) (.neg weak) φ)

/-- Double-negation introduction: `⊢ φ → ¬¬φ`. -/
lemma dn_intro (φ : LukPropForm ι) :
    Provable Γ (Imp φ (.neg (.neg φ))) :=
  imp_mp (dn_elim (Γ := Γ) (.neg φ)) (imp_contrapose_conv (.neg (.neg φ)) φ)

lemma ProvableEq.neg_neg (φ : LukPropForm ι) :
    ProvableEq Γ (.neg (.neg φ)) φ :=
  ⟨dn_elim φ, dn_intro φ⟩

/-- Direct contraposition: `(φ → ψ) → (¬ψ → ¬φ)`. -/
lemma imp_contrapose (φ ψ : LukPropForm ι) :
    Provable Γ (Imp (Imp φ ψ) (Imp (.neg ψ) (.neg φ))) := by
  -- From `φ → ψ` and DN, get `¬¬φ → ¬¬ψ`, then (A4) yields `¬ψ → ¬φ`.
  have h : Provable Γ
      (Imp (Imp (.neg (.neg φ)) (.neg (.neg ψ))) (Imp (.neg ψ) (.neg φ))) :=
    imp_contrapose_conv (Γ := Γ) (.neg φ) (.neg ψ)
  have h₁ : Provable Γ (Imp (Imp φ ψ) (Imp (Imp (.neg (.neg φ)) φ) (Imp (.neg (.neg φ)) ψ))) :=
    imp_suffix φ ψ (.neg (.neg φ))
  have h₂ : Provable Γ (Imp (Imp φ ψ) (Imp (.neg (.neg φ)) ψ)) :=
    imp_mp (dn_elim (Γ := Γ) φ) (imp_perm h₁)
  have h₃ : Provable Γ
      (Imp (Imp (.neg (.neg φ)) ψ) (Imp (.neg (.neg φ)) (.neg (.neg ψ)))) :=
    imp_mp (dn_intro (Γ := Γ) ψ) (imp_suffix ψ (.neg (.neg ψ)) (.neg (.neg φ)))
  exact imp_trans (imp_trans h₂ h₃) h

lemma ProvableEq.neg_congr {φ ψ : LukPropForm ι}
    (h : ProvableEq Γ φ ψ) : ProvableEq Γ (.neg φ) (.neg ψ) :=
  ⟨imp_mp h.2 (imp_contrapose ψ φ), imp_mp h.1 (imp_contrapose φ ψ)⟩

lemma ProvableEq.tsub_congr_left {φ φ' α : LukPropForm ι}
    (h : ProvableEq Γ φ φ') : ProvableEq Γ (φ.tsub α) (φ'.tsub α) :=
  ⟨imp_mp h.1 (imp_tsub_left φ φ' α), imp_mp h.2 (imp_tsub_left φ' φ α)⟩

lemma ProvableEq.tsub_congr_right {φ α α' : LukPropForm ι}
    (h : ProvableEq Γ α α') : ProvableEq Γ (φ.tsub α) (φ.tsub α') :=
  ⟨imp_mp h.2 (imp_tsub_right φ α' α), imp_mp h.1 (imp_tsub_right φ α α')⟩

lemma ProvableEq.tsub_congr {φ φ' α α' : LukPropForm ι}
    (hφ : ProvableEq Γ φ φ') (hα : ProvableEq Γ α α') :
    ProvableEq Γ (φ.tsub α) (φ'.tsub α') :=
  (hφ.tsub_congr_left).trans (hα.tsub_congr_right)

lemma ProvableEq.imp_congr {α α' β β' : LukPropForm ι}
    (hα : ProvableEq Γ α α') (hβ : ProvableEq Γ β β') :
    ProvableEq Γ (Imp α β) (Imp α' β') :=
  hβ.tsub_congr hα

/-- Subtracting a theorem does nothing: if `Γ ⊢ α` then `β ∸ α ≡ β`. -/
lemma ProvableEq.tsub_of_theorem {β α : LukPropForm ι}
    (hα : Provable Γ α) : ProvableEq Γ (β.tsub α) β := by
  refine ⟨?_, ?_⟩
  · exact imp_mp hα (imp_or α β)
  · exact ax0 (.A1 β α)

/-- Every formula implies a theorem: `⊢ φ → (ψ ∸ ψ)`. -/
lemma imp_theorem (φ ψ : LukPropForm ι) :
    Provable Γ (Imp φ (ψ.tsub ψ)) :=
  imp_mp (imp_refl ψ) (ax0 (.A1 (ψ.tsub ψ) φ))

/-- Contraposition as an equivalence: `(¬p → ¬q) ≡ (q → p)`. -/
lemma ProvableEq.contra (p q : LukPropForm ι) :
    ProvableEq Γ (Imp (.neg p) (.neg q)) (Imp q p) :=
  ⟨imp_contrapose_conv p q, imp_contrapose q p⟩

lemma imp_swap_neg (a b : LukPropForm ι) :
    Provable Γ (Imp (Imp a (.neg b)) (Imp b (.neg a))) :=
  imp_trans (imp_contrapose a (.neg b))
    (ProvableEq.tsub_congr_right (φ := .neg a) (ProvableEq.neg_neg (Γ := Γ) b)).1

/-- `(a → ¬b) ≡ (b → ¬a)`. -/
lemma ProvableEq.swap_neg (a b : LukPropForm ι) :
    ProvableEq Γ (Imp a (.neg b)) (Imp b (.neg a)) :=
  ⟨imp_swap_neg a b, imp_swap_neg b a⟩

/-- Permutation of antecedents as an equivalence. -/
lemma ProvableEq.perm (a b c : LukPropForm ι) :
    ProvableEq Γ (Imp a (Imp b c)) (Imp b (Imp a c)) :=
  ⟨imp_perm_schema a b c, imp_perm_schema b a c⟩

/-- (A3) as an equivalence: `a ∨ b ≡ b ∨ a`. -/
lemma ProvableEq.orF_comm (a b : LukPropForm ι) :
    ProvableEq Γ (OrF a b) (OrF b a) :=
  ⟨ax0 (.A3 a b), ax0 (.A3 b a)⟩

end Hilbert

def provableEqSetoid {ι : Type*} (Γ : Set (LukPropForm ι)) : Setoid (LukPropForm ι) where
  r := ProvableEq Γ
  iseqv := ProvableEq.equivalence

/-- MV-addition at the formula level: `φ ⊕ ψ := ¬(ψ → ¬φ) = ¬(¬φ ∸ ψ)`. -/
def mvadd {ι : Type*} (φ ψ : LukPropForm ι) : LukPropForm ι :=
  LukPropForm.neg ((LukPropForm.neg φ).tsub ψ)

section MV

variable {ι : Type*} {Γ : Set (LukPropForm ι)}

lemma ProvableEq.mvadd_congr {φ φ' ψ ψ' : LukPropForm ι}
    (hφ : ProvableEq Γ φ φ') (hψ : ProvableEq Γ ψ ψ') :
    ProvableEq Γ (mvadd φ ψ) (mvadd φ' ψ') := by
  simpa [mvadd] using (hφ.neg_congr.tsub_congr hψ).neg_congr

/-- `φ ⊕ 0 ≡ φ`, where `0` is any theorem. -/
lemma ProvableEq.mvadd_tsub_self (φ ψ : LukPropForm ι) :
    ProvableEq Γ (mvadd φ (ψ.tsub ψ)) φ := by
  simpa [mvadd] using
    ((ProvableEq.tsub_of_theorem (β := LukPropForm.neg φ) (provable_tsub_self (Γ := Γ) ψ)).neg_congr).trans
      (ProvableEq.neg_neg φ)

/-- `φ ⊕ 1 ≡ 1`, where `1 = ¬0` and `0` is any theorem. -/
lemma ProvableEq.mvadd_neg_tsub_self (φ ψ : LukPropForm ι) :
    ProvableEq Γ (mvadd φ (LukPropForm.neg (ψ.tsub ψ))) (LukPropForm.neg (ψ.tsub ψ)) := by
  have h : Provable Γ ((LukPropForm.neg φ).tsub (LukPropForm.neg (ψ.tsub ψ))) :=
    imp_mp (imp_theorem φ ψ) (imp_contrapose φ (ψ.tsub ψ))
  simpa [mvadd] using
    (ProvableEq.of_provable h (provable_tsub_self ψ)).neg_congr

/-- (MV2) at the formula level. -/
lemma ProvableEq.mvadd_comm (φ ψ : LukPropForm ι) :
    ProvableEq Γ (mvadd φ ψ) (mvadd ψ φ) := by
  simpa [mvadd] using (ProvableEq.swap_neg (Γ := Γ) ψ φ).neg_congr

/-- (MV1) at the formula level. -/
lemma ProvableEq.mvadd_assoc (x y z : LukPropForm ι) :
    ProvableEq Γ (mvadd x (mvadd y z)) (mvadd (mvadd x y) z) := by
  -- Both sides are `¬(z → (y → ¬x))` up to provable equivalence.
  have hL : ProvableEq Γ (Imp (mvadd y z) (.neg x)) (Imp z (Imp y (.neg x))) := by
    have h₁ : ProvableEq Γ (Imp (mvadd y z) (.neg x)) (Imp x (Imp z (.neg y))) :=
      ProvableEq.contra (Imp z (.neg y)) x
    have h₂ : ProvableEq Γ (Imp x (Imp z (.neg y))) (Imp z (Imp x (.neg y))) :=
      ProvableEq.perm x z (.neg y)
    have h₃ : ProvableEq Γ (Imp z (Imp x (.neg y))) (Imp z (Imp y (.neg x))) :=
      ProvableEq.imp_congr (ProvableEq.refl z) (ProvableEq.swap_neg x y)
    exact h₁.trans (h₂.trans h₃)
  have hR : ProvableEq Γ (Imp z (.neg (mvadd x y))) (Imp z (Imp y (.neg x))) :=
    ProvableEq.imp_congr (ProvableEq.refl z) (ProvableEq.neg_neg (Imp y (.neg x)))
  have h := (hL.trans hR.symm).neg_congr
  simpa [mvadd] using h

/-- `¬(¬x ⊕ y) ≡ y → x`. -/
lemma ProvableEq.neg_mvadd_neg (x y : LukPropForm ι) :
    ProvableEq Γ (.neg (mvadd (.neg x) y)) (Imp y x) := by
  have h : ProvableEq Γ (mvadd (.neg x) y) (.neg (Imp y x)) := by
    simpa [mvadd] using
      (ProvableEq.imp_congr (ProvableEq.refl y) (ProvableEq.neg_neg (Γ := Γ) x)).neg_congr
  exact h.neg_congr.trans (ProvableEq.neg_neg _)

/-- `(y → x) ⊕ y ≡ ¬(¬x ∨ ¬y)`, the lattice join written with `OrF` (which is `min`). -/
lemma ProvableEq.mvadd_imp_self (x y : LukPropForm ι) :
    ProvableEq Γ (mvadd (Imp y x) y) (.neg (OrF (.neg x) (.neg y))) := by
  have h₁ : ProvableEq Γ (Imp y (.neg (Imp y x))) (Imp (Imp y x) (.neg y)) :=
    ProvableEq.swap_neg y (Imp y x)
  have h₂ : ProvableEq Γ (Imp (Imp y x) (.neg y)) (OrF (.neg x) (.neg y)) :=
    ProvableEq.imp_congr (ProvableEq.contra x y).symm (ProvableEq.refl _)
  simpa [mvadd] using (h₁.trans h₂).neg_congr

/-- (MV6) at the formula level. -/
lemma ProvableEq.mvadd_absorp (x y : LukPropForm ι) :
    ProvableEq Γ (mvadd (.neg (mvadd (.neg x) y)) y)
      (mvadd (.neg (mvadd (.neg y) x)) x) := by
  have hL := (ProvableEq.mvadd_congr (ProvableEq.neg_mvadd_neg (Γ := Γ) x y)
    (ProvableEq.refl y)).trans (ProvableEq.mvadd_imp_self x y)
  have hR := (ProvableEq.mvadd_congr (ProvableEq.neg_mvadd_neg (Γ := Γ) y x)
    (ProvableEq.refl x)).trans (ProvableEq.mvadd_imp_self y x)
  exact hL.trans ((ProvableEq.orF_comm _ _).neg_congr.trans hR.symm)

/-- `φ ∸ ψ ≡ ¬(¬φ ⊕ ψ)`: truncated subtraction is MV-subtraction. -/
lemma ProvableEq.tsub_eq_msub (φ ψ : LukPropForm ι) :
    ProvableEq Γ (φ.tsub ψ) (.neg (mvadd (.neg φ) ψ)) :=
  (ProvableEq.neg_mvadd_neg φ ψ).symm

end MV

end LukPropForm

open LukPropForm

/-- The Lindenbaum algebra of Łukasiewicz formulae over `ι`, relative to premises `Γ`. -/
abbrev LukLindT {ι : Type*} (Γ : Set (LukPropForm ι)) :=
  Quotient (LukPropForm.provableEqSetoid Γ)

/-- The Lindenbaum algebra of Łukasiewicz formulae over the variable type `ι`
    (no premises). -/
abbrev LukLind (ι : Type*) :=
  LukLindT (∅ : Set (LukPropForm ι))

namespace LukLind

variable {ι : Type*} {Γ : Set (LukPropForm ι)}

def mk (φ : LukPropForm ι) : LukLindT Γ :=
  Quotient.mk _ φ

lemma mk_eq_iff {φ ψ : LukPropForm ι} :
    (mk φ : LukLindT Γ) = mk ψ ↔ ProvableEq Γ φ ψ :=
  Quotient.eq

/-- Every formula provable from `Γ` represents the same class. -/
lemma mk_eq_of_provable {φ ψ : LukPropForm ι}
    (hφ : Provable Γ φ) (hψ : Provable Γ ψ) : (mk φ : LukLindT Γ) = mk ψ :=
  (mk_eq_iff).2 (ProvableEq.of_provable hφ hψ)

lemma mk_tsub_self (φ ψ : LukPropForm ι) :
    (mk (φ.tsub φ) : LukLindT Γ) = mk (ψ.tsub ψ) :=
  mk_eq_of_provable (provable_tsub_self φ) (provable_tsub_self ψ)

/-- `mk φ` is the class of theorems iff `Γ ⊢ φ`. -/
theorem mk_eq_id_iff (φ ψ : LukPropForm ι) :
    (mk φ : LukLindT Γ) = mk (ψ.tsub ψ) ↔ Provable Γ φ := by
  rw [mk_eq_iff]
  exact ProvableEq.iff_provable

def neg : LukLindT Γ → LukLindT Γ :=
  Quotient.lift (fun φ => mk (LukPropForm.neg φ)) fun _φ _ψ h =>
    (mk_eq_iff).2 (ProvableEq.neg_congr h)

def add : LukLindT Γ → LukLindT Γ → LukLindT Γ :=
  Quotient.lift₂ (fun φ ψ => mk (mvadd φ ψ)) fun _φ _ψ _φ' _ψ' hφ hψ =>
    (mk_eq_iff).2 (ProvableEq.mvadd_congr hφ hψ)

lemma neg_mk (φ : LukPropForm ι) : neg (mk φ : LukLindT Γ) = mk (LukPropForm.neg φ) :=
  rfl

lemma add_mk (φ ψ : LukPropForm ι) :
    add (mk φ : LukLindT Γ) (mk ψ) = mk (mvadd φ ψ) :=
  rfl

@[elab_as_elim]
lemma ind {motive : LukLindT Γ → Prop} (h : ∀ φ, motive (mk φ)) (x : LukLindT Γ) : motive x :=
  Quotient.inductionOn x h

lemma neg_neg (x : LukLindT Γ) : neg (neg x) = x := by
  induction x using ind with | h φ => ?_
  rw [neg_mk, neg_mk]
  exact (mk_eq_iff).2 (ProvableEq.neg_neg φ)

lemma add_comm (x y : LukLindT Γ) : add x y = add y x := by
  induction x using ind with | h φ => ?_
  induction y using ind with | h ψ => ?_
  rw [add_mk, add_mk]
  exact (mk_eq_iff).2 (ProvableEq.mvadd_comm φ ψ)

lemma add_assoc (x y z : LukLindT Γ) : add x (add y z) = add (add x y) z := by
  induction x using ind with | h φ => ?_
  induction y using ind with | h ψ => ?_
  induction z using ind with | h χ => ?_
  rw [add_mk, add_mk, add_mk, add_mk]
  exact (mk_eq_iff).2 (ProvableEq.mvadd_assoc φ ψ χ)

lemma add_absorp (x y : LukLindT Γ) :
    add (neg (add (neg x) y)) y = add (neg (add (neg y) x)) x := by
  induction x using ind with | h φ => ?_
  induction y using ind with | h ψ => ?_
  simp only [neg_mk, add_mk]
  exact (mk_eq_iff).2 (ProvableEq.mvadd_absorp φ ψ)

variable [Inhabited (LukPropForm ι)]

/-- Zero is the class of theorems. The representative is `default ∸ default`. -/
instance : Zero (LukLindT Γ) :=
  ⟨mk ((default : LukPropForm ι).tsub default)⟩

lemma zero_def : (0 : LukLindT Γ) = mk ((default : LukPropForm ι).tsub default) :=
  rfl

lemma zero_eq_mk_tsub_self (φ : LukPropForm ι) :
    (0 : LukLindT Γ) = mk (φ.tsub φ) := by
  rw [zero_def]
  exact mk_tsub_self (default : LukPropForm ι) φ

/-- The defining property of the Lindenbaum zero: `mk φ = 0` if and only if `Γ ⊢ φ`. -/
theorem mk_eq_zero_iff (φ : LukPropForm ι) :
    (mk φ : LukLindT Γ) = 0 ↔ Provable Γ φ := by
  rw [zero_eq_mk_tsub_self φ]
  exact mk_eq_id_iff φ φ

lemma add_zero (x : LukLindT Γ) : add x 0 = x := by
  induction x using ind with | h φ => ?_
  rw [zero_def, add_mk]
  exact (mk_eq_iff).2 (ProvableEq.mvadd_tsub_self φ (default : LukPropForm ι))

lemma add_neg_zero (x : LukLindT Γ) : add x (neg 0) = neg 0 := by
  induction x using ind with | h φ => ?_
  rw [zero_def, neg_mk, add_mk]
  exact (mk_eq_iff).2 (ProvableEq.mvadd_neg_tsub_self φ (default : LukPropForm ι))

/-- The Lindenbaum algebra is an MV-algebra (Chang's axioms (MV1)–(MV6)). -/
instance instMVAlgebra : MVAlgebra (LukLindT Γ) where
  add := add
  neg := neg
  zero := 0
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  neg_neg := neg_neg
  add_neg_zero := add_neg_zero
  add_absorp := add_absorp

lemma mv_zero_eq : (MVAlgebra.zero : LukLindT Γ) = 0 := rfl

lemma msub_mk (φ ψ : LukPropForm ι) :
    MVAlgebra.msub (mk φ : LukLindT Γ) (mk ψ) = mk (φ.tsub ψ) :=
  ((mk_eq_iff).2 (ProvableEq.tsub_eq_msub φ ψ)).symm

/-- Evaluating a formula in its own Lindenbaum algebra, at the canonical assignment
    `i ↦ [var i]`, returns its class. -/
lemma evalMV_mk (φ : LukPropForm ι) :
    evalMV (A := LukLindT Γ) (fun i => mk (.var i)) φ = mk φ := by
  induction φ with
  | var i => rfl
  | tsub φ ψ ihφ ihψ =>
    simp only [evalMV, ihφ, ihψ]
    exact msub_mk φ ψ
  | neg φ ih =>
    simp only [evalMV, ih]
    rfl

/-- `Γ ⊢ φ` iff `φ` evaluates to `0` at the canonical assignment of the Lindenbaum
    algebra of `Γ`. -/
theorem provable_iff_evalMV_canonical (φ : LukPropForm ι) :
    Provable Γ φ ↔ evalMV (A := LukLindT Γ) (fun i => mk (.var i)) φ = 0 := by
  rw [evalMV_mk, mk_eq_zero_iff]

end LukLind

end ContinuousFOL
