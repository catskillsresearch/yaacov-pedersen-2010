/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §4 Facts 4.2–4.4. Compactness of `[0, 1]^I` (Tychonoff) makes
satisfiability finitary. With finite strong completeness (from Facts 4.1 and
4.5) this gives consistency ↔ satisfiability for both propositional logics, when
there is at least one propositional variable, and approximated strong
completeness for continuous logic (Fact 4.4).

Note: with no propositional variables (`I` empty) there are no formulas at all,
so the empty premise set is satisfiable but not consistent
(`∃ φ, ¬ Σ ⊢ φ` fails). The official statements of Facts 4.2 and 4.3 quantify
over every `I`, so they fail at `I = Empty`; see
`LukPropForm.consistent_iff_satisfiable_fails_empty` and
`CLPropForm.consistent_iff_satisfiable_fails_empty`.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.CLFromLuk
public import ContinuousFOL.Group1Axioms.CLPropForm.Dyadic
public import ContinuousFOL.Group1Axioms.DyadicCode.Val
public import ContinuousFOL.LukasiewiczAndContinuous.CLPropFormDeduction
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace PropCompactness

variable {I : Type*}

/-- The cube `[0, 1]^I`. -/
def cube : Set (I → ℝ) := Set.pi Set.univ (fun _ => Set.Icc 0 1)

lemma isCompact_cube : IsCompact (cube : Set (I → ℝ)) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

lemma mem_cube {v : I → ℝ} : v ∈ cube ↔ ∀ i, 0 ≤ v i ∧ v i ≤ 1 :=
  Set.mem_univ_pi

/-- Compactness: continuous conditions `f j = 0` that are finitely satisfiable in
    the cube are jointly satisfiable there. -/
theorem exists_common_zero {J : Type*} (f : J → (I → ℝ) → ℝ) (hf : ∀ j, Continuous (f j))
    (h : ∀ s : Finset J, ∃ v ∈ cube, ∀ j ∈ s, f j v = 0) :
    ∃ v ∈ cube, ∀ j, f j v = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨s, hs⟩ := isCompact_cube.elim_finite_subfamily_closed (fun j => f j ⁻¹' {0})
    (fun j => isClosed_singleton.preimage (hf j)) (by
      rw [Set.disjoint_iff]
      rintro v ⟨hv, hall⟩
      simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff] at hall
      obtain ⟨j, hj⟩ := hne v hv
      exact hj (hall j))
  obtain ⟨v, hv, hvs⟩ := h s
  refine Set.disjoint_iff.mp hs ⟨hv, ?_⟩
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
  exact hvs

lemma continuous_tsubR {X : Type*} [TopologicalSpace X] {f g : X → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ∸ g x := by
  simp only [tsubR]
  exact (hf.sub hg).max continuous_const

end PropCompactness

open PropCompactness

/-! ### Łukasiewicz logic -/

namespace LukPropForm

variable {I : Type*}

lemma continuous_eval (φ : LukPropForm I) : Continuous fun v : I → ℝ => eval v φ := by
  induction φ with
  | var i => exact continuous_apply i
  | tsub φ ψ ihφ ihψ => exact continuous_tsubR ihφ ihψ
  | neg φ ih => exact continuous_const.sub ih

/-- Compactness: a premise set is satisfiable if all its finite subsets are. -/
theorem satisfiable_of_finite (Γ : Set (LukPropForm I))
    (h : ∀ Γ₀ : Finset (LukPropForm I), (↑Γ₀ : Set (LukPropForm I)) ⊆ Γ → Satisfiable (↑Γ₀ : Set (LukPropForm I))) :
    Satisfiable Γ := by
  obtain ⟨v, hv, hall⟩ := exists_common_zero (J := Γ) (fun j v => eval v j.1)
    (fun j => continuous_eval j.1) (by
      intro s
      obtain ⟨v, hv⟩ := h (s.image Subtype.val) (by
        intro x hx
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
        exact j.2)
      exact ⟨v, mem_cube.mpr hv.1, fun j hj =>
        hv.2 _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hj))⟩)
  exact ⟨v, mem_cube.mp hv, fun φ hφ => hall ⟨φ, hφ⟩⟩

/-- Fact 4.2, consistent ⇒ satisfiable (any `I`). -/
theorem satisfiable_of_consistent (Γ : Set (LukPropForm I)) (h : Consistent Γ) :
    Satisfiable Γ := by
  by_contra hs
  have : ∃ Γ₀ : Finset (LukPropForm I), (↑Γ₀ : Set (LukPropForm I)) ⊆ Γ ∧
      ¬ Satisfiable (↑Γ₀ : Set (LukPropForm I)) := by
    by_contra h'
    push Not at h'
    exact hs (satisfiable_of_finite Γ h')
  obtain ⟨Γ₀, hsub, hns⟩ := this
  obtain ⟨φ, hφ⟩ := h
  exact hφ (mono hsub (provable_of_entails_finset Γ₀ φ (fun v hv => absurd ⟨v, hv⟩ hns)))

/-- Fact 4.2, satisfiable ⇒ consistent, when there is a propositional variable. -/
theorem consistent_of_satisfiable [Nonempty I] (Γ : Set (LukPropForm I))
    (h : Satisfiable Γ) : Consistent Γ := by
  obtain ⟨v, hv⟩ := h
  let i : I := Classical.arbitrary I
  refine ⟨.neg (.tsub (.var i) (.var i)), fun hp => ?_⟩
  have := soundness hp v hv
  simp [eval, tsubR] at this

/-- Fact 4.2 when `I` is nonempty. -/
theorem consistent_iff_satisfiable [Nonempty I] (Γ : Set (LukPropForm I)) :
    Consistent Γ ↔ Satisfiable Γ :=
  ⟨satisfiable_of_consistent Γ, consistent_of_satisfiable Γ⟩

lemma isEmpty_of_empty (φ : LukPropForm Empty) : False := by
  induction φ with
  | var i => exact i.elim
  | tsub _ _ ih _ => exact ih
  | neg _ ih => exact ih

/-- With no propositional variables, `∅` is satisfiable but not consistent. -/
theorem consistent_iff_satisfiable_fails_empty :
    ¬ (Consistent (∅ : Set (LukPropForm Empty)) ↔ Satisfiable (∅ : Set (LukPropForm Empty))) := by
  intro h
  obtain ⟨φ, -⟩ := h.mpr ⟨fun i => i.elim, fun i => i.elim, fun _ hφ => absurd hφ (Set.notMem_empty _)⟩
  exact isEmpty_of_empty φ

end LukPropForm

/-! ### Continuous propositional logic -/

namespace CLPropForm

variable {I : Type*}

lemma continuous_eval (φ : CLPropForm I) : Continuous fun v : I → ℝ => eval v φ := by
  induction φ with
  | var i => exact continuous_apply i
  | tsub φ ψ ihφ ihψ => exact continuous_tsubR ihφ ihψ
  | neg φ ih => exact continuous_const.sub ih
  | half φ ih => exact ih.div_const 2

theorem satisfiable_of_finite (Γ : Set (CLPropForm I))
    (h : ∀ Γ₀ : Finset (CLPropForm I), (↑Γ₀ : Set (CLPropForm I)) ⊆ Γ → Satisfiable (↑Γ₀ : Set (CLPropForm I))) :
    Satisfiable Γ := by
  obtain ⟨v, hv, hall⟩ := exists_common_zero (J := Γ) (fun j v => eval v j.1)
    (fun j => continuous_eval j.1) (by
      intro s
      obtain ⟨v, hv⟩ := h (s.image Subtype.val) (by
        intro x hx
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
        exact j.2)
      exact ⟨v, mem_cube.mpr hv.1, fun j hj =>
        hv.2 _ (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hj))⟩)
  exact ⟨v, mem_cube.mp hv, fun φ hφ => hall ⟨φ, hφ⟩⟩

/-- Fact 4.3, consistent ⇒ satisfiable (any `I`). -/
theorem satisfiable_of_consistent (Γ : Set (CLPropForm I)) (h : Consistent Γ) :
    Satisfiable Γ := by
  by_contra hs
  have : ∃ Γ₀ : Finset (CLPropForm I), (↑Γ₀ : Set (CLPropForm I)) ⊆ Γ ∧
      ¬ Satisfiable (↑Γ₀ : Set (CLPropForm I)) := by
    by_contra h'
    push Not at h'
    exact hs (satisfiable_of_finite Γ h')
  obtain ⟨Γ₀, hsub, hns⟩ := this
  obtain ⟨φ, hφ⟩ := h
  exact hφ (mono hsub (provable_of_entails_finset Γ₀ φ (fun v hv => absurd ⟨v, hv⟩ hns)))

/-- Fact 4.3, satisfiable ⇒ consistent, when there is a propositional variable. -/
theorem consistent_of_satisfiable [Nonempty I] (Γ : Set (CLPropForm I))
    (h : Satisfiable Γ) : Consistent Γ := by
  obtain ⟨v, hv⟩ := h
  let i : I := Classical.arbitrary I
  refine ⟨.neg (.tsub (.var i) (.var i)), fun hp => ?_⟩
  have := soundness hp v hv
  simp [eval, tsubR] at this

/-- Fact 4.3 when `I` is nonempty. -/
theorem consistent_iff_satisfiable [Nonempty I] (Γ : Set (CLPropForm I)) :
    Consistent Γ ↔ Satisfiable Γ :=
  ⟨satisfiable_of_consistent Γ, consistent_of_satisfiable Γ⟩

lemma isEmpty_of_empty (φ : CLPropForm Empty) : False := by
  induction φ with
  | var i => exact i.elim
  | tsub _ _ ih _ => exact ih
  | neg _ ih => exact ih
  | half _ ih => exact ih

/-- With no propositional variables, `∅` is satisfiable but not consistent. -/
theorem consistent_iff_satisfiable_fails_empty :
    ¬ (Consistent (∅ : Set (CLPropForm Empty)) ↔ Satisfiable (∅ : Set (CLPropForm Empty))) := by
  intro h
  obtain ⟨φ, -⟩ := h.mpr ⟨fun i => i.elim, fun i => i.elim, fun _ hφ => absurd hφ (Set.notMem_empty _)⟩
  exact isEmpty_of_empty φ

lemma eval_dyadic' (v : I → ℝ) (a : CLPropForm I) (d : DyadicCode) :
    eval v (dyadic a d) = d.val := by
  induction d with
  | one => simp [dyadic, one, eval, DyadicCode.val, tsubR]
  | neg d ih => simp only [dyadic, eval, DyadicCode.val, ih]
  | tsub d e ihd ihe => simp only [dyadic, eval, DyadicCode.val, ihd, ihe]
  | half d ih => simp only [dyadic, eval, DyadicCode.val, ih]

lemma pow2Neg_pos (n : ℕ) : 0 < (DyadicCode.pow2Neg n).val := by
  rw [DyadicCode.val_pow2Neg]; positivity

/-- Fact 4.4 (Approximated strong completeness). -/
theorem entails_iff_forall_provable_tsub_pow2Neg (Γ : Set (CLPropForm I)) (φ : CLPropForm I) :
    Entails Γ φ ↔ ∀ n : ℕ, Provable Γ (.tsub φ (dyadic φ (.pow2Neg n))) := by
  constructor
  · intro h n
    set d := dyadic φ (DyadicCode.pow2Neg n) with hd
    have hdv : ∀ v, eval v d = (DyadicCode.pow2Neg n).val := fun v => eval_dyadic' v φ _
    have hpos := pow2Neg_pos n
    -- conditions: the premises, and `d ∸ φ = 0` (i.e. `φ ≥ 2⁻ⁿ`)
    let f : Option Γ → (I → ℝ) → ℝ := fun o v =>
      match o with
      | none => eval v (.tsub d φ)
      | some j => eval v j.1
    have hf : ∀ o, Continuous (f o) := by
      intro o
      cases o with
      | none => exact continuous_eval _
      | some j => exact continuous_eval j.1
    have hfin : ¬ ∀ s : Finset (Option Γ), ∃ v ∈ cube, ∀ o ∈ s, f o v = 0 := by
      intro hall
      obtain ⟨v, hv, hz⟩ := exists_common_zero f hf hall
      have hmod : Models v Γ := ⟨mem_cube.mp hv, fun ψ hψ => hz (some ⟨ψ, hψ⟩)⟩
      have h0 := h v hmod
      have h1 := hz none
      simp only [f, eval, hdv] at h1
      rw [tsubR.eq_zero_iff, h0] at h1
      linarith
    push Not at hfin
    obtain ⟨s, hs⟩ := hfin
    let Γ₀ : Finset (CLPropForm I) := s.eraseNone.image Subtype.val
    have hsub : (↑Γ₀ : Set (CLPropForm I)) ⊆ Γ := by
      intro x hx
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hx)
      exact j.2
    have hent : Entails (↑Γ₀ : Set (CLPropForm I)) (.tsub φ d) := by
      intro v hv
      by_contra hne
      obtain ⟨o, ho, hno⟩ := hs v (mem_cube.mpr hv.1)
      apply hno
      cases o with
      | none =>
        simp only [f, eval, hdv] at hne ⊢
        rw [tsubR.eq_zero_iff] at hne ⊢
        linarith
      | some j =>
        exact hv.2 _ (Finset.mem_coe.mpr
          (Finset.mem_image_of_mem _ (Finset.mem_eraseNone.mpr ho)))
    exact mono hsub (provable_of_entails_finset Γ₀ _ hent)
  · intro h v hv
    have hle : ∀ n : ℕ, eval v φ ≤ (DyadicCode.pow2Neg n).val := by
      intro n
      have := soundness (h n) v hv
      simp only [eval, eval_dyadic'] at this
      exact (tsubR.eq_zero_iff _ _).mp this
    have h0 := (eval_mem_Icc v hv.1 φ).1
    by_contra hne
    have hpos : 0 < eval v φ := lt_of_le_of_ne h0 (Ne.symm hne)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (by norm_num : (2 : ℝ)⁻¹ < 1)
    have := hle n
    rw [DyadicCode.val_pow2Neg, zpow_neg, zpow_natCast, ← inv_pow] at this
    linarith

end CLPropForm

end ContinuousFOL
