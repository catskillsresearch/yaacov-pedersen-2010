/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: the semantic half of the propositional deduction theorem
used for Facts 4.1 and 4.5.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.HasPL
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormDeduction
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormModels
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Lattice.Basic

@[expose] public section

noncomputable section
open Classical
open Set

namespace ContinuousFOL

namespace LukPropForm

variable {I : Type*}

def vars : LukPropForm I → Finset I
  | .var i => {i}
  | .tsub φ ψ => vars φ ∪ vars ψ
  | .neg φ => vars φ

lemma eval_eqOn {v w : I → ℝ} {φ : LukPropForm I}
    (h : Set.EqOn v w (vars φ)) : eval v φ = eval w φ := by
  induction φ with
  | var i =>
    exact h (by simp [vars])
  | tsub φ ψ ihφ ihψ =>
    have hφ : Set.EqOn v w (vars φ) := h.mono (by simp [vars])
    have hψ : Set.EqOn v w (vars ψ) := h.mono (by simp [vars])
    simp [eval, ihφ hφ, ihψ hψ]
  | neg φ ih =>
    exact congrArg (fun r => 1 - r) (ih (h.mono (by simp [vars])))

/-- Extend a cube vector by zero off the listed variables. -/
noncomputable def extendOn (s : Finset I) (x : Fin s.card → ℝ) : I → ℝ :=
  fun i =>
    if h : i ∈ s then
      x ((Fintype.equivFinOfCardEq (Fintype.card_coe s)) ⟨i, h⟩)
    else 0

lemma extendOn_mem_Icc {s : Finset I} {x : Fin s.card → ℝ}
    (hx : x ∈ unitCube s.card) (i : I) :
    0 ≤ extendOn s x i ∧ extendOn s x i ≤ 1 := by
  dsimp [extendOn]
  split_ifs with h
  · exact hx _
  · constructor <;> linarith

def restrictTo (s : Finset I) (v : I → ℝ) : Fin s.card → ℝ :=
  fun j => v ((Fintype.equivFinOfCardEq (Fintype.card_coe s)).symm j)

lemma restrictTo_mem_unitCube {s : Finset I} {v : I → ℝ}
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) : restrictTo s v ∈ unitCube s.card := by
  intro j
  exact hv _

lemma eqOn_extendOn_restrictTo {s : Finset I} (v : I → ℝ) :
    Set.EqOn (extendOn s (restrictTo s v)) v (s : Set I) := by
  intro i hi
  have hi' : i ∈ s := hi
  simp [extendOn, restrictTo, hi']

lemma eval_extendOn_restrictTo {s : Finset I} {φ : LukPropForm I}
    (hvars : vars φ ⊆ s) (v : I → ℝ) :
    eval (extendOn s (restrictTo s v)) φ = eval v φ :=
  eval_eqOn (eqOn_extendOn_restrictTo (s := s) v |>.mono hvars)

lemma hasPL_eval (s : Finset I) (φ : LukPropForm I) (hvars : vars φ ⊆ s) :
    HasPL (fun x => eval (extendOn s x) φ) := by
  induction φ with
  | var i =>
    have hi : i ∈ s := hvars (by simp [vars])
    have hfun :
        (fun x : Fin s.card → ℝ => eval (extendOn s x) (.var i)) =
          fun x => x ((Fintype.equivFinOfCardEq (Fintype.card_coe s)) ⟨i, hi⟩) := by
      funext x
      simp [eval, extendOn, hi]
    rw [hfun]
    exact hasPL_proj _
  | tsub φ ψ ihφ ihψ =>
    have hφ : vars φ ⊆ s := (Finset.union_subset_iff.1 hvars).1
    have hψ : vars ψ ⊆ s := (Finset.union_subset_iff.1 hvars).2
    simpa [eval] using hasPL_tsub (ihφ hφ) (ihψ hψ)
  | neg φ ih =>
    have hφ : vars φ ⊆ s := by simpa [vars] using hvars
    simpa [eval] using hasPL_neg (ih hφ)

/-- Semantic iteration for a finite set of Łukasiewicz premises:
    `Σ ∪ {ψ} ⊨ φ` implies `Σ ⊨ φ ∸ nψ` for some `n`. -/
theorem semantic_iteration (hypSet : Finset (LukPropForm I)) (φ ψ : LukPropForm I)
    (h : Entails (↑hypSet ∪ {ψ}) φ) :
    ∃ n : ℕ, Entails (↑hypSet : Set (LukPropForm I)) (iterSub φ ψ n) := by
  let s : Finset I := hypSet.biUnion vars ∪ vars φ ∪ vars ψ
  have hψs : vars ψ ⊆ s := by
    intro i hi
    simp [s]
    exact Or.inr (Or.inr hi)
  have hφs : vars φ ⊆ s := by
    intro i hi
    simp [s]
    exact Or.inr (Or.inl hi)
  have hhyps : ∀ θ ∈ hypSet, vars θ ⊆ s := by
    intro θ hθ i hi
    simp [s]
    exact Or.inl ⟨θ, hθ, hi⟩
  have hf := hasPL_eval s φ hφs
  have hg := hasPL_eval s ψ hψs
  let hypsFn : List ((Fin s.card → ℝ) → ℝ) :=
    hypSet.toList.map (fun θ x => eval (extendOn s x) θ)
  have hlist : ∀ f ∈ hypsFn, HasPL f := by
    intro f hf
    obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hf
    exact hasPL_eval s θ (hhyps θ (Finset.mem_toList.mp hθ))
  have hg0 : ∀ x ∈ unitCube s.card, 0 ≤ eval (extendOn s x) ψ := by
    intro x hx
    exact (eval_mem_Icc (extendOn s x) (extendOn_mem_Icc hx) ψ).1
  have hvan : ∀ x ∈ unitCube s.card,
      (∀ f ∈ hypsFn, f x = 0) →
        eval (extendOn s x) ψ = 0 → eval (extendOn s x) φ = 0 := by
    intro x hx hθs hψ0
    refine h (extendOn s x) ⟨extendOn_mem_Icc hx, ?_⟩
    intro θ hθ
    rcases (Set.mem_union θ (↑hypSet) {ψ}).mp hθ with hθ | hsing
    · exact hθs (fun z => eval (extendOn s z) θ)
        (List.mem_map.2 ⟨θ, Finset.mem_toList.mpr hθ, rfl⟩)
    · have : θ = ψ := by simpa [Set.mem_singleton_iff] using hsing
      simpa [this] using hψ0
  obtain ⟨n, hn⟩ :=
    semantic_iteration_cube hypsFn (fun x => eval (extendOn s x) φ)
      (fun x => eval (extendOn s x) ψ) hlist hf hg hg0 hvan
  refine ⟨n, ?_⟩
  intro v hv
  have hx : restrictTo s v ∈ unitCube s.card := restrictTo_mem_unitCube hv.1
  have hhyps0 : ∀ f ∈ hypsFn, f (restrictTo s v) = 0 := by
    intro f hf
    obtain ⟨θ, hθ, rfl⟩ := List.mem_map.1 hf
    change eval (extendOn s (restrictTo s v)) θ = 0
    rw [eval_extendOn_restrictTo (hhyps θ (Finset.mem_toList.mp hθ)) v]
    exact hv.2 θ (Finset.mem_toList.mp hθ)
  have := hn (restrictTo s v) hx hhyps0
  have hφeq := eval_extendOn_restrictTo (s := s) (φ := φ) hφs v
  have hψeq := eval_extendOn_restrictTo (s := s) (φ := ψ) hψs v
  have hle : eval v φ ≤ (n : ℝ) * eval v ψ := by
    simpa [hφeq, hψeq] using this
  have h0φ := (eval_mem_Icc v hv.1 φ).1
  have h0ψ := (eval_mem_Icc v hv.1 ψ).1
  have : eval v (iterSub φ ψ n) = iterSubR (eval v φ) (eval v ψ) n :=
    eval_iterSub v φ ψ n
  rw [this, iterSubR_eq h0φ h0ψ n, max_eq_right]
  linarith

end LukPropForm

end ContinuousFOL
