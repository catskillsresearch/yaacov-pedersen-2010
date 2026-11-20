/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: algebraic background for Fact 4.1 (Chang 1959). Evaluation of a
Łukasiewicz formula in the interval `[0, u]` of a linearly ordered abelian group
(Chang's `Γ(G, u)`), and the transfer: if a formula takes a non-zero value there,
it takes a non-zero value under some `[0, 1]`-assignment. The proof records, for
the given point, which branch each truncated subtraction takes. That makes the
formula's value an integer-linear form on the point, cut out by finitely many
integer-linear inequalities, and `LinTransfer.exists_real_solution_fintype` moves
the whole system to `ℝ`.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LinearTransfer
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormSemanticIteration

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

open LinTransfer

section Lin

variable {κ : Type*} [Fintype κ] {M : Type*} [AddCommGroup M]

/-- Integer-linear form `∑ c k • x k`. -/
def lin (c : κ → ℤ) (x : κ → M) : M :=
  ∑ k, c k • x k

lemma lin_sub (c d : κ → ℤ) (x : κ → M) : lin (c - d) x = lin c x - lin d x := by
  simp [lin, sub_smul, Finset.sum_sub_distrib]

lemma lin_zero (x : κ → M) : lin (0 : κ → ℤ) x = 0 := by
  simp [lin]

lemma lin_single [DecidableEq κ] (k₀ : κ) (x : κ → M) : lin (Pi.single k₀ 1) x = x k₀ := by
  simp [lin, Pi.single_apply]

lemma KCon.eval_eq_lin (c : KCon κ) (x : κ → M) : c.eval x = lin c.coef x :=
  rfl

end Lin

section GroupEval

variable {ι : Type*} {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

/-- Evaluation in the interval `[0, u]` of an ordered abelian group (`Γ(G, u)`):
    `φ ∸ ψ ↦ max (φ - ψ) 0` and `¬φ ↦ u - φ`. -/
def evalG (u : G) (a : ι → G) : LukPropForm ι → G
  | .var i => a i
  | .tsub φ ψ => max (evalG u a φ - evalG u a ψ) 0
  | .neg φ => u - evalG u a φ

lemma evalG_mem (u : G) (a : ι → G) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ u) (φ : LukPropForm ι) :
    0 ≤ evalG u a φ ∧ evalG u a φ ≤ u := by
  induction φ with
  | var i => exact ha i
  | tsub φ ψ ihφ ihψ =>
    refine ⟨le_max_right _ _, max_le ?_ (ihφ.1.trans ihφ.2)⟩
    exact (sub_le_self _ ihψ.1).trans ihφ.2
  | neg φ ih => exact ⟨sub_nonneg.mpr ih.2, sub_le_self _ ih.1⟩

variable (u : G) (a : ι → G) (s : Finset ι)

/-- The integer-linear form computing a formula near the point `(u, a)`. Coordinate
    `none` is `u`, coordinate `some i` is `a i`. -/
def lf : LukPropForm ι → (Option s → ℤ)
  | .var i => if h : i ∈ s then Pi.single (some ⟨i, h⟩) 1 else 0
  | .tsub φ ψ => if evalG u a ψ ≤ evalG u a φ then lf φ - lf ψ else 0
  | .neg φ => Pi.single none 1 - lf φ

/-- The branch condition of one truncated subtraction at `(u, a)`. -/
def branchCon (φ ψ : LukPropForm ι) : KCon (Option s) :=
  if evalG u a ψ ≤ evalG u a φ then ⟨lf u a s φ - lf u a s ψ, false⟩
  else ⟨lf u a s ψ - lf u a s φ, true⟩

/-- All branch conditions of a formula at `(u, a)`. -/
def cons : LukPropForm ι → List (KCon (Option s))
  | .var _ => []
  | .tsub φ ψ => branchCon u a s φ ψ :: (cons φ ++ cons ψ)
  | .neg φ => cons φ

/-- The point `(u, a)` as a vector indexed by `Option s`. -/
def pt : Option s → G
  | none => u
  | some k => a k

lemma lin_lf_pt (φ : LukPropForm ι) (hs : vars φ ⊆ s) :
    lin (lf u a s φ) (pt u a s) = evalG u a φ := by
  induction φ with
  | var i =>
    have hi : i ∈ s := hs (by simp [vars])
    simp only [lf, dif_pos hi, lin_single]
    rfl
  | tsub φ ψ ihφ ihψ =>
    have hs' : vars φ ⊆ s ∧ vars ψ ⊆ s := by
      simpa [vars, Finset.union_subset_iff] using hs
    simp only [lf, evalG]
    split_ifs with h
    · rw [lin_sub, ihφ hs'.1, ihψ hs'.2, max_eq_left (sub_nonneg.mpr h)]
    · rw [lin_zero, max_eq_right (sub_nonpos.mpr (le_of_lt (not_le.mp h)))]
  | neg φ ih =>
    simp only [lf, evalG]
    rw [lin_sub, lin_single, ih (by simpa [vars] using hs)]
    rfl

lemma holds_cons_pt (φ : LukPropForm ι) (hs : vars φ ⊆ s) :
    ∀ c ∈ cons u a s φ, c.Holds (pt u a s) := by
  induction φ with
  | var i => simp [cons]
  | tsub φ ψ ihφ ihψ =>
    have hs' : vars φ ⊆ s ∧ vars ψ ⊆ s := by
      simpa [vars, Finset.union_subset_iff] using hs
    intro c hc
    simp only [cons, List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | hc | hc
    · unfold branchCon
      split_ifs with h
      · simp only [KCon.Holds, KCon.eval_eq_lin, rel, Bool.false_eq_true, ite_false]
        rw [lin_sub, lin_lf_pt u a s φ hs'.1, lin_lf_pt u a s ψ hs'.2]
        exact sub_nonneg.mpr h
      · simp only [KCon.Holds, KCon.eval_eq_lin, rel, ite_true]
        rw [lin_sub, lin_lf_pt u a s φ hs'.1, lin_lf_pt u a s ψ hs'.2]
        exact sub_pos.mpr (not_le.mp h)
    · exact ihφ hs'.1 c hc
    · exact ihψ hs'.2 c hc
  | neg φ ih =>
    intro c hc
    exact ih (by simpa [vars] using hs) c hc

/-- The real assignment read off a real solution `y`. -/
def realVal (y : Option s → ℝ) : ι → ℝ :=
  fun i => if h : i ∈ s then y (some ⟨i, h⟩) / y none else 0

lemma eval_realVal (y : Option s → ℝ) (hy : 0 < y none) (φ : LukPropForm ι)
    (hs : vars φ ⊆ s) (hcons : ∀ c ∈ cons u a s φ, c.Holds y) :
    eval (realVal s y) φ = lin (lf u a s φ) y / y none := by
  induction φ with
  | var i =>
    have hi : i ∈ s := hs (by simp [vars])
    simp only [eval, realVal, dif_pos hi, lf, lin_single]
  | tsub φ ψ ihφ ihψ =>
    have hs' : vars φ ⊆ s ∧ vars ψ ⊆ s := by
      simpa [vars, Finset.union_subset_iff] using hs
    have hφ := ihφ hs'.1 (fun c hc => hcons c (by simp [cons, hc]))
    have hψ := ihψ hs'.2 (fun c hc => hcons c (by simp [cons, hc]))
    have hb := hcons (branchCon u a s φ ψ) (by simp [cons])
    simp only [eval, lf, tsubR.def_eq, hφ, hψ]
    unfold branchCon at hb
    split_ifs with h
    · rw [if_pos h] at hb
      simp only [KCon.Holds, KCon.eval_eq_lin, rel, Bool.false_eq_true, ite_false,
        lin_sub] at hb
      rw [lin_sub, ← sub_div, max_eq_left (div_nonneg (sub_nonneg.mpr (sub_nonneg.mp hb)) hy.le)]
    · rw [if_neg h] at hb
      simp only [KCon.Holds, KCon.eval_eq_lin, rel, ite_true, lin_sub] at hb
      rw [lin_zero, zero_div, ← sub_div]
      exact max_eq_right (div_nonpos_of_nonpos_of_nonneg (by linarith) hy.le)
  | neg φ ih =>
    have h := ih (by simpa [vars] using hs) (fun c hc => hcons c (by simpa [cons] using hc))
    simp only [eval, lf, h, lin_sub, lin_single]
    field_simp

end GroupEval

/-- **Γ(G, u) to `[0, 1]`.** If a Łukasiewicz formula takes a non-zero value in the
    interval `[0, u]` of a linearly ordered abelian group, it takes a non-zero value
    under some `[0, 1]`-valued assignment. -/
theorem exists_real_of_evalG_ne_zero {ι : Type*} {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] (u : G) (hu : 0 < u) (a : ι → G)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ u) (φ : LukPropForm ι) (hφ : evalG u a φ ≠ 0) :
    ∃ v : ι → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ 1) ∧ eval v φ ≠ 0 := by
  set s := vars φ with hs_def
  have hs : vars φ ⊆ s := le_refl _
  let base : List (KCon (Option s)) :=
    ⟨Pi.single none 1, true⟩ :: (Finset.univ : Finset s).toList.flatMap
      (fun k => [⟨Pi.single (some k) 1, false⟩, ⟨Pi.single none 1 - Pi.single (some k) 1, false⟩])
  let S : List (KCon (Option s)) := base ++ cons u a s φ ++ [⟨lf u a s φ, true⟩]
  have hpos : 0 < evalG u a φ := lt_of_le_of_ne (evalG_mem u a ha φ).1 (Ne.symm hφ)
  have hS : ∀ c ∈ S, c.Holds (pt u a s) := by
    intro c hc
    simp only [S, base, List.mem_append, List.mem_cons, List.mem_flatMap, Finset.mem_toList,
      Finset.mem_univ, true_and, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | ⟨k, rfl | rfl⟩) | hc) | rfl
    · simp only [KCon.Holds, KCon.eval_eq_lin, rel, ite_true, lin_single]
      exact hu
    · simp only [KCon.Holds, KCon.eval_eq_lin, rel, Bool.false_eq_true, ite_false, lin_single]
      exact (ha k).1
    · simp only [KCon.Holds, KCon.eval_eq_lin, rel, Bool.false_eq_true, ite_false, lin_sub,
        lin_single]
      exact sub_nonneg.mpr (ha k).2
    · exact holds_cons_pt u a s φ hs c hc
    · simp only [KCon.Holds, KCon.eval_eq_lin, rel, ite_true]
      rw [lin_lf_pt u a s φ hs]
      exact hpos
  obtain ⟨y, hy⟩ := exists_real_solution_fintype S (pt u a s) hS
  have hmem : ∀ c, c ∈ base → c ∈ S := fun c hc => by simp [S, hc]
  have hy0 : 0 < y none := by
    have h := hy ⟨Pi.single none 1, true⟩ (hmem _ List.mem_cons_self)
    simpa [KCon.Holds, KCon.eval_eq_lin, rel, lin_single] using h
  have hyk : ∀ k : s, 0 ≤ y (some k) ∧ y (some k) ≤ y none := by
    intro k
    have hk : k ∈ (Finset.univ : Finset s).toList := Finset.mem_toList.mpr (Finset.mem_univ k)
    have h1 := hy ⟨Pi.single (some k) 1, false⟩ (hmem _ (List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨k, hk, by simp⟩)))
    have h2 := hy ⟨Pi.single none 1 - Pi.single (some k) 1, false⟩ (hmem _ (List.mem_cons_of_mem _
      (List.mem_flatMap.mpr ⟨k, hk, by simp⟩)))
    simp only [KCon.Holds, KCon.eval_eq_lin, rel, Bool.false_eq_true, ite_false, lin_sub,
      lin_single] at h1 h2
    exact ⟨h1, by linarith⟩
  have hcons : ∀ c ∈ cons u a s φ, c.Holds y := fun c hc => hy c (by simp [S, hc])
  have hlast := hy ⟨lf u a s φ, true⟩ (by simp [S])
  simp only [KCon.Holds, KCon.eval_eq_lin, rel, ite_true] at hlast
  refine ⟨realVal s y, fun i => ?_, ?_⟩
  · unfold realVal
    split_ifs with h
    · exact ⟨div_nonneg (hyk _).1 hy0.le, (div_le_one hy0).mpr (hyk _).2⟩
    · exact ⟨le_refl _, zero_le_one⟩
  · rw [eval_realVal u a s y hy0 φ hs hcons]
    exact (div_pos hlast hy0).ne'

end LukPropForm

end ContinuousFOL
