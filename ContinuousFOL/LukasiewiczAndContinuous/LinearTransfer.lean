/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: algebraic background for Fact 4.1 (Chang 1959). This is the
"ordered abelian groups have the universal theory of ℝ" step (Gurevich–Kokorin),
in the form needed by Chang's completeness theorem: a finite system of homogeneous
integer-linear inequalities (strict or not) that has a solution in some linearly
ordered abelian group already has a real solution. The proof is Fourier–Motzkin
elimination, which only takes non-negative integer combinations, so every step is
valid in an arbitrary ordered abelian group.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LinTransfer

/-- `rel s a b` is `a < b` when `s` is true and `a ≤ b` otherwise. -/
def rel {α : Type*} [Preorder α] (s : Bool) (a b : α) : Prop :=
  if s then a < b else a ≤ b

lemma rel_le {α : Type*} [Preorder α] {s : Bool} {a b : α} (h : rel s a b) : a ≤ b := by
  cases s
  · simpa [rel] using h
  · exact le_of_lt (by simpa [rel] using h)

/-- A homogeneous integer-linear constraint in `n` variables:
    `0 ≤ ∑ coef j • x j`, or `0 < ∑ coef j • x j` when `strict`. -/
structure LinCon (n : ℕ) where
  coef : Fin n → ℤ
  strict : Bool

namespace LinCon

variable {n : ℕ}

def eval {M : Type*} [AddCommGroup M] (c : LinCon n) (x : Fin n → M) : M :=
  ∑ j, c.coef j • x j

def Holds {M : Type*} [AddCommGroup M] [Preorder M] (c : LinCon n) (x : Fin n → M) : Prop :=
  rel c.strict 0 (c.eval x)

/-- The constraint with the last variable dropped. -/
def rest (c : LinCon (n + 1)) : LinCon n :=
  ⟨fun j => c.coef j.castSucc, c.strict⟩

/-- The coefficient of the last variable. -/
def lead (c : LinCon (n + 1)) : ℤ :=
  c.coef (Fin.last n)

lemma eval_succ {M : Type*} [AddCommGroup M] (c : LinCon (n + 1)) (x : Fin (n + 1) → M) :
    c.eval x = c.rest.eval (fun j => x j.castSucc) + c.lead • x (Fin.last n) := by
  simp [eval, rest, lead, Fin.sum_univ_castSucc]

/-- The Fourier–Motzkin combination of a constraint with positive leading coefficient
    and one with negative leading coefficient. -/
def comb (p q : LinCon (n + 1)) : LinCon n :=
  ⟨fun j => (-q.lead) * p.coef j.castSucc + p.lead * q.coef j.castSucc, p.strict || q.strict⟩

lemma eval_comb {M : Type*} [AddCommGroup M] (p q : LinCon (n + 1)) (x : Fin n → M) :
    (p.comb q).eval x = (-q.lead) • p.rest.eval x + p.lead • q.rest.eval x := by
  simp only [eval, comb, rest, add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]

end LinCon

open LinCon

/-- One round of Fourier–Motzkin elimination of the last variable. -/
def elim {n : ℕ} (S : List (LinCon (n + 1))) : List (LinCon n) :=
  (S.filter (fun c => c.lead = 0)).map LinCon.rest ++
    (S.filter (fun c => 0 < c.lead)).flatMap
      (fun p => (S.filter (fun c => c.lead < 0)).map (LinCon.comb p))

section Group

variable {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]

lemma rel_add {s t : Bool} {a b : G} (ha : rel s 0 a) (hb : rel t 0 b) :
    rel (s || t) 0 (a + b) := by
  cases s <;> cases t <;> simp only [rel, Bool.or_false, Bool.or_true,
    ite_true, ite_false, Bool.false_eq_true] at ha hb ⊢
  · exact add_nonneg ha hb
  · exact add_pos_of_nonneg_of_pos ha hb
  · exact add_pos_of_pos_of_nonneg ha hb
  · exact add_pos ha hb

lemma rel_zsmul {s : Bool} {a : G} {k : ℤ} (hk : 0 < k) (ha : rel s 0 a) :
    rel s 0 (k • a) := by
  cases s <;> simp only [rel, ite_true, ite_false, Bool.false_eq_true] at ha ⊢
  · exact zsmul_nonneg ha hk.le
  · exact zsmul_pos ha hk

/-- Elimination is sound in any ordered abelian group. -/
lemma holds_elim {n : ℕ} (S : List (LinCon (n + 1))) (x : Fin (n + 1) → G)
    (hS : ∀ c ∈ S, c.Holds x) : ∀ c ∈ elim S, c.Holds (fun j => x j.castSucc) := by
  intro c hc
  simp only [elim, List.mem_append, List.mem_map, List.mem_filter, List.mem_flatMap,
    decide_eq_true_eq] at hc
  rcases hc with ⟨c', ⟨hc'S, hc'0⟩, rfl⟩ | ⟨p, ⟨hpS, hp⟩, q, ⟨hqS, hq⟩, rfl⟩
  · have h := hS c' hc'S
    simp only [Holds, eval_succ, hc'0, zero_smul, add_zero] at h
    exact h
  · have hp' := hS p hpS
    have hq' := hS q hqS
    simp only [Holds, eval_succ] at hp' hq'
    have key : (p.comb q).eval (fun j => x j.castSucc) =
        (-q.lead) • (p.rest.eval (fun j => x j.castSucc) + p.lead • x (Fin.last n)) +
          p.lead • (q.rest.eval (fun j => x j.castSucc) + q.lead • x (Fin.last n)) := by
      rw [eval_comb]
      module
    have h := rel_add (rel_zsmul (neg_pos.mpr hq) hp') (rel_zsmul hp hq')
    simp only [Holds]
    rw [key]
    exact h

end Group

/-- Choosing a real number between finitely many lower and upper bounds. -/
lemma exists_between_lists {α : Type*} (L U : List α) (l u : α → ℝ) (sl su : α → Bool)
    (h : ∀ p ∈ L, ∀ q ∈ U, rel (sl p || su q) (l p) (u q)) :
    ∃ t : ℝ, (∀ p ∈ L, rel (sl p) (l p) t) ∧ ∀ q ∈ U, rel (su q) t (u q) := by
  by_cases hL : L = []
  · subst hL
    by_cases hU : U = []
    · subst hU
      exact ⟨0, by simp, by simp⟩
    · obtain ⟨q0, hq0, hmin⟩ := U.toFinset.exists_min_image u (by simpa using hU)
      refine ⟨u q0 - 1, by simp, fun q hq => ?_⟩
      have := hmin q (by simpa using hq)
      cases su q <;> simp [rel] <;> linarith
  · obtain ⟨p0, hp0, hmax⟩ := L.toFinset.exists_max_image l (by simpa using hL)
    have hp0' : p0 ∈ L := by simpa using hp0
    by_cases hU : U = []
    · subst hU
      refine ⟨l p0 + 1, fun p hp => ?_, by simp⟩
      have := hmax p (by simpa using hp)
      cases sl p <;> simp [rel] <;> linarith
    · obtain ⟨q0, hq0, hmin⟩ := U.toFinset.exists_min_image u (by simpa using hU)
      have hq0' : q0 ∈ U := by simpa using hq0
      have h00 := rel_le (h p0 hp0' q0 hq0')
      rcases lt_or_eq_of_le h00 with hlt | heq
      · refine ⟨(l p0 + u q0) / 2, fun p hp => ?_, fun q hq => ?_⟩
        · have := hmax p (by simpa using hp)
          cases sl p <;> simp [rel] <;> linarith
        · have := hmin q (by simpa using hq)
          cases su q <;> simp [rel] <;> linarith
      · refine ⟨l p0, fun p hp => ?_, fun q hq => ?_⟩
        · have hle := hmax p (by simpa using hp)
          have hpq := h p hp q0 hq0'
          cases hs : sl p
          · simpa [rel] using hle
          · simp only [hs, Bool.true_or, rel, ite_true] at hpq
            simp only [rel, ite_true]
            linarith
        · have hle := rel_le (h p0 hp0' q hq)
          have hpq := h p0 hp0' q hq
          cases hs : su q
          · simpa [rel] using hle
          · simp only [hs, Bool.or_true, rel, ite_true] at hpq
            simp only [rel, ite_true]
            exact hpq

lemma eval_real_succ {n : ℕ} (c : LinCon (n + 1)) (y' : Fin n → ℝ) (t : ℝ) :
    c.eval (Fin.snoc y' t : Fin (n + 1) → ℝ) = c.rest.eval y' + (c.lead : ℝ) * t := by
  rw [eval_succ]
  simp [Fin.snoc_castSucc, Fin.snoc_last, zsmul_eq_mul]

/-- **Transfer.** A finite system of homogeneous integer-linear inequalities that is
    solvable in some linearly ordered abelian group is solvable in `ℝ`. -/
theorem exists_real_solution {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] :
    ∀ (n : ℕ) (S : List (LinCon n)) (x : Fin n → G), (∀ c ∈ S, c.Holds x) →
      ∃ y : Fin n → ℝ, ∀ c ∈ S, c.Holds y := by
  intro n
  induction n with
  | zero =>
    intro S x hS
    refine ⟨0, fun c hc => ?_⟩
    have h := hS c hc
    simp only [Holds, eval, Finset.univ_eq_empty, Finset.sum_empty] at h ⊢
    cases hs : c.strict
    · simp [rel]
    · simp [hs, rel] at h
  | succ n ih =>
    intro S x hS
    obtain ⟨y', hy'⟩ := ih (elim S) _ (holds_elim S x hS)
    let L := S.filter (fun c => 0 < c.lead)
    let U := S.filter (fun c => c.lead < 0)
    have hpair : ∀ p ∈ L, ∀ q ∈ U,
        rel (p.strict || q.strict) (-(p.rest.eval y') / (p.lead : ℝ))
          (q.rest.eval y' / (-(q.lead : ℝ))) := by
      intro p hp q hq
      have hp' : 0 < p.lead := by simpa [L] using (List.mem_filter.mp hp).2
      have hq' : q.lead < 0 := by simpa [U] using (List.mem_filter.mp hq).2
      have hmem : p.comb q ∈ elim S := by
        simp only [elim, List.mem_append, List.mem_flatMap, List.mem_map]
        exact Or.inr ⟨p, hp, q, hq, rfl⟩
      have h : rel (p.strict || q.strict) 0 ((p.comb q).eval y') := hy' _ hmem
      simp only [eval_comb, zsmul_eq_mul] at h
      have hA : (0 : ℝ) < p.lead := by exact_mod_cast hp'
      have hB : (0 : ℝ) < -(q.lead : ℝ) := by
        have : (q.lead : ℝ) < 0 := by exact_mod_cast hq'
        linarith
      cases hs : (p.strict || q.strict)
      · simp only [hs, rel, ite_false, Bool.false_eq_true] at h ⊢
        rw [div_le_div_iff₀ hA hB]
        push_cast at h
        nlinarith
      · simp only [hs, rel, ite_true] at h ⊢
        rw [div_lt_div_iff₀ hA hB]
        push_cast at h
        nlinarith
    obtain ⟨t, hlow, hup⟩ := exists_between_lists L U
      (fun p => -(p.rest.eval y') / (p.lead : ℝ)) (fun q => q.rest.eval y' / (-(q.lead : ℝ)))
      LinCon.strict LinCon.strict hpair
    refine ⟨Fin.snoc y' t, fun c hc => ?_⟩
    simp only [Holds, eval_real_succ]
    rcases lt_trichotomy c.lead 0 with hneg | hzero | hpos
    · have hcU : c ∈ U := List.mem_filter.mpr ⟨hc, by simpa using hneg⟩
      have h := hup c hcU
      have hB : (0 : ℝ) < -(c.lead : ℝ) := by
        have : (c.lead : ℝ) < 0 := by exact_mod_cast hneg
        linarith
      cases hs : c.strict
      · simp only [hs, rel, ite_false, Bool.false_eq_true] at h ⊢
        rw [le_div_iff₀ hB] at h
        linarith
      · simp only [hs, rel, ite_true] at h ⊢
        rw [lt_div_iff₀ hB] at h
        linarith
    · have hmem : c.rest ∈ elim S := by
        simp only [elim, List.mem_append, List.mem_map]
        exact Or.inl ⟨c, List.mem_filter.mpr ⟨hc, by simpa using hzero⟩, rfl⟩
      have h : rel c.strict 0 (c.rest.eval y') := hy' _ hmem
      simpa [hzero] using h
    · have hcL : c ∈ L := List.mem_filter.mpr ⟨hc, by simpa using hpos⟩
      have h := hlow c hcL
      have hA : (0 : ℝ) < c.lead := by exact_mod_cast hpos
      cases hs : c.strict
      · simp only [hs, rel, ite_false, Bool.false_eq_true] at h ⊢
        rw [div_le_iff₀ hA] at h
        linarith
      · simp only [hs, rel, ite_true] at h ⊢
        rw [div_lt_iff₀ hA] at h
        linarith

/-- A homogeneous integer-linear constraint over a finite index type `κ`. -/
structure KCon (κ : Type*) where
  coef : κ → ℤ
  strict : Bool

namespace KCon

variable {κ : Type*} [Fintype κ]

def eval {M : Type*} [AddCommGroup M] (c : KCon κ) (x : κ → M) : M :=
  ∑ k, c.coef k • x k

def Holds {M : Type*} [AddCommGroup M] [Preorder M] (c : KCon κ) (x : κ → M) : Prop :=
  rel c.strict 0 (c.eval x)

/-- Transport along `κ ≃ Fin n`. -/
def toLin (c : KCon κ) : LinCon (Fintype.card κ) :=
  ⟨fun j => c.coef ((Fintype.equivFin κ).symm j), c.strict⟩

lemma eval_toLin {M : Type*} [AddCommGroup M] (c : KCon κ) (x : κ → M) :
    c.toLin.eval (fun j => x ((Fintype.equivFin κ).symm j)) = c.eval x := by
  simp only [toLin, LinCon.eval, eval]
  exact Equiv.sum_comp (Fintype.equivFin κ).symm (fun k => c.coef k • x k)

end KCon

/-- **Transfer** over a finite index type. -/
theorem exists_real_solution_fintype {κ : Type*} [Fintype κ]
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    (S : List (KCon κ)) (x : κ → G) (hS : ∀ c ∈ S, c.Holds x) :
    ∃ y : κ → ℝ, ∀ c ∈ S, c.Holds y := by
  obtain ⟨y', hy'⟩ := exists_real_solution _ (S.map KCon.toLin)
    (fun j => x ((Fintype.equivFin κ).symm j)) (by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      have h := hS c' hc'
      simp only [LinCon.Holds, KCon.Holds] at h ⊢
      rw [KCon.eval_toLin]
      exact h)
  refine ⟨fun k => y' (Fintype.equivFin κ k), fun c hc => ?_⟩
  have h := hy' _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  simp only [LinCon.Holds, KCon.Holds] at h ⊢
  rw [← KCon.eval_toLin]
  simpa [KCon.toLin] using h

end LinTransfer

end ContinuousFOL
