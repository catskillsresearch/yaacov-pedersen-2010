/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Piecewise-linear charts on the unit cube, used to prove a uniform slope
bound for propositional evaluations.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.PolyCell
public import ContinuousFOL.Introduction.TsubR
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.ProdSigma
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section
open Classical
open Set

namespace ContinuousFOL

namespace PolyCell

variable {n : ℕ}

def inter (C D : PolyCell n) : PolyCell n :=
  ⟨C.ineq ∪ D.ineq⟩

lemma mem_inter {C D : PolyCell n} {x : Fin n → ℝ} :
    x ∈ (C.inter D).toSet ↔ x ∈ C.toSet ∧ x ∈ D.toSet := by
  constructor
  · intro hx
    constructor
    · intro a ha
      apply hx
      simp only [inter, constraints, Finset.mem_union]
      rcases Finset.mem_union.1 ha with hI | hC
      · exact Or.inl (Or.inl hI)
      · exact Or.inr hC
    · intro a ha
      apply hx
      simp only [inter, constraints, Finset.mem_union]
      rcases Finset.mem_union.1 ha with hI | hC
      · exact Or.inl (Or.inr hI)
      · exact Or.inr hC
  · intro ⟨hC, hD⟩ a ha
    simp only [inter, constraints, Finset.mem_union] at ha
    rcases ha with hCD | hcube
    · rcases hCD with hCi | hDi
      · exact hC a (Finset.mem_union.2 (Or.inl hCi))
      · exact hD a (Finset.mem_union.2 (Or.inl hDi))
    · exact hC a (Finset.mem_union.2 (Or.inr hcube))

def restrict (C : PolyCell n) (a : AffineFn n) : PolyCell n :=
  ⟨C.ineq ∪ {a}⟩

lemma mem_restrict {C : PolyCell n} {a : AffineFn n} {x : Fin n → ℝ} :
    x ∈ (C.restrict a).toSet ↔ x ∈ C.toSet ∧ a.eval x ≤ 0 := by
  constructor
  · intro hx
    constructor
    · intro f hf
      apply hx
      simp only [restrict, constraints, Finset.mem_union, Finset.mem_singleton]
      rcases Finset.mem_union.1 hf with hI | hC
      · exact Or.inl (Or.inl hI)
      · exact Or.inr hC
    · apply hx
      simp [restrict, constraints]
  · intro ⟨hC, ha⟩ f hf
    simp only [restrict, constraints, Finset.mem_union, Finset.mem_singleton] at hf
    rcases hf with (hI | hEq) | hcube
    · exact hC f (Finset.mem_union.2 (Or.inl hI))
    · simpa [hEq] using ha
    · exact hC f (Finset.mem_union.2 (Or.inr hcube))

def equalize (C : PolyCell n) (a : AffineFn n) : PolyCell n :=
  (C.restrict a).restrict a.neg

lemma mem_equalize {C : PolyCell n} {a : AffineFn n} {x : Fin n → ℝ} :
    x ∈ (C.equalize a).toSet ↔ x ∈ C.toSet ∧ a.eval x = 0 := by
  simp only [equalize, mem_restrict, AffineFn.eval_neg]
  constructor
  · intro ⟨⟨hC, hle⟩, hneg⟩
    exact ⟨hC, le_antisymm hle (by linarith)⟩
  · intro ⟨hC, heq⟩
    simp [hC, heq]

def cube (n : ℕ) : PolyCell n :=
  ⟨∅⟩

lemma mem_cube {x : Fin n → ℝ} : x ∈ (cube n).toSet ↔ x ∈ unitCube n := by
  constructor
  · intro hx
    exact PolyCell.mem_unitCube hx
  · intro hx a ha
    have hle : ∀ a ∈ cubeConstraints n, a.eval x ≤ 0 := (cubeConstraints_le).2 hx
    simp only [cube, constraints, Finset.empty_union] at ha
    exact hle a ha

end PolyCell

variable {n : ℕ}

/-- An affine expression together with the polyhedral cell on which it is valid. -/
structure AffineChart (n : ℕ) where
  cell : PolyCell n
  fn : AffineFn n

def AffineChart.Represents (ch : AffineChart n) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x ∈ ch.cell.toSet, f x = ch.fn.eval x

/-- `f` is piecewise affine on a finite polyhedral cover of the unit cube. -/
def HasPL {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ charts : List (AffineChart n),
    (∀ x ∈ unitCube n, ∃ ch ∈ charts, x ∈ ch.cell.toSet) ∧
    (∀ ch ∈ charts, ch.Represents f)

lemma hasPL_const {n : ℕ} (c : ℝ) : HasPL (fun _ : Fin n → ℝ => c) := by
  refine ⟨[{ cell := PolyCell.cube n, fn := AffineFn.const c }], ?_, ?_⟩
  · intro x hx
    refine ⟨_, List.mem_singleton.2 rfl, ?_⟩
    exact (PolyCell.mem_cube).2 hx
  · intro ch hch x hx
    simp only [List.mem_singleton] at hch
    subst hch
    simp [AffineFn.eval_const]

lemma hasPL_proj {n : ℕ} (i : Fin n) : HasPL (fun x : Fin n → ℝ => x i) := by
  refine ⟨[{ cell := PolyCell.cube n, fn := AffineFn.proj i }], ?_, ?_⟩
  · intro x hx
    refine ⟨_, List.mem_singleton.2 rfl, ?_⟩
    exact (PolyCell.mem_cube).2 hx
  · intro ch hch x hx
    simp only [List.mem_singleton] at hch
    subst hch
    simp [AffineFn.eval_proj]

lemma hasPL_neg {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : HasPL f) :
    HasPL (fun x => 1 - f x) := by
  obtain ⟨charts, hcov, hrep⟩ := hf
  refine ⟨charts.map (fun ch => ⟨ch.cell, (AffineFn.const 1).sub ch.fn⟩), ?_, ?_⟩
  · intro x hx
    obtain ⟨ch, hch, hxch⟩ := hcov x hx
    exact ⟨⟨ch.cell, (AffineFn.const 1).sub ch.fn⟩, List.mem_map.2 ⟨ch, hch, rfl⟩, hxch⟩
  · intro ch' hch' x hx
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    have := hrep ch hch x hx
    simp [AffineFn.eval_sub, AffineFn.eval_const, this]

lemma hasPL_smul {n : ℕ} {f : (Fin n → ℝ) → ℝ} (c : ℝ) (hf : HasPL f) :
    HasPL (fun x => c * f x) := by
  obtain ⟨charts, hcov, hrep⟩ := hf
  refine ⟨charts.map (fun ch => ⟨ch.cell, ch.fn.smul c⟩), ?_, ?_⟩
  · intro x hx
    obtain ⟨ch, hch, hxch⟩ := hcov x hx
    exact ⟨⟨ch.cell, ch.fn.smul c⟩, List.mem_map.2 ⟨ch, hch, rfl⟩, hxch⟩
  · intro ch' hch' x hx
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.1 hch'
    have := hrep ch hch x hx
    simp [AffineFn.eval_smul, this]

/-- Common refinement of two piecewise-linear covers. -/
lemma HasPL.pair {n : ℕ} {f g : (Fin n → ℝ) → ℝ} (hf : HasPL f) (hg : HasPL g) :
    ∃ charts : List (PolyCell n × AffineFn n × AffineFn n),
      (∀ x ∈ unitCube n, ∃ ch ∈ charts, x ∈ ch.1.toSet) ∧
      (∀ ch ∈ charts, (∀ x ∈ ch.1.toSet, f x = ch.2.1.eval x) ∧
        ∀ x ∈ ch.1.toSet, g x = ch.2.2.eval x) := by
  obtain ⟨cf, hcovf, hrepf⟩ := hf
  obtain ⟨cg, hcovg, hrepg⟩ := hg
  refine ⟨cf ×ˢ cg |>.map (fun p => (p.1.cell.inter p.2.cell, p.1.fn, p.2.fn)), ?_, ?_⟩
  · intro x hx
    obtain ⟨chf, hcf, hxf⟩ := hcovf x hx
    obtain ⟨chg, hcg, hxg⟩ := hcovg x hx
    refine ⟨(chf.cell.inter chg.cell, chf.fn, chg.fn), ?_, ?_⟩
    · exact List.mem_map.2 ⟨(chf, chg), List.mem_product.2 ⟨hcf, hcg⟩, rfl⟩
    · exact (PolyCell.mem_inter).2 ⟨hxf, hxg⟩
  · intro ch hch
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hch
    obtain ⟨hp1, hp2⟩ := List.mem_product.1 hp
    constructor
    · intro x hx
      have hx' := (PolyCell.mem_inter).1 hx
      exact hrepf p.1 hp1 x hx'.1
    · intro x hx
      have hx' := (PolyCell.mem_inter).1 hx
      exact hrepg p.2 hp2 x hx'.2

lemma hasPL_tsub {n : ℕ} {f g : (Fin n → ℝ) → ℝ} (hf : HasPL f) (hg : HasPL g) :
    HasPL (fun x => f x ∸ g x) := by
  obtain ⟨charts, hcov, hrep⟩ := HasPL.pair hf hg
  let split : List (AffineChart n) :=
    charts.flatMap fun ch =>
      [⟨ch.1.restrict (ch.2.1.sub ch.2.2), AffineFn.const 0⟩,
        ⟨ch.1.restrict (ch.2.2.sub ch.2.1), ch.2.1.sub ch.2.2⟩]
  refine ⟨split, ?_, ?_⟩
  · intro x hx
    obtain ⟨ch, hch, hxch⟩ := hcov x hx
    have hfg : (ch.2.1.sub ch.2.2).eval x ≤ 0 ∨ (ch.2.2.sub ch.2.1).eval x ≤ 0 := by
      rw [AffineFn.eval_sub, AffineFn.eval_sub]
      cases le_total (ch.2.1.eval x) (ch.2.2.eval x) with
      | inl h => exact Or.inl (sub_nonpos_of_le h)
      | inr h => exact Or.inr (sub_nonpos_of_le h)
    rcases hfg with hle | hle
    · refine ⟨⟨ch.1.restrict (ch.2.1.sub ch.2.2), AffineFn.const 0⟩, ?_, ?_⟩
      · exact List.mem_flatMap.2 ⟨ch, hch, by simp⟩
      · exact (PolyCell.mem_restrict).2 ⟨hxch, hle⟩
    · refine ⟨⟨ch.1.restrict (ch.2.2.sub ch.2.1), ch.2.1.sub ch.2.2⟩, ?_, ?_⟩
      · exact List.mem_flatMap.2 ⟨ch, hch, by simp⟩
      · exact (PolyCell.mem_restrict).2 ⟨hxch, hle⟩
  · intro ch' hch' x hx
    simp only [split, List.mem_flatMap] at hch'
    obtain ⟨ch, hch, hmem⟩ := hch'
    have hmem' : ch' = ⟨ch.1.restrict (ch.2.1.sub ch.2.2), AffineFn.const 0⟩ ∨
        ch' = ⟨ch.1.restrict (ch.2.2.sub ch.2.1), ch.2.1.sub ch.2.2⟩ := by
      simpa [List.mem_cons, List.mem_singleton] using hmem
    rcases hmem' with rfl | rfl
    · 
      have hx' := (PolyCell.mem_restrict).1 hx
      have hfval := (hrep ch hch).1 x hx'.1
      have hgval := (hrep ch hch).2 x hx'.1
      have hle : f x - g x ≤ 0 := by
        have := hx'.2
        simp [AffineFn.eval_sub] at this
        linarith
      have : f x ∸ g x = 0 := (tsubR.eq_zero_iff _ _).2 (by linarith)
      simpa [AffineFn.eval_const] using this
    · 
      have hx' := (PolyCell.mem_restrict).1 hx
      have hfval := (hrep ch hch).1 x hx'.1
      have hgval := (hrep ch hch).2 x hx'.1
      have hle : g x - f x ≤ 0 := by
        have := hx'.2
        simp [AffineFn.eval_sub] at this
        linarith
      have hfg : f x ∸ g x = f x - g x := by
        rw [tsubR.def_eq, max_eq_left (by linarith)]
      calc
        f x ∸ g x = f x - g x := hfg
        _ = ch.2.1.eval x - ch.2.2.eval x := by rw [hfval, hgval]
        _ = (ch.2.1.sub ch.2.2).eval x := (AffineFn.eval_sub _ _ x).symm

lemma mem_equalize_foldl {n : ℕ} (C : PolyCell n) (as : List (AffineFn n)) (x : Fin n → ℝ) :
    x ∈ (as.foldl PolyCell.equalize C).toSet ↔
      x ∈ C.toSet ∧ ∀ a ∈ as, a.eval x = 0 := by
  induction as generalizing C with
  | nil => simp
  | cons a tl ih =>
    simp [List.foldl_cons, ih, PolyCell.mem_equalize, and_assoc]

lemma exists_nat_forall_list {α : Type*} (l : List α) (P : ℕ → α → Prop)
    (h : ∀ a ∈ l, ∃ N, P N a)
    (hmono : ∀ {N N' : ℕ} {a}, a ∈ l → N ≤ N' → P N a → P N' a) :
    ∃ N, ∀ a ∈ l, P N a := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a tl ih =>
    obtain ⟨Na, hNa⟩ := h a (by simp)
    obtain ⟨Ntl, hNtl⟩ := ih (fun b hb => h b (by simp [hb]))
      (fun hb hle hP => hmono (by simp [hb]) hle hP)
    refine ⟨max Na Ntl, ?_⟩
    intro b hb
    simp only [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hmono (by simp) (le_max_left Na Ntl) hNa
    · exact hmono (by simp [hb]) (le_max_right Na Ntl) (hNtl b hb)

/-- Refine two piecewise-linear functions together with a list of constraints. -/
lemma refine_with_hyps {n : ℕ} (hyps : List ((Fin n → ℝ) → ℝ))
    {f g : (Fin n → ℝ) → ℝ} (hhyps : ∀ h ∈ hyps, HasPL h)
    (hf : HasPL f) (hg : HasPL g) :
    ∃ charts : List (PolyCell n × AffineFn n × AffineFn n × List (AffineFn n)),
      (∀ x ∈ unitCube n, ∃ ch ∈ charts, x ∈ ch.1.toSet) ∧
      (∀ ch ∈ charts, ch.2.2.2.length = hyps.length) ∧
      (∀ ch ∈ charts, ∀ x ∈ ch.1.toSet, f x = ch.2.1.eval x ∧ g x = ch.2.2.1.eval x) ∧
      (∀ ch ∈ charts, ∀ (i : ℕ) (a : (Fin n → ℝ) → ℝ),
        hyps[i]? = some a → ∀ x ∈ ch.1.toSet,
          a x = ((ch.2.2.2[i]?).getD (AffineFn.const 0)).eval x) := by
  induction hyps with
  | nil =>
    obtain ⟨charts, hcov, hrep⟩ := HasPL.pair hf hg
    refine ⟨charts.map (fun ch => (ch.1, ch.2.1, ch.2.2, [])), ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨ch, hch, hxch⟩ := hcov x hx
      exact ⟨(ch.1, ch.2.1, ch.2.2, []), List.mem_map.2 ⟨ch, hch, rfl⟩, hxch⟩
    · intro ch hch
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hch
      rfl
    · intro ch hch x hx
      obtain ⟨ch0, hch0, rfl⟩ := List.mem_map.1 hch
      exact ⟨(hrep ch0 hch0).1 x hx, (hrep ch0 hch0).2 x hx⟩
    · intro ch _ i a hsome
      simp at hsome
  | cons h tl ih =>
    have ih' := ih (fun k hk => hhyps k (List.mem_cons.2 (Or.inr hk)))
    obtain ⟨ch0, hcov0, hlen0, hfg0, hhy0⟩ := ih'
    have hh : HasPL h := hhyps h (List.mem_cons.2 (Or.inl rfl))
    obtain ⟨chh, hcovh, hreph⟩ := hh
    let charts : List (PolyCell n × AffineFn n × AffineFn n × List (AffineFn n)) :=
      (ch0 ×ˢ chh).map fun p =>
        (p.1.1.inter p.2.cell, p.1.2.1, p.1.2.2.1, p.2.fn :: p.1.2.2.2)
    refine ⟨charts, ?_, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨c0, hc0, hx0⟩ := hcov0 x hx
      obtain ⟨ch, hch, hxh⟩ := hcovh x hx
      refine ⟨(c0.1.inter ch.cell, c0.2.1, c0.2.2.1, ch.fn :: c0.2.2.2), ?_, ?_⟩
      · exact List.mem_map.2 ⟨(c0, ch), List.mem_product.2 ⟨hc0, hch⟩, rfl⟩
      · exact (PolyCell.mem_inter).2 ⟨hx0, hxh⟩
    · intro ch hch
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hch
      simp [hlen0 p.1 (List.mem_product.1 hp).1]
    · intro ch hch x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hch
      have hx' := (PolyCell.mem_inter).1 hx
      exact hfg0 p.1 (List.mem_product.1 hp).1 x hx'.1
    · intro ch hch i a hsome x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hch
      have hx' := (PolyCell.mem_inter).1 hx
      have hp0 := (List.mem_product.1 hp).1
      have hph := (List.mem_product.1 hp).2
      cases i with
      | zero =>
        cases hsome
        simpa using (hreph p.2 hph x hx'.2)
      | succ j =>
        exact hhy0 p.1 hp0 j a hsome x hx'.1

/-- If `f` and `g` are piecewise linear on the cube, `g` is nonnegative, and
`f` vanishes whenever `g` and a finite list of piecewise-linear constraints do,
then `f ≤ N g` on the constraint set for some uniform `N`. -/
lemma semantic_iteration_cube {n : ℕ}
    (hyps : List ((Fin n → ℝ) → ℝ)) (f g : (Fin n → ℝ) → ℝ)
    (hhyps : ∀ h ∈ hyps, HasPL h) (hf : HasPL f) (hg : HasPL g)
    (hg0 : ∀ x ∈ unitCube n, 0 ≤ g x)
    (hvan : ∀ x ∈ unitCube n, (∀ h ∈ hyps, h x = 0) → g x = 0 → f x = 0) :
    ∃ N : ℕ, ∀ x ∈ unitCube n, (∀ h ∈ hyps, h x = 0) → f x ≤ (N : ℝ) * g x := by
  obtain ⟨charts, hcov, hlen, hfg, hhy⟩ := refine_with_hyps hyps hhyps hf hg
  let cell' (ch : PolyCell n × AffineFn n × AffineFn n × List (AffineFn n)) : PolyCell n :=
    ch.2.2.2.foldl PolyCell.equalize ch.1
  have hbound : ∀ ch ∈ charts,
      ∃ N : ℕ, ∀ x ∈ (cell' ch).toSet, ch.2.1.eval x ≤ (N : ℝ) * ch.2.2.1.eval x := by
    intro ch hch
    refine PolyCell.affine_ratio_bound (cell' ch) ch.2.1 ch.2.2.1 ?_ ?_
    · intro x hx
      have hxC := (mem_equalize_foldl ch.1 ch.2.2.2 x).1 hx |>.1
      have hxU := PolyCell.mem_unitCube hxC
      have := (hfg ch hch x hxC).2
      rw [← this]
      exact hg0 x hxU
    · intro x hx hg0x
      have hxall := (mem_equalize_foldl ch.1 ch.2.2.2 x).1 hx
      have hxC := hxall.1
      have hxU := PolyCell.mem_unitCube hxC
      have hhyps0 : ∀ h ∈ hyps, h x = 0 := by
        intro h hh
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hh
        have hsome : hyps[i]? = some (hyps[i]) := List.getElem?_eq_getElem hi
        have heq := hhy ch hch i (hyps[i]) hsome x hxC
        have hlen' := hlen ch hch
        have hidx : i < ch.2.2.2.length := by omega
        have hget : (ch.2.2.2[i]?).getD (AffineFn.const 0) = ch.2.2.2[i] := by
          simp [List.getElem?_eq_getElem hidx]
        have haff : (ch.2.2.2[i]).eval x = 0 :=
          hxall.2 _ (List.getElem_mem hidx)
        simpa [heq, hget] using haff
      have hfval := (hfg ch hch x hxC).1
      have hgval := (hfg ch hch x hxC).2
      have : g x = 0 := by simpa [hgval] using hg0x
      have := hvan x hxU hhyps0 this
      simpa [hfval] using this
  obtain ⟨N, hN⟩ := exists_nat_forall_list charts
    (fun N ch => ∀ x ∈ (cell' ch).toSet, ch.2.1.eval x ≤ (N : ℝ) * ch.2.2.1.eval x)
    hbound
    (fun {N N' ch} hch hle hNx x hx => by
      have := hNx x hx
      have hxC := (mem_equalize_foldl ch.1 ch.2.2.2 x).1 hx |>.1
      have hxU := PolyCell.mem_unitCube hxC
      have hgval := (hfg ch hch x hxC).2
      have hgnonneg : 0 ≤ ch.2.2.1.eval x := by
        rw [← hgval]
        exact hg0 x hxU
      have hcast : (N : ℝ) ≤ (N' : ℝ) := Nat.cast_le.mpr hle
      nlinarith [hcast])
  refine ⟨N, ?_⟩
  intro x hx hhyps0
  obtain ⟨ch, hch, hxch⟩ := hcov x hx
  have hxcell' : x ∈ (cell' ch).toSet := by
    refine (mem_equalize_foldl ch.1 ch.2.2.2 x).2 ⟨hxch, ?_⟩
    intro a ha
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 ha
    have hi' : i < hyps.length := by
      have := hlen ch hch
      omega
    have hsome : hyps[i]? = some (hyps[i]) := List.getElem?_eq_getElem hi'
    have heq := hhy ch hch i (hyps[i]) hsome x hxch
    have : hyps[i] x = 0 := hhyps0 _ (List.getElem_mem hi')
    have hget : (ch.2.2.2[i]?).getD (AffineFn.const 0) = ch.2.2.2[i] := by
      simp [List.getElem?_eq_getElem hi]
    simpa [heq, hget] using this
  have hfval := (hfg ch hch x hxch).1
  have hgval := (hfg ch hch x hxch).2
  have := hN ch hch x hxcell'
  simpa [hfval, hgval] using this

end ContinuousFOL
