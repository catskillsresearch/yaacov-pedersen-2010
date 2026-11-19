/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Bounded polyhedral cells in the unit cube, and a uniform slope bound for a
pair of affine maps that vanish together on a cell.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.AffineFn
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

noncomputable section
open Classical
open Set

namespace ContinuousFOL

/-- The unit cube in `Fin n → ℝ`. -/
def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ x i ∧ x i ≤ 1}

lemma unitCube_eq_pi (n : ℕ) :
    unitCube n = Set.pi Set.univ fun _ => Icc (0 : ℝ) 1 := by
  ext x
  constructor
  · intro hx i hi
    exact mem_Icc.2 (hx i)
  · intro hx i
    exact mem_Icc.1 (hx i (mem_univ i))

lemma isCompact_unitCube (n : ℕ) : IsCompact (unitCube n) := by
  rw [unitCube_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc

lemma convex_unitCube (n : ℕ) : Convex ℝ (unitCube n) := by
  rw [unitCube_eq_pi]
  exact convex_pi fun _ _ => convex_Icc 0 1

/-- Cube facets as affine inequalities `x i ≤ 1` and `-x i ≤ 0`. -/
def cubeConstraints (n : ℕ) : Finset (AffineFn n) :=
  Finset.univ.image (fun i => (AffineFn.proj i).sub (AffineFn.const 1)) ∪
    Finset.univ.image (fun i => (AffineFn.proj i).neg)

lemma cubeConstraints_le {n : ℕ} {x : Fin n → ℝ} :
    (∀ a ∈ cubeConstraints n, a.eval x ≤ 0) ↔ ∀ i, 0 ≤ x i ∧ x i ≤ 1 := by
  constructor
  · intro h i
    have hhi : ((AffineFn.proj i).sub (AffineFn.const 1)).eval x ≤ 0 := by
      apply h
      simp [cubeConstraints]
    have hlo : ((AffineFn.proj i).neg).eval x ≤ 0 := by
      apply h
      simp [cubeConstraints]
    simp [AffineFn.eval_sub, AffineFn.eval_proj, AffineFn.eval_const, AffineFn.eval_neg] at hhi hlo
    constructor <;> linarith
  · intro hx a ha
    simp only [cubeConstraints, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
      true_and] at ha
    rcases ha with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · have := hx i
      simp [AffineFn.eval_sub, AffineFn.eval_proj, AffineFn.eval_const]
      linarith
    · have := hx i
      simp [AffineFn.eval_neg, AffineFn.eval_proj]
      linarith

/-- A polyhedral cell: the unit cube cut by finitely many affine inequalities `a ≤ 0`. -/
structure PolyCell (n : ℕ) where
  ineq : Finset (AffineFn n)

namespace PolyCell

variable {n : ℕ}

def constraints (C : PolyCell n) : Finset (AffineFn n) :=
  C.ineq ∪ cubeConstraints n

def Mem (C : PolyCell n) (x : Fin n → ℝ) : Prop :=
  ∀ a ∈ C.constraints, a.eval x ≤ 0

def toSet (C : PolyCell n) : Set (Fin n → ℝ) :=
  {x | C.Mem x}

lemma mem_unitCube {C : PolyCell n} {x : Fin n → ℝ} (hx : x ∈ C.toSet) :
    x ∈ unitCube n :=
  (cubeConstraints_le (x := x)).1 fun a ha =>
    hx a (Finset.mem_union.2 (Or.inr ha))

lemma toSet_subset_unitCube (C : PolyCell n) : C.toSet ⊆ unitCube n :=
  fun _ hx => mem_unitCube hx

lemma isClosed_toSet (C : PolyCell n) : IsClosed C.toSet := by
  have hhalf (a : AffineFn n) : IsClosed {x : Fin n → ℝ | a.eval x ≤ 0} :=
    isClosed_le a.continuous continuous_const
  have : C.toSet = ⋂ a ∈ C.constraints, {x : Fin n → ℝ | a.eval x ≤ 0} := by
    ext x
    simp [toSet, Mem]
  rw [this]
  exact isClosed_biInter fun a _ => hhalf a

lemma isCompact_toSet (C : PolyCell n) : IsCompact C.toSet :=
  (isCompact_unitCube n).of_isClosed_subset C.isClosed_toSet C.toSet_subset_unitCube

lemma convex_toSet (C : PolyCell n) : Convex ℝ C.toSet := by
  intro x hx y hy a b ha hb hab f hf
  have hx' := hx f hf
  have hy' := hy f hf
  have : f.eval (a • x + b • y) = a * f.eval x + b * f.eval y :=
    AffineFn.eval_affineCombo f a b x y hab
  change f.eval (a • x + b • y) ≤ 0
  rw [this]
  nlinarith

/-- The inequalities tight at `x`. -/
def tightSet (C : PolyCell n) (x : Fin n → ℝ) : Finset (AffineFn n) :=
  C.constraints.filter (fun a => a.eval x = 0)

lemma tightSet_subset (C : PolyCell n) (x : Fin n → ℝ) :
    C.tightSet x ⊆ C.constraints :=
  Finset.filter_subset _ _

/-- Distinct extreme points have distinct tight constraint sets. -/
lemma tightSet_injOn_extremePoints (C : PolyCell n) :
    InjOn C.tightSet (C.toSet.extremePoints ℝ) := by
  intro x hxext y hyext htight
  have hx : x ∈ C.toSet := mem_of_mem_of_subset hxext extremePoints_subset
  have hy : y ∈ C.toSet := mem_of_mem_of_subset hyext extremePoints_subset
  by_contra hne
  let d : Fin n → ℝ := fun i => y i - x i
  have hd : d ≠ 0 := by
    intro hd0
    apply hne
    funext i
    have : y i - x i = 0 := congrFun hd0 i
    linarith
  have hline (t : ℝ) (a : AffineFn n) :
      a.eval (fun i => x i + t * d i) = a.eval x + t * (a.eval y - a.eval x) := by
    simpa [d] using AffineFn.eval_line a x y t
  have htight_iff : ∀ a ∈ C.constraints, a.eval x = 0 ↔ a.eval y = 0 := by
    intro a ha
    have : (a ∈ C.tightSet x) ↔ (a ∈ C.tightSet y) := by
      simp only [htight]
    simpa [tightSet, ha] using this
  let loose : Finset (AffineFn n) := C.constraints.filter (fun a => a.eval x < 0)
  -- Slack and a Lipschitz bound for the loose inequalities.
  have hex : ∃ ε : ℝ, 0 < ε ∧ ∀ t : ℝ, |t| < ε → (fun i => x i + t * d i) ∈ C.toSet := by
    by_cases hlo : loose.Nonempty
    · let slack := loose.inf' hlo (fun a => -(a.eval x))
      let M := loose.sup' hlo (fun a => |a.eval y - a.eval x|)
      have hslack : 0 < slack := by
        obtain ⟨a0, ha0, hseq⟩ :=
          Finset.exists_mem_eq_inf' (s := loose) hlo (fun a => -(a.eval x))
        have : a0.eval x < 0 := (Finset.mem_filter.mp ha0).2
        have : 0 < -(a0.eval x) := by linarith
        simp [slack, hseq, this]
      have hM0 : 0 ≤ M := by
        obtain ⟨a0, ha0⟩ := hlo
        exact le_trans (abs_nonneg _) (Finset.le_sup' (f := fun a => |a.eval y - a.eval x|) ha0)
      let ε : ℝ := min (1 / 2) (slack / (M + 1))
      have hεpos : 0 < ε := by
        have : 0 < slack / (M + 1) := div_pos hslack (by linarith)
        exact lt_min (by norm_num) this
      refine ⟨ε, hεpos, ?_⟩
      intro t ht f hf
      rw [hline]
      by_cases h0 : f.eval x = 0
      · have hy0 : f.eval y = 0 := (htight_iff f hf).1 h0
        simp [h0, hy0]
      · have hlt : f.eval x < 0 := lt_of_le_of_ne (hx f hf) h0
        have hfloose : f ∈ loose := Finset.mem_filter.2 ⟨hf, hlt⟩
        have hslack_le : slack ≤ -(f.eval x) :=
          Finset.inf'_le (fun a => -(a.eval x)) hfloose
        have habs : |f.eval y - f.eval x| ≤ M :=
          Finset.le_sup' (f := fun a => |a.eval y - a.eval x|) hfloose
        have hden : 0 < M + 1 := by linarith
        have ht' : |t| < slack / (M + 1) :=
          lt_of_lt_of_le ht (min_le_right _ _)
        have htM : |t| * (M + 1) < slack := by
          rwa [lt_div_iff₀ hden] at ht'
        have hbound : |t| * |f.eval y - f.eval x| < slack := by
          nlinarith [abs_nonneg t, habs]
        have : f.eval x + t * (f.eval y - f.eval x) ≤
            f.eval x + |t * (f.eval y - f.eval x)| := by
          linarith [le_abs_self (t * (f.eval y - f.eval x))]
        have : |t * (f.eval y - f.eval x)| = |t| * |f.eval y - f.eval x| :=
          abs_mul t _
        linarith
    · refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
      intro t ht f hf
      rw [hline]
      have h0 : f.eval x = 0 := by
        have hle : f.eval x ≤ 0 := hx f hf
        have hnlt : ¬ f.eval x < 0 := by
          intro hlt
          exact hlo ⟨f, Finset.mem_filter.2 ⟨hf, hlt⟩⟩
        exact le_antisymm hle (le_of_not_gt hnlt)
      have hy0 : f.eval y = 0 := (htight_iff f hf).1 h0
      simp [h0, hy0]
  obtain ⟨ε, hεpos, hseg⟩ := hex
  let t0 : ℝ := ε / 2
  have ht0 : 0 < t0 := half_pos hεpos
  have ht0lt : |t0| < ε := by
    have ht0lt' : t0 < ε := by dsimp [t0]; linarith
    simpa [abs_of_pos ht0] using ht0lt'
  let p : Fin n → ℝ := fun i => x i + (-t0) * d i
  let q : Fin n → ℝ := fun i => x i + t0 * d i
  have hp : p ∈ C.toSet := by
    have : |(-t0)| < ε := by simpa [abs_neg] using ht0lt
    exact hseg (-t0) this
  have hq : q ∈ C.toSet := hseg t0 ht0lt
  have hxmid : x ∈ openSegment ℝ p q := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    funext i
    change (1 / 2) * p i + (1 / 2) * q i = x i
    dsimp [p, q]
    ring
  have hpx : p ≠ x := by
    intro hpq
    have hzero : ∀ i, (-t0) * d i = 0 := by
      intro i
      have := congrFun hpq i
      dsimp [p] at this
      linarith
    have : d = 0 := by
      funext i
      have hi := hzero i
      have : t0 * d i = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left (ne_of_gt ht0)
    exact hd this
  have hxleft := (mem_extremePoints_iff_left.mp hxext).2 p hp q hq hxmid
  exact hpx hxleft

lemma finite_extremePoints (C : PolyCell n) :
    (C.toSet.extremePoints ℝ).Finite := by
  refine Finite.of_injOn (f := C.tightSet)
    (t := (C.constraints.powerset : Set (Finset (AffineFn n))))
    ?_ (tightSet_injOn_extremePoints C) C.constraints.powerset.finite_toSet
  intro x hx
  exact Finset.mem_powerset.mpr (tightSet_subset C x)

/-- The maximizer of an affine function on a nonempty cell may be taken extreme. -/
lemma exists_extreme_isMaxOn (C : PolyCell n) (hC : C.toSet.Nonempty) (a : AffineFn n) :
    ∃ x ∈ C.toSet.extremePoints ℝ, IsMaxOn a.eval C.toSet x := by
  obtain ⟨y, hy, hymax⟩ :=
    C.isCompact_toSet.exists_isMaxOn hC a.continuous.continuousOn
  let M : Set (Fin n → ℝ) := {z ∈ C.toSet | a.eval z = a.eval y}
  have hMsub : M ⊆ C.toSet := fun _ hz => hz.1
  have hMcl : IsClosed M := by
    have : M = C.toSet ∩ a.eval ⁻¹' {a.eval y} := by
      ext z
      simp [M]
    rw [this]
    exact C.isClosed_toSet.inter (isClosed_singleton.preimage a.continuous)
  have hMcp : IsCompact M := C.isCompact_toSet.of_isClosed_subset hMcl hMsub
  have hMne : M.Nonempty := ⟨y, hy, rfl⟩
  have hMconv : Convex ℝ M := by
    intro p hp q hq s t hs ht hst
    refine ⟨C.convex_toSet hp.1 hq.1 hs ht hst, ?_⟩
    have heval := AffineFn.eval_affineCombo a s t p q hst
    change a.eval (s • p + t • q) = a.eval y
    rw [heval, hp.2, hq.2]
    calc
      s * a.eval y + t * a.eval y = (s + t) * a.eval y := by ring
      _ = a.eval y := by rw [hst, one_mul]
  obtain ⟨z, hzMext⟩ := hMcp.extremePoints_nonempty hMne
  have hzM : z ∈ M := extremePoints_subset hzMext
  have hface : IsExtreme ℝ C.toSet M := by
    refine ⟨hMsub, ?_⟩
    intro p hpC q hqC z' hz'M hzseg
    have hz'Max : a.eval z' = a.eval y := hz'M.2
    obtain ⟨s, t, hs, ht, hst, rfl⟩ := hzseg
    have heval := AffineFn.eval_affineCombo a s t p q hst
    have hpmax : a.eval p ≤ a.eval y := hymax hpC
    have hqmax : a.eval q ≤ a.eval y := hymax hqC
    have heqp : a.eval p = a.eval y := by
      apply le_antisymm hpmax
      by_contra hne
      have hlt : a.eval p < a.eval y := not_le.mp hne
      have : s * a.eval p + t * a.eval q < s * a.eval y + t * a.eval y := by
        nlinarith
      have : s * a.eval y + t * a.eval y = a.eval y := by
        calc
          s * a.eval y + t * a.eval y = (s + t) * a.eval y := by ring
          _ = a.eval y := by rw [hst, one_mul]
      linarith [heval, hz'Max]
    exact ⟨hpC, heqp⟩
  have hzext : z ∈ C.toSet.extremePoints ℝ :=
    hface.extremePoints_subset_extremePoints hzMext
  refine ⟨z, hzext, fun w hw => ?_⟩
  calc
    a.eval w ≤ a.eval y := hymax hw
    _ = a.eval z := hzM.2.symm

/-- If two affine maps vanish together on a polyhedral cell, and the
denominator is nonnegative there, their ratio is bounded. -/
lemma affine_ratio_bound (C : PolyCell n) (f g : AffineFn n)
    (hg0 : ∀ x ∈ C.toSet, 0 ≤ g.eval x)
    (hvan : ∀ x ∈ C.toSet, g.eval x = 0 → f.eval x = 0) :
    ∃ N : ℕ, ∀ x ∈ C.toSet, f.eval x ≤ (N : ℝ) * g.eval x := by
  rcases eq_empty_or_nonempty C.toSet with hempty | hne
  · exact ⟨0, fun x hx => by simp [hempty] at hx⟩
  have hfin := C.finite_extremePoints
  let V := hfin.toFinset
  let N : ℕ := V.sup fun x => if g.eval x = 0 then 0 else Nat.ceil (f.eval x / g.eval x)
  have hNvert : ∀ x ∈ V, f.eval x ≤ (N : ℝ) * g.eval x := by
    intro x hx
    have hxC : x ∈ C.toSet := extremePoints_subset (hfin.mem_toFinset.mp hx)
    by_cases hg : g.eval x = 0
    · have hf := hvan x hxC hg
      simp [hf, hg]
    · have hgpos : 0 < g.eval x := lt_of_le_of_ne (hg0 x hxC) (Ne.symm hg)
      have hle :
          (if g.eval x = 0 then 0 else Nat.ceil (f.eval x / g.eval x)) ≤ N :=
        Finset.le_sup (f := fun y =>
          if g.eval y = 0 then 0 else Nat.ceil (f.eval y / g.eval y)) hx
      have hle' : (Nat.ceil (f.eval x / g.eval x) : ℕ) ≤ N := by simpa [hg] using hle
      have hceil : f.eval x / g.eval x ≤ (Nat.ceil (f.eval x / g.eval x) : ℝ) :=
        Nat.le_ceil _
      have : f.eval x / g.eval x ≤ (N : ℝ) :=
        le_trans hceil (by exact_mod_cast hle')
      have := mul_le_mul_of_nonneg_right this (le_of_lt hgpos)
      rwa [div_mul_cancel₀ _ hg] at this
  refine ⟨N, ?_⟩
  intro z hz
  let hfn : AffineFn n := f.sub (g.smul (N : ℝ))
  obtain ⟨x, hxext, hmax⟩ := C.exists_extreme_isMaxOn hne hfn
  have hxV : x ∈ V := hfin.mem_toFinset.mpr hxext
  have hveq : hfn.eval x = f.eval x - (N : ℝ) * g.eval x := by
    simp [hfn, AffineFn.eval_sub, AffineFn.eval_smul]
  have hleq : hfn.eval x ≤ 0 := by
    have := hNvert x hxV
    linarith
  have hzeq : hfn.eval z = f.eval z - (N : ℝ) * g.eval z := by
    simp [hfn, AffineFn.eval_sub, AffineFn.eval_smul]
  have : hfn.eval z ≤ hfn.eval x := hmax hz
  linarith

end PolyCell

end ContinuousFOL
