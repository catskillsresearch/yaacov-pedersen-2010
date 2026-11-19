/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Definition 8.8 / Lemmas 8.6, 8.11–8.12 / Theorem 8.10; vision.md pages 18–20
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.LanguageAndSemantics.FormulaRank
public import ContinuousFOL.LanguageAndSemantics.FormulaEquiv
public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeSubst
public import ContinuousFOL.Essentials.ConsistentAdjoin
public import ContinuousFOL.Essentials.InconsistentIffProvableOne
public import ContinuousFOL.Essentials.ProvableQMono
public import ContinuousFOL.Group1Axioms.DyadicCode.Val
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Basic
public import Mathlib.Order.Zorn

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Definition 8.8: Maximal consistent set of formulae in continuous first-order logic. -/
structure MaximalConsistent {L : Signature} (Δ : Set (Formula L)) : Prop where
  consistent : ConsistentQ Δ
  archimedean : ∀ φ, (∀ n : ℕ, ProvableQ Δ (.tsub φ (Formula.pow2Neg L n))) → φ ∈ Δ
  comparable  : ∀ φ ψ, Formula.tsub φ ψ ∈ Δ ∨ Formula.tsub ψ φ ∈ Δ

namespace MaximalConsistent

/-- Remark 8.9: Deductive closure of maximal consistent sets. -/
lemma mem_iff_provable {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (φ : Formula L) :
    φ ∈ Δ ↔ ProvableQ Δ φ := by
  constructor
  · exact fun h => .hyp h
  · intro hprov
    exact hmc.archimedean φ fun n =>
      ProvableQ.mp hprov (ProvableQ.ax0 (.A1 φ (Formula.pow2Neg L n)))

end MaximalConsistent

/-- From `⊢ ½φ` infer `⊢ φ`, by (A6) and two applications of modus ponens. -/
lemma ProvableQ.of_half {L : Signature} {Γ : Set (Formula L)} {φ : Formula L}
    (h : ProvableQ Γ (.half φ)) : ProvableQ Γ φ := by
  have hA6 : ProvableQ Γ (.tsub (.tsub φ (.half φ)) (.half φ)) :=
    ProvableQ.ax0 (.A6 φ)
  exact ProvableQ.mp h (ProvableQ.mp h hA6)

/-- A proof of the constant `2^{-n}` yields a proof of `1`. -/
lemma ProvableQ.one_of_pow2Neg {L : Signature} {Γ : Set (Formula L)} (n : ℕ)
    (h : ProvableQ Γ (Formula.pow2Neg L n)) : ProvableQ Γ (Formula.one L) := by
  induction n with
  | zero =>
    simpa [Formula.pow2Neg, DyadicCode.pow2Neg, Formula.dyadic] using h
  | succ n ih =>
    have hhalf : ProvableQ Γ (.half (Formula.pow2Neg L n)) := by
      simpa [Formula.pow2Neg, DyadicCode.pow2Neg, Formula.dyadic] using h
    exact ih (ProvableQ.of_half hhalf)

/-- Congruence of `∸` under provable two-way `∸`-bounds (cf. proof of Lemma 8.3). -/
lemma ProvableQ.tsub_congr0 {L : Signature} {α α' β β' : Formula L}
    (hα₁ : ProvableQ (∅ : Set (Formula L)) (.tsub α α'))
    (hα₂ : ProvableQ (∅ : Set (Formula L)) (.tsub α' α))
    (hβ₁ : ProvableQ (∅ : Set (Formula L)) (.tsub β β'))
    (hβ₂ : ProvableQ (∅ : Set (Formula L)) (.tsub β' β)) :
    ProvableQ ∅ (.tsub (.tsub α β) (.tsub α' β')) ∧
    ProvableQ ∅ (.tsub (.tsub α' β') (.tsub α β)) :=
  ⟨ProvableQ.mp hα₁ (ProvableQ.mp hβ₂
      (ProvableQ.tsub_cong_schema (Γ := (∅ : Set (Formula L))) β' β α' α)),
    ProvableQ.mp hα₂ (ProvableQ.mp hβ₁
      (ProvableQ.tsub_cong_schema (Γ := (∅ : Set (Formula L))) β β' α α'))⟩

lemma Formula.boundSubst_of_not_mem_boundVars {L : Signature} (φ : Formula L) {x y : Var}
    (hx : x ∉ φ.boundVars) : φ.boundSubst y x = φ := by
  induction φ with
  | rel _ _ => rfl
  | tsub α β ihα ihβ =>
    simp only [Formula.boundVars, Finset.mem_union, not_or] at hx
    simp only [Formula.boundSubst, ihα hx.1, ihβ hx.2]
  | neg α ih => simp only [Formula.boundSubst, ih hx]
  | half α ih => simp only [Formula.boundSubst, ih hx]
  | sup z α ih =>
    simp only [Formula.boundVars, Finset.mem_insert, not_or] at hx
    have hzx : ¬ z = x := fun h => hx.1 h.symm
    simp only [Formula.boundSubst, ih hx.2, eq_false hzx, ↓reduceIte]

lemma Formula.rank_freeSubst {L : Signature} (φ : Formula L) (t : Term L) (x : Var) :
    (φ.freeSubst t x).rank = φ.rank := by
  induction φ with
  | rel _ _ => rfl
  | tsub α β ihα ihβ => simp [Formula.freeSubst, Formula.rank, ihα, ihβ]
  | neg α ih => simp [Formula.freeSubst, Formula.rank, ih]
  | half α ih => simp [Formula.freeSubst, Formula.rank, ih]
  | sup z α ih => by_cases h : z = x <;> simp [Formula.freeSubst, Formula.rank, h, ih]

lemma Formula.rank_renameBound {L : Signature} (avoid : Finset Var) (φ : Formula L) :
    (φ.renameBound avoid).rank = φ.rank := by
  induction φ with
  | rel _ _ => rfl
  | tsub α β ihα ihβ => simp [Formula.renameBound, Formula.rank, ihα, ihβ]
  | neg α ih => simp [Formula.renameBound, Formula.rank, ih]
  | half α ih => simp [Formula.renameBound, Formula.rank, ih]
  | sup z α ih =>
    simp only [Formula.renameBound]
    split_ifs <;> simp [Formula.rank, Formula.rank_freeSubst, ih]

lemma Formula.freeSubstCorrect_of_disjoint {L : Signature} (φ : Formula L) (t : Term L)
    (x : Var) (h : Disjoint t.vars φ.boundVars) : φ.FreeSubstCorrect t x := by
  induction φ with
  | rel _ _ => simp [Formula.FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    simp only [Formula.boundVars, Finset.disjoint_union_right] at h
    exact ⟨ihα h.1, ihβ h.2⟩
  | neg α ih => exact ih h
  | half α ih => exact ih h
  | sup z α ih =>
    simp only [Formula.boundVars, Finset.disjoint_insert_right] at h
    unfold Formula.FreeSubstCorrect
    by_cases hz : z = x
    · simp [hz]
    · simp only [eq_false hz, ↓reduceIte]
      exact ⟨fun _ => h.1, ih h.2⟩

/-- Renaming bound variables (Lemma 6.4's `renameBound`) is provably two-way bounded,
    by repeated applications of Lemma 8.3 and (A2) (cf. proof of Lemma 8.11). -/
lemma ProvableQ.renameBound {L : Signature} (avoid : Finset Var) (φ : Formula L) :
    ProvableQ (∅ : Set (Formula L)) (.tsub φ (φ.renameBound avoid)) ∧
    ProvableQ ∅ (.tsub (φ.renameBound avoid) φ) := by
  induction φ with
  | rel _ _ => exact ⟨ProvableQ.imp_refl _, ProvableQ.imp_refl _⟩
  | tsub α β ihα ihβ =>
    simp only [Formula.renameBound]
    exact ProvableQ.tsub_congr0 ihα.1 ihα.2 ihβ.1 ihβ.2
  | neg α ih =>
    simp only [Formula.renameBound]
    exact ⟨ProvableQ.neg_tsub ih.2, ProvableQ.neg_tsub ih.1⟩
  | half α ih =>
    simp only [Formula.renameBound]
    exact ⟨ProvableQ.half_mono ih.1, ProvableQ.half_mono ih.2⟩
  | sup z α ih =>
    simp only [Formula.renameBound]
    split_ifs with hz
    · set α' := α.renameBound avoid with hα'
      set y := freshAbove (avoid ∪ α'.allVars) with hy
      have hyfresh := freshAbove_not_mem (avoid ∪ α'.allVars)
      rw [← hy] at hyfresh
      have hyz : y ≠ z := fun h => hyfresh (Finset.mem_union_left _ (h ▸ hz))
      have hyall : y ∉ (Formula.sup z α').allVars := by
        simp only [Formula.allVars, Finset.mem_insert, not_or]
        exact ⟨hyz, fun h => hyfresh (Finset.mem_union_right _ h)⟩
      have hzb : z ∉ α'.boundVars := fun h =>
        Finset.disjoint_left.mp (Formula.boundVars_renameBound avoid α) hz h
      obtain ⟨b1, b2⟩ := provable_bound_subst (Formula.sup z α') z y hyall
      have hb : (Formula.sup z α').boundSubst y z = .sup y (α'.freeSubst (.var y) z) := by
        simp only [Formula.boundSubst, ↓reduceIte, Formula.boundSubst_of_not_mem_boundVars α' hzb]
      rw [hb] at b1 b2
      exact ⟨ProvableQ.tsub_trans (ProvableQ.sup_cong0 z ih.1) b1,
        ProvableQ.tsub_trans b2 (ProvableQ.sup_cong0 z ih.2)⟩
    · exact ⟨ProvableQ.sup_cong0 z ih.1, ProvableQ.sup_cong0 z ih.2⟩

/-- Helper for Lemma 8.11 (used by the truth lemma): the paper's conclusion together with the
facts its proof provides, namely `rank φ' = rank φ` and correctness of `φ'[t/x]`.
Not a paper statement; see `maximal_consistent_sup_instantiate`. -/
theorem maximal_consistent_sup_instantiate_aux {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (t : Term L) (x : Var) (φ : Formula L) (p : DyadicCode)
    (hmem : Formula.tsub (.sup x φ) (Formula.dyadic L p) ∈ Δ) :
    ∃ φ' : Formula L, (φ ≡ᶠ φ') ∧ φ'.rank = φ.rank ∧
      Formula.FreeSubstCorrect φ' t x ∧
      Formula.tsub (φ'.freeSubst t x) (Formula.dyadic L p) ∈ Δ := by
  -- Lemma 6.4: rename bound variables of `φ` off the variables of `t`.
  refine ⟨φ.renameBound t.vars, fun M σ => (Formula.eval_renameBound M t.vars φ σ).symm,
    Formula.rank_renameBound _ _,
    Formula.freeSubstCorrect_of_disjoint _ t x (Formula.boundVars_renameBound t.vars φ), ?_⟩
  have hcorr : (φ.renameBound t.vars).FreeSubstCorrect t x :=
    Formula.freeSubstCorrect_of_disjoint _ t x (Formula.boundVars_renameBound t.vars φ)
  -- Lemma 8.3 + (A2), Generalization, (A7): `⊢ sup_x φ' ∸ sup_x φ`.
  have h1 : ProvableQ Δ (.tsub (.sup x (φ.renameBound t.vars)) (.sup x φ)) :=
    (ProvableQ.sup_cong0 x (ProvableQ.renameBound t.vars φ).2).mono (Set.empty_subset _)
  -- (A8): `⊢ φ'[t/x] ∸ sup_x φ'`.
  have h2 : ProvableQ Δ (.tsub ((φ.renameBound t.vars).freeSubst t x)
      (.sup x (φ.renameBound t.vars))) :=
    ProvableQ.ax0 (.A8 x t _ hcorr)
  have h3 : ProvableQ Δ (.tsub (.sup x φ) (Formula.dyadic L p)) := .hyp hmem
  exact (hmc.mem_iff_provable _).mpr
    (ProvableQ.tsub_trans (ProvableQ.tsub_trans h2 h1) h3)

/-- Lemma 8.11: Let `Γ ⊆ For(𝓛)`, let `Δ` be a maximal consistent set of formulae containing
`Γ`, let `t` be a term, and let `p ∈ 𝔻`. Then if `sup_x φ ∸ p ∈ Δ`, there is a formula `φ'`
such that `φ ≡ φ'` and `φ'[t/x] ∸ p ∈ Δ`. -/
theorem maximal_consistent_sup_instantiate {L : Signature} (Γ : Set (Formula L))
    {Δ : Set (Formula L)} (hmc : MaximalConsistent Δ) (_hΓΔ : Γ ⊆ Δ) (t : Term L)
    (p : DyadicCode) (x : Var) (φ : Formula L) :
    Formula.tsub (.sup x φ) (Formula.dyadic L p) ∈ Δ →
      ∃ φ' : Formula L, (φ ≡ᶠ φ') ∧
        Formula.tsub (φ'.freeSubst t x) (Formula.dyadic L p) ∈ Δ := by
  intro hmem
  obtain ⟨φ', heq, -, -, hmem'⟩ := maximal_consistent_sup_instantiate_aux hmc t x φ p hmem
  exact ⟨φ', heq, hmem'⟩

/-- CL: `⊢ 0 ∸ φ`. -/
lemma ProvableQ.zero_tsub {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) :
    ProvableQ Γ (.tsub (Formula.dyadic L .zero) φ) := by
  have h := CLPropForm.toFormula_provable_of_valid (Γ := Γ) ![φ, Formula.defaultAtom L]
    (.tsub (CLPropForm.dyadic (.var 1) .zero) (.var 0)) (by
      intro v hv
      obtain ⟨h0, _⟩ := hv 0
      simp only [CLPropForm.eval, CLPropForm.eval_dyadic, DyadicCode.val_zero, tsubR]
      exact max_eq_right (by linarith))
  have hform : (CLPropForm.tsub (CLPropForm.dyadic (.var 1) .zero) (.var 0)).toFormula
      ![φ, Formula.defaultAtom L] = .tsub (Formula.dyadic L .zero) φ := by
    simp only [CLPropForm.toFormula, CLPropForm.toFormula_dyadic ![φ, Formula.defaultAtom L] 1 rfl]
    rfl
  rw [hform] at h
  exact h

/-- A proof of a dyadic constant of positive value yields a proof of `1` (CL, Fact 4.5). -/
lemma ProvableQ.one_of_dyadic_pos {L : Signature} {Γ : Set (Formula L)} (d : DyadicCode)
    (hd : 0 < d.val) (h : ProvableQ Γ (Formula.dyadic L d)) : ProvableQ Γ (Formula.one L) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / d.val)
  have hk' : 1 ≤ (k : ℝ) * d.val := by rw [div_le_iff₀ hd] at hk; exact hk
  have ht := CLPropForm.toFormula_provable_of_valid (Γ := Γ) ![Formula.defaultAtom L]
    (CLPropForm.iterSub (CLPropForm.one (.var 0)) (CLPropForm.dyadic (.var 0) d) k) (by
      intro v _
      rw [CLPropForm.eval_iterSub, CLPropForm.eval_dyadic]
      have hone : (CLPropForm.one (.var (0 : Fin 1))).eval v = 1 := by
        simp [CLPropForm.one, CLPropForm.eval, tsubR]
      rw [hone, iterSubR_eq zero_le_one hd.le]
      exact max_eq_right (by linarith))
  have hform : (CLPropForm.iterSub (CLPropForm.one (.var 0)) (CLPropForm.dyadic (.var 0) d)
      k).toFormula ![Formula.defaultAtom L] =
        Formula.iterSub (Formula.one L) (Formula.dyadic L d) k := by
    rw [CLPropForm.toFormula_iterSub, CLPropForm.toFormula_dyadic _ 0 rfl]
    simp [CLPropForm.one, CLPropForm.toFormula, Formula.one]
  rw [hform] at ht
  exact ProvableQ.cancel_iterSub h k ht

/-- Lemma 8.12: Dedekind cut equality of dyadic lower and upper bounds in `Δ`. -/
theorem maximal_consistent_sup_eq_inf {L : Signature} {Γ Δ : Set (Formula L)}
    (_hcons : ConsistentQ Γ) (hmc : MaximalConsistent Δ) (_hΓΔ : Γ ⊆ Δ)
    (φ : Formula L) :
    sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ Formula.tsub (Formula.dyadic L p) φ ∈ Δ} =
    sInf {r : ℝ | ∃ q : DyadicCode, r = q.val ∧ Formula.tsub φ (Formula.dyadic L q) ∈ Δ} := by
  set A := {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ Formula.tsub (Formula.dyadic L p) φ ∈ Δ}
  set B := {r : ℝ | ∃ q : DyadicCode, r = q.val ∧ Formula.tsub φ (Formula.dyadic L q) ∈ Δ}
  have h0A : (0 : ℝ) ∈ A :=
    ⟨.zero, DyadicCode.val_zero.symm, (hmc.mem_iff_provable _).mpr (ProvableQ.zero_tsub Δ φ)⟩
  have h1B : (1 : ℝ) ∈ B :=
    ⟨.one, DyadicCode.val_one.symm, (hmc.mem_iff_provable _).mpr (ProvableQ.tsub_one Δ φ)⟩
  -- Consistency: every lower bound `p` lies below every upper bound `q`.
  have hAB : ∀ a ∈ A, ∀ b ∈ B, a ≤ b := by
    rintro a ⟨p, rfl, hp⟩ b ⟨q, rfl, hq⟩
    by_contra hlt
    push Not at hlt
    have hpq : ProvableQ Δ (Formula.dyadic L (.tsub p q)) :=
      ProvableQ.tsub_trans (.hyp hp) (.hyp hq)
    have hpos : 0 < (DyadicCode.tsub p q).val := by
      simp only [DyadicCode.val, tsubR]
      exact lt_max_of_lt_left (by linarith)
    exact (inconsistent_iff_provable_one Δ).mpr
      (ProvableQ.one_of_dyadic_pos (.tsub p q) hpos hpq) hmc.consistent
  have hAbdd : BddAbove A := ⟨1, by rintro a ⟨p, rfl, -⟩; exact (DyadicCode.val_mem_Icc p).2⟩
  have hBbdd : BddBelow B := ⟨0, by rintro b ⟨q, rfl, -⟩; exact (DyadicCode.val_mem_Icc q).1⟩
  apply le_antisymm
  · exact csSup_le ⟨0, h0A⟩ fun a ha => le_csInf ⟨1, h1B⟩ fun b hb => hAB a ha b hb
  · -- Comparability + density of dyadics (Remark 3.4) close any gap.
    by_contra hlt
    push Not at hlt
    have hx : 0 ≤ sSup A := le_csSup hAbdd h0A
    have hy : sInf B ≤ 1 := csInf_le hBbdd h1B
    obtain ⟨r, hr1, hr2⟩ := DyadicCode.dense_in_Icc hx hy hlt
    rcases hmc.comparable (Formula.dyadic L r) φ with h | h
    · exact absurd (le_csSup hAbdd ⟨r, rfl, h⟩) (not_le.mpr hr1)
    · exact absurd (csInf_le hBbdd ⟨r, rfl, h⟩) (not_le.mpr hr2)

/-- Helper: Lemma 8.6 with the right-hand side packaged as `MaximalConsistent`. -/
theorem maximal_in_consistent_extensions_iff_maximalConsistent
    {L : Signature} {Γ Δ : Set (Formula L)} (_hΓ : ConsistentQ Γ) :
    Maximal (fun Γ' => Γ ⊆ Γ' ∧ ConsistentQ Γ') Δ ↔ (Γ ⊆ Δ ∧ MaximalConsistent Δ) := by
  constructor
  · rintro ⟨⟨hsub, hcons⟩, hmax⟩
    refine ⟨hsub, ⟨hcons, ?_, ?_⟩⟩
    · intro φ happrox
      have hcons' := consistent_adjoin_approx hcons φ happrox
      have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hcons'⟩ Set.subset_union_left
      exact heq (Set.mem_union_right _ (Set.mem_singleton φ))
    · intro φ ψ
      rcases consistent_adjoin_comparable hcons φ ψ with hc₁ | hc₂
      · left
        have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hc₁⟩ Set.subset_union_left
        exact heq (Set.mem_union_right _ (Set.mem_singleton _))
      · right
        have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hc₂⟩ Set.subset_union_left
        exact heq (Set.mem_union_right _ (Set.mem_singleton _))
  · rintro ⟨hsub, hmc⟩
    refine ⟨⟨hsub, hmc.consistent⟩, ?_⟩
    rintro Γ' ⟨_hΓ'sub, hΓ'cons⟩ hΔΓ' φ hφ
    apply hmc.archimedean
    intro n
    -- Comparability: `φ ∸ 2^{-n} ∈ Δ` or `2^{-n} ∸ φ ∈ Δ`.
    -- The second alternative, with `φ ∈ Γ' ⊇ Δ`, proves `2^{-n}` and hence `1`.
    rcases hmc.comparable φ (Formula.pow2Neg L n) with hle | hge
    · exact .hyp hle
    · exfalso
      have hpow : ProvableQ Γ' (Formula.pow2Neg L n) :=
        ProvableQ.mp (.hyp hφ) (.hyp (hΔΓ' hge))
      exact (inconsistent_iff_provable_one Γ').mpr
        (ProvableQ.one_of_pow2Neg n hpow) hΓ'cons

/-- Lemma 8.6: `Δ` is maximal in `E(Γ)` iff the paper's clauses (i)–(iii) hold. -/
theorem maximal_in_consistent_extensions_iff {L : Signature} {Γ Δ : Set (Formula L)}
    (hΓ : ConsistentQ Γ) :
    Maximal (fun Γ' => Γ ⊆ Γ' ∧ ConsistentQ Γ') Δ ↔
      (Γ ⊆ Δ ∧ ConsistentQ Δ ∧
        (∀ φ, (∀ n : ℕ, ProvableQ Δ (.tsub φ (Formula.pow2Neg L n))) → φ ∈ Δ) ∧
        (∀ φ ψ, Formula.tsub φ ψ ∈ Δ ∨ Formula.tsub ψ φ ∈ Δ)) := by
  constructor
  · intro h
    obtain ⟨hsub, hmc⟩ := (maximal_in_consistent_extensions_iff_maximalConsistent hΓ).mp h
    exact ⟨hsub, hmc.consistent, hmc.archimedean, hmc.comparable⟩
  · intro ⟨hsub, hcons, harch, hcomp⟩
    exact (maximal_in_consistent_extensions_iff_maximalConsistent hΓ).mpr
      ⟨hsub, ⟨hcons, harch, hcomp⟩⟩

/-- Theorem 8.10: Lindenbaum's Lemma via Zorn's Lemma. -/
theorem exists_maximal_consistent {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) :
    ∃ Δ : Set (Formula L), Γ ⊆ Δ ∧ MaximalConsistent Δ := by
  let E : Set (Set (Formula L)) := {Γ' | Γ ⊆ Γ' ∧ ConsistentQ Γ'}
  have hchain : ∀ c ⊆ E, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ E, ∀ s ∈ c, s ⊆ ub := by
    intro c hcE hch ⟨s₀, hs₀⟩
    refine ⟨⋃₀ c, ⟨?sub, ?cons⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · exact Set.Subset.trans (hcE hs₀).1 (Set.subset_sUnion_of_mem hs₀)
    · -- Consistency of directed unions of consistent sets (via proof compactness).
      by_contra hincons
      rw [inconsistent_iff_provable_one] at hincons
      obtain ⟨Γ₀, hΓ₀sub, hΓ₀prov⟩ := hincons.compact
      have hdir : DirectedOn (· ⊆ ·) c := hch.directedOn
      have hex : ∃ t ∈ c, (Γ₀ : Set (Formula L)) ⊆ t := by
        refine Finset.induction_on (motive := fun S =>
            (S : Set (Formula L)) ⊆ ⋃₀ c → ∃ t ∈ c, (S : Set (Formula L)) ⊆ t) Γ₀ ?empty ?insert hΓ₀sub
        · intro _
          exact ⟨s₀, hs₀, by simp [Finset.coe_empty]⟩
        · intro ψ S _ ih hsub
          have hψ : ψ ∈ ⋃₀ c := hsub (by simp)
          obtain ⟨t₂, ht₂c, hψt₂⟩ := Set.mem_sUnion.mp hψ
          obtain ⟨t₁, ht₁c, ht₁sub⟩ := ih (Set.Subset.trans (by simp) hsub)
          obtain ⟨t₃, ht₃c, h₁₃, h₂₃⟩ := hdir t₁ ht₁c t₂ ht₂c
          exact ⟨t₃, ht₃c, by
            rw [Finset.coe_insert]
            exact Set.insert_subset (h₂₃ hψt₂) (Set.Subset.trans ht₁sub h₁₃)⟩
      obtain ⟨t, htc, htsub⟩ := hex
      have ht_incons : ¬ ConsistentQ t := by
        rw [inconsistent_iff_provable_one]
        exact hΓ₀prov.mono htsub
      exact ht_incons (hcE htc).2
  have hΓE : Γ ∈ E := ⟨Set.Subset.rfl, hcons⟩
  obtain ⟨Δ, hΓΔ, hmax⟩ := zorn_subset_nonempty E hchain Γ hΓE
  exact ⟨Δ, (maximal_in_consistent_extensions_iff_maximalConsistent hcons).mp hmax⟩

end ContinuousFOL
