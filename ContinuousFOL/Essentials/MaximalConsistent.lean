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

/-- Lemma 8.11: Instantiation inside maximal consistent sets after bound renaming. -/
theorem maximal_consistent_sup_instantiate {L : Signature} {Δ : Set (Formula L)}
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

/-- Lemma 8.12: Dedekind cut equality of dyadic lower and upper bounds in `Δ`. -/
theorem maximal_consistent_sup_eq_inf {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (φ : Formula L) :
    sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ Formula.tsub (Formula.dyadic L p) φ ∈ Δ} =
    sInf {r : ℝ | ∃ q : DyadicCode, r = q.val ∧ Formula.tsub φ (Formula.dyadic L q) ∈ Δ} := by
  sorry

/-- Lemma 8.6: Maximal elements of `E(Γ)` coincide with `MaximalConsistent`. -/
theorem maximal_in_consistent_extensions_iff {L : Signature} {Γ Δ : Set (Formula L)}
    (_hΓ : ConsistentQ Γ) :
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
  exact ⟨Δ, (maximal_in_consistent_extensions_iff hcons).mp hmax⟩

end ContinuousFOL
