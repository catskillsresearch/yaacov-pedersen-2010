/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8 Lemma 8.4; vision.md page 16
-/
module

public import ContinuousFOL.Group2Axioms.ProvableQ
public import ContinuousFOL.Group2Axioms.ProvableMetricQ
public import ContinuousFOL.Group2Axioms.MetricAxiomSchema
public import ContinuousFOL.Essentials.DeductionTheorem
public import ContinuousFOL.Essentials.GeneralizationTheorem
public import ContinuousFOL.SubstitutionAndCompletions.FormulaHasFunc
public import ContinuousFOL.Essentials.ProvableBoundSubst
public import ContinuousFOL.Essentials.ProvableQMono
public import ContinuousFOL.Essentials.MaximalConsistent

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

lemma Term.substConstVar_of_not_hasFunc {L : Signature} (s : Term L) (c : L.Func) (y : Var)
    (h : ¬ s.hasFunc c) : s.substConstVar c y = s := by
  induction s with
  | var z => rfl
  | func f args ih =>
    simp only [Term.hasFunc, not_or, not_exists] at h
    simp only [Term.substConstVar, h.1, false_and, ↓reduceIte]
    congr 1
    funext i
    exact ih i (h.2 i)

lemma Term.vars_substConstVar {L : Signature} (s : Term L) (c : L.Func) (y : Var) :
    (s.substConstVar c y).vars ⊆ insert y s.vars := by
  induction s with
  | var z => simp [Term.substConstVar]
  | func f args ih =>
    simp only [Term.substConstVar]
    split_ifs
    · simp [Term.vars]
    · intro v hv
      simp only [Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and] at hv
      obtain ⟨i, hi⟩ := hv
      rcases Finset.mem_insert.mp (ih i hi) with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert_of_mem (by
          simp only [Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and]
          exact ⟨i, h⟩)

lemma Term.substConstVar_subst {L : Signature} (s t : Term L) (c : L.Func) (y z : Var)
    (hyz : y ≠ z) :
    (s.subst t z).substConstVar c y = (s.substConstVar c y).subst (t.substConstVar c y) z := by
  induction s with
  | var w => by_cases hw : w = z <;> simp [Term.subst, Term.substConstVar, hw]
  | func f args ih =>
    simp only [Term.subst, Term.substConstVar]
    split_ifs with hf
    · simp [Term.subst, hyz]
    · simp only [Term.subst]
      congr 1
      funext i
      exact ih i

lemma Term.subst_substConstVar_var {L : Signature} (s : Term L) (c : L.Func) (x y : Var)
    (hy : y ∉ s.vars) : (s.substConstVar c y).subst (.var x) y = s.substConstVar c x := by
  induction s with
  | var w =>
    have hw : w ≠ y := by rintro rfl; simp [Term.vars] at hy
    simp [Term.substConstVar, Term.subst, hw]
  | func f args ih =>
    simp only [Term.substConstVar]
    split_ifs
    · simp [Term.subst]
    · simp only [Term.subst]
      congr 1
      funext i
      exact ih i (fun h => hy (by
        simp only [Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, h⟩))

namespace Formula

variable {L : Signature}

lemma boundVars_subset_allVars (φ : Formula L) : φ.boundVars ⊆ φ.allVars := by
  induction φ with
  | rel _ _ => simp [boundVars]
  | tsub α β ihα ihβ =>
    simp only [boundVars, allVars]
    exact Finset.union_subset_union ihα ihβ
  | neg α ih => exact ih
  | half α ih => exact ih
  | sup z α ih =>
    simp only [boundVars, allVars]
    exact Finset.insert_subset_insert z ih

lemma substConstVar_of_not_hasFunc (φ : Formula L) (c : L.Func) (y : Var)
    (h : ¬ φ.hasFunc c) : φ.substConstVar c y = φ := by
  induction φ with
  | rel P args =>
    simp only [hasFunc, not_exists] at h
    simp only [substConstVar]
    congr 1
    funext i
    exact Term.substConstVar_of_not_hasFunc _ c y (h i)
  | tsub α β ihα ihβ =>
    simp only [hasFunc, not_or] at h
    simp only [substConstVar, ihα h.1, ihβ h.2]
  | neg α ih => simp only [substConstVar, ih h]
  | half α ih => simp only [substConstVar, ih h]
  | sup z α ih => simp only [substConstVar, ih h]

lemma boundVars_substConstVar (φ : Formula L) (c : L.Func) (y : Var) :
    (φ.substConstVar c y).boundVars = φ.boundVars := by
  induction φ with
  | rel _ _ => rfl
  | tsub α β ihα ihβ => simp only [substConstVar, boundVars, ihα, ihβ]
  | neg α ih => exact ih
  | half α ih => exact ih
  | sup z α ih => simp only [substConstVar, boundVars, ih]

lemma freeVars_substConstVar (φ : Formula L) (c : L.Func) (y : Var) :
    (φ.substConstVar c y).freeVars ⊆ insert y φ.freeVars := by
  induction φ with
  | rel P args =>
    intro v hv
    simp only [substConstVar, freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    rcases Finset.mem_insert.mp (Term.vars_substConstVar _ c y hi) with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (by
        simp only [freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, h⟩)
  | tsub α β ihα ihβ =>
    intro v hv
    simp only [substConstVar, freeVars, Finset.mem_union] at hv
    rcases hv with h | h
    · rcases Finset.mem_insert.mp (ihα h) with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h')
    · rcases Finset.mem_insert.mp (ihβ h) with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h')
  | neg α ih => exact ih
  | half α ih => exact ih
  | sup z α ih =>
    intro v hv
    simp only [substConstVar, freeVars, Finset.mem_erase] at hv
    rcases Finset.mem_insert.mp (ih hv.2) with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hv.1, h⟩)

lemma allVars_substConstVar (φ : Formula L) (c : L.Func) (y : Var) :
    (φ.substConstVar c y).allVars ⊆ insert y φ.allVars := by
  induction φ with
  | rel P args =>
    intro v hv
    simp only [substConstVar, allVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    rcases Finset.mem_insert.mp (Term.vars_substConstVar _ c y hi) with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (by
        simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, h⟩)
  | tsub α β ihα ihβ =>
    intro v hv
    simp only [substConstVar, allVars, Finset.mem_union] at hv
    rcases hv with h | h
    · rcases Finset.mem_insert.mp (ihα h) with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h')
    · rcases Finset.mem_insert.mp (ihβ h) with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h')
  | neg α ih => exact ih
  | half α ih => exact ih
  | sup z α ih =>
    intro v hv
    simp only [substConstVar, allVars, Finset.mem_insert] at hv
    rcases hv with h | h
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl h))
    · rcases Finset.mem_insert.mp (ih h) with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h')

lemma substConstVar_freeSubst (φ : Formula L) (t : Term L) (c : L.Func) (y z : Var)
    (hyz : y ≠ z) :
    (φ.freeSubst t z).substConstVar c y =
      (φ.substConstVar c y).freeSubst (t.substConstVar c y) z := by
  induction φ with
  | rel P args =>
    simp only [freeSubst, substConstVar]
    congr 1
    funext i
    exact Term.substConstVar_subst _ _ c y z hyz
  | tsub α β ihα ihβ => simp only [freeSubst, substConstVar, ihα, ihβ]
  | neg α ih => simp only [freeSubst, substConstVar, ih]
  | half α ih => simp only [freeSubst, substConstVar, ih]
  | sup w α ih =>
    by_cases hw : w = z
    · simp only [freeSubst, substConstVar, eq_true hw, ↓reduceIte]
    · simp only [freeSubst, substConstVar, eq_false hw, ↓reduceIte, ih]

lemma substConstVar_freeSubstCorrect (φ : Formula L) (t : Term L) (c : L.Func) (y z : Var)
    (hyz : y ≠ z) (hyb : y ∉ φ.boundVars) (h : φ.FreeSubstCorrect t z) :
    (φ.substConstVar c y).FreeSubstCorrect (t.substConstVar c y) z := by
  induction φ with
  | rel _ _ => simp [substConstVar, FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    simp only [boundVars, Finset.mem_union, not_or] at hyb
    simp only [substConstVar, FreeSubstCorrect] at h ⊢
    exact ⟨ihα hyb.1 h.1, ihβ hyb.2 h.2⟩
  | neg α ih => exact ih hyb h
  | half α ih => exact ih hyb h
  | sup w α ih =>
    simp only [boundVars, Finset.mem_insert, not_or] at hyb
    simp only [substConstVar]
    unfold FreeSubstCorrect at h ⊢
    by_cases hw : w = z
    · simp [hw]
    · simp only [eq_false hw, ↓reduceIte] at h ⊢
      refine ⟨fun hz hwt => ?_, ih hyb.2 h.2⟩
      rcases Finset.mem_insert.mp (freeVars_substConstVar α c y hz) with h' | h'
      · exact hyz h'.symm
      · rcases Finset.mem_insert.mp (Term.vars_substConstVar t c y hwt) with h'' | h''
        · exact hyb.1 h''.symm
        · exact h.1 h' h''

lemma substConstVar_genList (xs : List Var) (ψ : Formula L) (c : L.Func) (y : Var) :
    (Formula.genList xs ψ).substConstVar c y = Formula.genList xs (ψ.substConstVar c y) := by
  induction xs with
  | nil => rfl
  | cons z zs ih => simp only [Formula.genList, substConstVar, ih]

lemma freeSubst_substConstVar_var (φ : Formula L) (c : L.Func) (x y : Var)
    (hy : y ∉ φ.allVars) :
    (φ.substConstVar c y).freeSubst (.var x) y = φ.substConstVar c x := by
  induction φ with
  | rel P args =>
    simp only [substConstVar, freeSubst]
    congr 1
    funext i
    exact Term.subst_substConstVar_var _ c x y (fun h => hy (by
      simp only [allVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, h⟩))
  | tsub α β ihα ihβ =>
    simp only [allVars, Finset.mem_union, not_or] at hy
    simp only [substConstVar, freeSubst, ihα hy.1, ihβ hy.2]
  | neg α ih => simp only [substConstVar, freeSubst, ih hy]
  | half α ih => simp only [substConstVar, freeSubst, ih hy]
  | sup z α ih =>
    simp only [allVars, Finset.mem_insert, not_or] at hy
    have hzy : ¬ z = y := fun h => hy.1 h.symm
    simp only [substConstVar, freeSubst, eq_false hzy, ↓reduceIte, ih hy.2]

end Formula

/-- Replacing a constant by a variable absent from an axiom instance yields an axiom instance. -/
lemma BaseAxiomSchema.substConstVar {L : Signature} {ψ : Formula L} (h : BaseAxiomSchema ψ)
    (c : L.Func) (y : Var) (hy : y ∉ ψ.allVars) :
    BaseAxiomSchema (ψ.substConstVar c y) := by
  cases h with
  | A1 φ ψ => exact .A1 _ _
  | A2 φ ψ χ => exact .A2 _ _ _
  | A3 φ ψ => exact .A3 _ _
  | A4 φ ψ => exact .A4 _ _
  | A5 φ => exact .A5 _
  | A6 φ => exact .A6 _
  | A7 x φ ψ => exact .A7 x _ _
  | A8 z t φ hc =>
    have hyz : y ≠ z := fun h => hy (by simp [Formula.allVars, h])
    have hyb : y ∉ φ.boundVars := fun h =>
      hy (by simp [Formula.allVars, Formula.boundVars_subset_allVars φ h])
    simp only [Formula.substConstVar]
    rw [Formula.substConstVar_freeSubst φ t c y z hyz]
    exact .A8 z _ _ (Formula.substConstVar_freeSubstCorrect φ t c y z hyz hyb hc)
  | A9 z φ hz =>
    have hyz : y ≠ z := fun h => hy (by simp [Formula.allVars, h])
    refine .A9 z _ (fun h => ?_)
    rcases Finset.mem_insert.mp (Formula.freeVars_substConstVar φ c y h) with h' | h'
    · exact hyz h'.symm
    · exact hz h'

/-- Replacing a constant absent from `Γ` by any sufficiently fresh variable preserves
    `Γ ⊢_Q`. -/
lemma ProvableQ.substConstVar_fresh {L : Signature} {Γ : Set (Formula L)} (c : L.Func)
    (hcΓ : ∀ ψ ∈ Γ, ¬ ψ.hasFunc c) {φ : Formula L} (h : ProvableQ Γ φ) :
    ∃ S : Finset Var, ∀ y ∉ S, ProvableQ Γ (φ.substConstVar c y) := by
  induction h with
  | @ax xs ψ hax =>
    refine ⟨ψ.allVars, fun y hy => ?_⟩
    rw [Formula.substConstVar_genList]
    exact .ax (hax.substConstVar c y hy)
  | @hyp ψ hmem =>
    exact ⟨∅, fun y _ => by
      rw [Formula.substConstVar_of_not_hasFunc ψ c y (hcΓ ψ hmem)]
      exact .hyp hmem⟩
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨S₁, h₁⟩ := ih₁
    obtain ⟨S₂, h₂⟩ := ih₂
    exact ⟨S₁ ∪ S₂, fun y hy =>
      .mp (h₁ y (fun h => hy (Finset.mem_union_left _ h)))
        (h₂ y (fun h => hy (Finset.mem_union_right _ h)))⟩

/-- Lemma 8.4: Generalizing over a fresh constant symbol `c`. -/
theorem generalize_fresh_const {L : Signature} (Γ : Set (Formula L)) (φ : Formula L)
    (c : L.Func) (hc0 : L.funcArity c = 0)
    (hcΓ : ∀ ψ ∈ Γ, ¬ ψ.hasFunc c) (x : Var) (hxφ : x ∉ φ.allVars)
    (hprov : ProvableQ Γ φ) :
    ProvableQ Γ (.sup x (φ.substConstVar c x)) := by
  -- Finitely many hypotheses suffice; pick `y` fresh for them, the proof, `φ`, and `x`.
  obtain ⟨Γ₀, hΓ₀, hprov₀⟩ := ProvableQ.compact hprov
  obtain ⟨S, hS⟩ := ProvableQ.substConstVar_fresh c (fun ψ hψ => hcΓ ψ (hΓ₀ hψ)) hprov₀
  have hyT := freshAbove_not_mem (S ∪ φ.allVars ∪ insert x (Γ₀.biUnion Formula.allVars))
  set y := freshAbove (S ∪ φ.allVars ∪ insert x (Γ₀.biUnion Formula.allVars))
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_biUnion, not_or, not_exists,
    not_and] at hyT
  obtain ⟨⟨hyS, hyφ⟩, hyx, hyΓ⟩ := hyT
  -- `Γ₀ ⊢ φ[y/c]`, then generalize on `y` (not free in `Γ₀`).
  have h1 : ProvableQ (↑Γ₀ : Set (Formula L)) (φ.substConstVar c y) := hS y hyS
  have h2 : ProvableQ (↑Γ₀ : Set (Formula L)) (.sup y (φ.substConstVar c y)) :=
    generalization_theorem _ _ y
      (fun ψ hψ hfree => hyΓ ψ hψ (Formula.freeVars_subset_allVars ψ hfree)) h1
  -- Rename the bound `y` to `x` by Lemma 8.3.
  have hxall : x ∉ (Formula.sup y (φ.substConstVar c y)).allVars := by
    simp only [Formula.allVars, Finset.mem_insert, not_or]
    refine ⟨fun h => hyx h.symm, fun h => ?_⟩
    rcases Finset.mem_insert.mp (Formula.allVars_substConstVar φ c y h) with h' | h'
    · exact hyx h'.symm
    · exact hxφ h'
  obtain ⟨-, b2⟩ := provable_bound_subst (Formula.sup y (φ.substConstVar c y)) y x hxall
  have hyb : y ∉ (φ.substConstVar c y).boundVars := by
    rw [Formula.boundVars_substConstVar]
    exact fun h => hyφ (Formula.boundVars_subset_allVars φ h)
  have hb : (Formula.sup y (φ.substConstVar c y)).boundSubst x y =
      .sup x (φ.substConstVar c x) := by
    simp only [Formula.boundSubst, ↓reduceIte, Formula.boundSubst_of_not_mem_boundVars _ hyb]
    rw [Formula.freeSubst_substConstVar_var φ c x y hyφ]
  rw [hb] at b2
  exact (ProvableQ.mp h2 (b2.mono (Set.empty_subset _))).mono hΓ₀


lemma Term.substConstVar_var {L : Signature} (z : Var) (c : L.Func) (y : Var) :
    (Term.var z).substConstVar c y = .var z := rfl

lemma Formula.substConstVar_dist {LM : MetricSignature} (t₀ t₁ : Term LM.toSignature)
    (c : LM.Func) (y : Var) :
    (Formula.dist (LM := LM) t₀ t₁).substConstVar c y =
      Formula.dist (LM := LM) (t₀.substConstVar c y) (t₁.substConstVar c y) := by
  simp only [Formula.dist, Formula.substConstVar]
  congr 1
  funext i
  split_ifs <;> rfl

lemma Formula.substConstVar_dyadic {L : Signature} (d : DyadicCode) (c : L.Func) (y : Var) :
    (Formula.dyadic L d).substConstVar c y = Formula.dyadic L d := by
  induction d with
  | one =>
    simp only [Formula.dyadic, Formula.one, Formula.substConstVar, Formula.defaultAtom,
      Term.substConstVar_var]
  | neg d ih =>
    simp only [Formula.dyadic, Formula.substConstVar, ih]
  | tsub a b iha ihb =>
    simp only [Formula.dyadic, Formula.substConstVar, iha, ihb]
  | half d ih =>
    simp only [Formula.dyadic, Formula.substConstVar, ih]

lemma MetricAxiomSchema.substConstVar {LM : MetricSignature}
    {ψ : Formula LM.toSignature} (h : MetricAxiomSchema (LM := LM) ψ)
    (c : LM.Func) (y : Var) (hy : y ∉ ψ.allVars) :
    MetricAxiomSchema (LM := LM) (ψ.substConstVar c y) := by
  cases h with
  | base hbase =>
    exact .base (hbase.substConstVar c y hy)
  | A10 x =>
    simp only [Formula.substConstVar_dist, Term.substConstVar_var]
    exact .A10 x
  | A11 x z =>
    simp only [Formula.substConstVar, Formula.substConstVar_dist, Term.substConstVar_var]
    exact .A11 x z
  | A12 x z w =>
    simp only [Formula.substConstVar, Formula.substConstVar_dist, Term.substConstVar_var]
    exact .A12 x z w
  | @A13 f i ε r q v z w hε0 hε1 hεr hqm =>
    have hterm (t : Term LM.toSignature) :
        (Term.func f (replaceArg (fun j => Term.var (v j)) i t)).substConstVar c y =
          .func f (replaceArg (fun j => Term.var (v j)) i (t.substConstVar c y)) := by
      -- `f` cannot be a 0-ary constant, since `i : Fin (funcArity f)`.
      have hf0 : ¬ (f = c ∧ LM.funcArity f = 0) := by
        rintro ⟨_, hf0⟩
        exact (hf0 ▸ i).elim0
      simp only [Term.substConstVar, hf0, ↓reduceIte]
      congr 1
      funext j
      simp only [replaceArg]
      split_ifs <;> simp [Term.substConstVar_var]
    simp only [Formula.minF, Formula.substConstVar, Formula.substConstVar_dist,
      Formula.substConstVar_dyadic, Term.substConstVar_var, hterm]
    exact .A13 f i ε r q v z w hε0 hε1 hεr hqm
  | @A14 P i ε r q v z w hε0 hε1 hεr hqm =>
    have hrel (t : Term LM.toSignature) :
        (fun j => (replaceArg (fun k => Term.var (v k)) i t j).substConstVar c y) =
          replaceArg (fun k => Term.var (v k)) i (t.substConstVar c y) := by
      funext j
      simp only [replaceArg]
      split_ifs <;> simp [Term.substConstVar_var]
    simp only [Formula.minF, Formula.substConstVar, Formula.substConstVar_dist,
      Formula.substConstVar_dyadic, Term.substConstVar_var, hrel]
    exact .A14 P i ε r q v z w hε0 hε1 hεr hqm

lemma ProvableMetricQ.substConstVar_fresh {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (c : LM.Func)
    (hcΓ : ∀ ψ ∈ Γ, ¬ ψ.hasFunc c) {φ : Formula LM.toSignature}
    (h : ProvableMetricQ Γ φ) :
    ∃ S : Finset Var, ∀ y ∉ S, ProvableMetricQ Γ (φ.substConstVar c y) := by
  induction h with
  | @ax xs ψ hax =>
    refine ⟨ψ.allVars, fun y hy => ?_⟩
    rw [Formula.substConstVar_genList]
    exact .ax (hax.substConstVar c y hy)
  | @hyp ψ hmem =>
    exact ⟨∅, fun y _ => by
      rw [Formula.substConstVar_of_not_hasFunc ψ c y (hcΓ ψ hmem)]
      exact .hyp hmem⟩
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨S₁, h₁⟩ := ih₁
    obtain ⟨S₂, h₂⟩ := ih₂
    exact ⟨S₁ ∪ S₂, fun y hy =>
      .mp (h₁ y (fun h => hy (Finset.mem_union_left _ h)))
        (h₂ y (fun h => hy (Finset.mem_union_right _ h)))⟩

/-- Lemma 8.4 for a signature with a metric. -/
theorem generalize_fresh_const_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature)
    (c : LM.Func) (_hc0 : LM.funcArity c = 0)
    (hcΓ : ∀ ψ ∈ Γ, ¬ ψ.hasFunc c) (x : Var) (hxφ : x ∉ φ.allVars)
    (hprov : ProvableMetricQ Γ φ) :
    ProvableMetricQ Γ (.sup x (φ.substConstVar c x)) := by
  obtain ⟨Γ₀, hΓ₀, hprov₀⟩ := ProvableMetricQ.compact hprov
  obtain ⟨S, hS⟩ :=
    ProvableMetricQ.substConstVar_fresh c (fun ψ hψ => hcΓ ψ (hΓ₀ hψ)) hprov₀
  have hyT := freshAbove_not_mem (S ∪ φ.allVars ∪ insert x (Γ₀.biUnion Formula.allVars))
  set y := freshAbove (S ∪ φ.allVars ∪ insert x (Γ₀.biUnion Formula.allVars))
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_biUnion, not_or, not_exists,
    not_and] at hyT
  obtain ⟨⟨hyS, hyφ⟩, hyx, hyΓ⟩ := hyT
  have h1 : ProvableMetricQ (↑Γ₀ : Set (Formula LM.toSignature))
      (φ.substConstVar c y) := hS y hyS
  have h2 : ProvableMetricQ (↑Γ₀ : Set (Formula LM.toSignature))
      (.sup y (φ.substConstVar c y)) :=
    generalization_theorem_metric _ _ y
      (fun ψ hψ hfree => hyΓ ψ hψ (Formula.freeVars_subset_allVars ψ hfree)) h1
  have hxall : x ∉ (Formula.sup y (φ.substConstVar c y)).allVars := by
    simp only [Formula.allVars, Finset.mem_insert, not_or]
    refine ⟨fun h => hyx h.symm, fun h => ?_⟩
    rcases Finset.mem_insert.mp (Formula.allVars_substConstVar φ c y h) with h' | h'
    · exact hyx h'.symm
    · exact hxφ h'
  obtain ⟨-, b2⟩ := provable_bound_subst_metric (Formula.sup y (φ.substConstVar c y)) y x hxall
  have hyb : y ∉ (φ.substConstVar c y).boundVars := by
    rw [Formula.boundVars_substConstVar]
    exact fun h => hyφ (Formula.boundVars_subset_allVars φ h)
  have hb : (Formula.sup y (φ.substConstVar c y)).boundSubst x y =
      .sup x (φ.substConstVar c x) := by
    simp only [Formula.boundSubst, ↓reduceIte, Formula.boundSubst_of_not_mem_boundVars _ hyb]
    rw [Formula.freeSubst_substConstVar_var φ c x y hyφ]
  rw [hb] at b2
  exact (ProvableMetricQ.mp h2 (b2.mono (Set.empty_subset _))).mono hΓ₀

end ContinuousFOL
