/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Proposition 9.2; vision.md page 21
-/
module

public import ContinuousFOL.Completeness.HenkinComplete
public import ContinuousFOL.Completeness.SignatureExtension
public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.MetricSignature
public import ContinuousFOL.Completeness.ProvableTsubOfInconsistentAdjoin
public import ContinuousFOL.Essentials.GeneralizeFreshConst
public import ContinuousFOL.Essentials.MaximalConsistent
public import ContinuousFOL.Essentials.MaximalConsistentMetric

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-! ### Auxiliary syntactic lemmas for Proposition 9.2 -/

namespace HenkinExt

variable {L : Signature}

/-- Instantiate a CL tautology given by an explicit propositional form. -/
lemma taut {Γ : Set (Formula L)} {n : ℕ}
    (T : CLPropForm (Fin n)) (f : Fin n → Formula L) {θ : Formula L}
    (hθ : T.toFormula f = θ)
    (hv : ∀ v : Fin n → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ 1) → T.eval v = 0) :
    ProvableQ Γ θ := by
  subst hθ
  exact CLPropForm.toFormula_provable_of_valid f T hv

/-- Cut: a provable hypothesis may be discharged. -/
lemma cut {Γ : Set (Formula L)} {χ ψ : Formula L}
    (h : ProvableQ (Γ ∪ {χ}) ψ) (hχ : ProvableQ Γ χ) : ProvableQ Γ ψ := by
  induction h with
  | ax hax => exact .ax hax
  | hyp hmem =>
    rcases hmem with hmem | hmem
    · exact .hyp hmem
    · rw [Set.mem_singleton_iff.mp hmem]; exact hχ
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

lemma inconsistent_of_imp {Γ : Set (Formula L)} {χ χ' : Formula L}
    (h : ¬ ConsistentQ (Γ ∪ {χ})) (himp : ProvableQ (Γ ∪ {χ'}) χ) :
    ¬ ConsistentQ (Γ ∪ {χ'}) := by
  rw [inconsistent_iff_provable_one] at h ⊢
  refine cut (ProvableQ.mono ?_ h) himp
  exact Set.union_subset_union_left _ Set.subset_union_left

lemma mem_adjoin (Γ : Set (Formula L)) (χ : Formula L) : χ ∈ Γ ∪ {χ} :=
  Set.mem_union_right _ (Set.mem_singleton _)

/-- Mirror of `provable_tsub_of_inconsistent_adjoin`: if `Γ ∪ {φ ∸ q}` is inconsistent,
    then `Γ ⊢_Q q ∸ φ`. -/
lemma provable_tsub_of_inconsistent_adjoin' (Γ : Set (Formula L)) (φ : Formula L)
    (q : DyadicCode) (h : ¬ ConsistentQ (Γ ∪ {.tsub φ (Formula.dyadic L q)})) :
    ProvableQ Γ (.tsub (Formula.dyadic L q) φ) := by
  have h' : ¬ ConsistentQ (Γ ∪ {.tsub (Formula.dyadic L (.neg q)) (.neg φ)}) :=
    inconsistent_of_imp h (.mp (.hyp (mem_adjoin _ _)) (taut
      (.tsub (.tsub (.var 0) (.var 1)) (.tsub (.neg (.var 1)) (.neg (.var 0))))
      ![φ, Formula.dyadic L q] rfl (by
        intro v _
        simp only [CLPropForm.eval, tsubR, max_def]
        split_ifs <;> linarith)))
  have := provable_tsub_of_inconsistent_adjoin Γ (.neg φ) (.neg q) h'
  exact .mp this (taut
    (.tsub (.tsub (.var 1) (.var 0)) (.tsub (.neg (.var 0)) (.neg (.var 1))))
    ![φ, Formula.dyadic L q] rfl (by
      intro v _
      simp only [CLPropForm.eval, tsubR, max_def]
      split_ifs <;> linarith))

lemma not_hasFunc_dyadic (c : L.Func) (d : DyadicCode) : ¬ (Formula.dyadic L d).hasFunc c := by
  induction d with
  | one => simp [Formula.dyadic, Formula.one, Formula.defaultAtom, Formula.hasFunc, Term.hasFunc]
  | neg d ih => simpa [Formula.dyadic, Formula.hasFunc] using ih
  | tsub a b iha ihb => simp [Formula.dyadic, Formula.hasFunc, iha, ihb]
  | half d ih => simpa [Formula.dyadic, Formula.hasFunc] using ih

lemma freeSubst_const_substConstVar (φ : Formula L) (c : L.Func) (hc : L.funcArity c = 0)
    (x y : Var) (hyx : y ≠ x) (hφ : ¬ φ.hasFunc c) :
    (φ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x).substConstVar c y =
      φ.freeSubst (.var y) x := by
  rw [Formula.substConstVar_freeSubst φ _ c y x hyx, Formula.substConstVar_of_not_hasFunc φ c y hφ]
  congr 1
  simp [Term.substConstVar, hc]

lemma freeSubstCorrect_var_back (φ : Formula L) {x y : Var}
    (hy : y ∉ φ.allVars) : (φ.freeSubst (.var y) x).FreeSubstCorrect (.var x) y := by
  induction φ with
  | rel _ _ => simp [Formula.freeSubst, Formula.FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    simp only [Formula.allVars, Finset.mem_union, not_or] at hy
    simp only [Formula.freeSubst, Formula.FreeSubstCorrect]
    exact ⟨ihα hy.1, ihβ hy.2⟩
  | neg α ih =>
    simp only [Formula.freeSubst, Formula.FreeSubstCorrect]
    exact ih hy
  | half α ih =>
    simp only [Formula.freeSubst, Formula.FreeSubstCorrect]
    exact ih hy
  | sup z α ih =>
    simp only [Formula.allVars, Finset.mem_insert, not_or] at hy
    have hzy : ¬ z = y := fun h => hy.1 h.symm
    have hyα : y ∉ α.freeVars := fun h => hy.2 (Formula.freeVars_subset_allVars α h)
    by_cases hzx : z = x
    · simp only [Formula.freeSubst, eq_true hzx, ↓reduceIte]
      unfold Formula.FreeSubstCorrect
      rw [← hzx]
      simp only [eq_false hzy, ↓reduceIte]
      exact ⟨fun h => absurd h hyα, Formula.freeSubstCorrect_of_not_mem_freeVars α _ y hyα⟩
    · simp only [Formula.freeSubst, eq_false hzx, ↓reduceIte]
      unfold Formula.FreeSubstCorrect
      simp only [eq_false hzy, ↓reduceIte]
      exact ⟨fun _ h => hzx (by simpa [Term.vars] using h), ih hy.2⟩

/-- `⊢ sup_x φ ∸ sup_y φ[y/x]` for `y` fresh. -/
lemma sup_le_rename {Γ : Set (Formula L)} (φ : Formula L) {x y : Var} (hyx : y ≠ x)
    (hy : y ∉ φ.allVars) :
    ProvableQ Γ (.tsub (.sup x φ) (.sup y (φ.freeSubst (.var y) x))) := by
  have hyfree : y ∉ φ.freeVars := fun h => hy (Formula.freeVars_subset_allVars φ h)
  have hcancel := Formula.freeSubst_var_cancel φ (Ne.symm hyx) hyfree
    (Formula.freeSubstCorrect_var_of_not_mem_allVars φ x y hy)
  have s1 : ProvableQ (∅ : Set (Formula L)) (.tsub φ (.sup y (φ.freeSubst (.var y) x))) := by
    have := ProvableQ.ax0 (Γ := (∅ : Set (Formula L)))
      (.A8 y (.var x) (φ.freeSubst (.var y) x) (freeSubstCorrect_var_back φ hy))
    rwa [hcancel] at this
  have s2 := ProvableQ.sup_cong0 x s1
  have hxβ := Formula.not_mem_freeVars_freeSubst_var φ hyx
  have s3 : ProvableQ (∅ : Set (Formula L))
      (.tsub (.sup x (.sup y (φ.freeSubst (.var y) x))) (.sup y (φ.freeSubst (.var y) x))) :=
    ProvableQ.ax0 (.A9 x _ (by simp [Formula.freeVars, hxβ]))
  exact ProvableQ.mono (Set.empty_subset _) (ProvableQ.tsub_trans s2 s3)

/-- Core of the proof of Proposition 9.2(ii): adjoining one Henkin axiom whose constant is
    fresh preserves consistency. -/
theorem henkin_adjoin_consistent {Γ : Set (Formula L)} (hΓ : ConsistentQ Γ)
    (φ : Formula L) (x : Var) (p q : DyadicCode) (hpq : p.val < q.val)
    (c : L.Func) (hc : L.funcArity c = 0)
    (hcΓ : ∀ ψ ∈ Γ, ¬ ψ.hasFunc c) (hcφ : ¬ φ.hasFunc c) :
    ConsistentQ (Γ ∪ {(Formula.minF (.tsub (.sup x φ) (Formula.dyadic L q))
      (.tsub (Formula.dyadic L p)
        (φ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x)))}) := by
  by_contra hinc
  have hA : ¬ ConsistentQ (Γ ∪ {Formula.tsub (.sup x φ) (Formula.dyadic L q)}) :=
    inconsistent_of_imp hinc (.mp (.hyp (mem_adjoin _ _)) (taut
    (.tsub (.tsub (.var 0) (.tsub (.var 0) (.var 1))) (.var 0))
    ![Formula.tsub (.sup x φ) (Formula.dyadic L q),
      Formula.tsub (Formula.dyadic L p)
        (φ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x)] rfl (by
      intro v hv
      obtain ⟨h0, _⟩ := hv 0
      obtain ⟨h1, _⟩ := hv 1
      simp only [CLPropForm.eval, tsubR, max_def]
      split_ifs <;> linarith)))
  have hB : ¬ ConsistentQ (Γ ∪ {(Formula.tsub (Formula.dyadic L p)
      (φ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x))}) :=
    inconsistent_of_imp hinc (.mp (.hyp (mem_adjoin _ _)) (taut
    (.tsub (.tsub (.var 0) (.tsub (.var 0) (.var 1))) (.var 1))
    ![Formula.tsub (.sup x φ) (Formula.dyadic L q),
      Formula.tsub (Formula.dyadic L p)
        (φ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x)] rfl (by
      intro v hv
      obtain ⟨h0, _⟩ := hv 0
      obtain ⟨h1, _⟩ := hv 1
      simp only [CLPropForm.eval, tsubR, max_def]
      split_ifs <;> linarith)))
  have h1 := provable_tsub_of_inconsistent_adjoin' Γ _ q hA
  have h2 := provable_tsub_of_inconsistent_adjoin Γ _ p hB
  have hyT := freshAbove_not_mem
    ((Formula.tsub (φ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x)
      (Formula.dyadic L p)).allVars ∪ φ.allVars ∪ {x})
  set y := freshAbove
    ((Formula.tsub (φ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x)
      (Formula.dyadic L p)).allVars ∪ φ.allVars ∪ {x})
  simp only [Finset.mem_union, Finset.mem_singleton, not_or] at hyT
  obtain ⟨⟨hyθ, hyφ⟩, hyx⟩ := hyT
  have hyp_free : y ∉ (Formula.dyadic L p).freeVars := fun h => hyθ (by
    simp only [Formula.allVars, Finset.mem_union]
    exact Or.inr (Formula.freeVars_subset_allVars _ h))
  have g := generalize_fresh_const Γ _ c hc hcΓ y hyθ h2
  have e : (Formula.tsub (φ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x)
      (Formula.dyadic L p)).substConstVar c y =
        .tsub (φ.freeSubst (.var y) x) (Formula.dyadic L p) := by
    simp only [Formula.substConstVar]
    rw [freeSubst_const_substConstVar φ c hc x y hyx hcφ,
      Formula.substConstVar_of_not_hasFunc _ c y (not_hasFunc_dyadic c p)]
  rw [e] at g
  have g2 : ProvableQ Γ (.tsub (.sup y (φ.freeSubst (.var y) x)) (.sup y (Formula.dyadic L p))) :=
    .mp g (ProvableQ.ax0 (.A7 y _ _))
  have g3 : ProvableQ Γ (.tsub (.sup y (Formula.dyadic L p)) (Formula.dyadic L p)) :=
    ProvableQ.ax0 (.A9 y _ hyp_free)
  have g4 : ProvableQ Γ (.tsub (.sup x φ) (.sup y (φ.freeSubst (.var y) x))) :=
    sup_le_rename φ hyx hyφ
  have hqp : ProvableQ Γ (Formula.dyadic L (.tsub q p)) :=
    ProvableQ.tsub_trans h1 (ProvableQ.tsub_trans g4 (ProvableQ.tsub_trans g2 g3))
  have hpos : 0 < (DyadicCode.tsub q p).val := by
    simp only [DyadicCode.val, tsubR]
    exact lt_max_of_lt_left (by linarith)
  exact (inconsistent_iff_provable_one Γ).mpr (ProvableQ.one_of_dyadic_pos _ hpos hqp) hΓ

end HenkinExt

/-! ### The signature `L^c`

Instead of the paper's tower `L₀ ⊆ L₁ ⊆ ⋯`, we use a single nested inductive type of codes
which contains the symbols of `L`, codes of `L^c`-formulas, and a constant
`c_(φ,x,p,q)` for every code of a formula `φ`.  Every symbol other than those of `L` is
a constant.  The well-founded "size" of codes replaces the paper's level `m`. -/

/-- Codes for the function symbols of `L^c` (and for its formulas). -/
inductive HCode (L : Signature) : Type
  | base : L.Func → HCode L
  | henkin : HCode L → Var → DyadicCode → DyadicCode → HCode L
  | var : Var → HCode L
  | app : HCode L → List (HCode L) → HCode L
  | rel : L.Rel → List (HCode L) → HCode L
  | tsub : HCode L → HCode L → HCode L
  | neg : HCode L → HCode L
  | half : HCode L → HCode L
  | sup : Var → HCode L → HCode L

namespace HCode

variable {L : Signature}

/-- Arity: symbols of `L` keep their arity, all new symbols are constants. -/
def arity : HCode L → ℕ
  | base f => L.funcArity f
  | _ => 0

/-- Moduli of uniform continuity (those of `L`; arbitrary for the new constants). -/
def fmod : (g : HCode L) → Fin g.arity → ℝ → ℝ
  | base f => L.funcMod f
  | _ => fun _ ε => ε

lemma fmod_pos (g : HCode L) (i : Fin g.arity) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    0 < g.fmod i ε ∧ g.fmod i ε ≤ 1 := by
  cases g
  case base f => exact L.funcMod_pos f i ε h0 h1
  all_goals exact ⟨h0, h1⟩

end HCode

/-- The Henkin signature `L^c`. -/
abbrev henkinSig (L : Signature) : Signature where
  Rel := L.Rel
  Func := HCode L
  nonempty_rel := L.nonempty_rel
  relArity := L.relArity
  funcArity := HCode.arity
  relMod := L.relMod
  funcMod := HCode.fmod
  relMod_pos := L.relMod_pos
  funcMod_pos := HCode.fmod_pos

/-- The inclusion `L ⊆ L^c`. -/
def henkinExt (L : Signature) : SignatureExtension L (henkinSig L) where
  relEquiv := Equiv.refl _
  funcMap := HCode.base
  funcMap_inj := fun _ _ h => HCode.base.inj h
  relArity_eq := fun _ => rfl
  funcArity_eq := fun _ => rfl
  relMod_eq := fun _ _ _ => rfl
  funcMod_eq := fun _ _ _ => rfl

namespace HenkinExt

variable {L : Signature}

/-! #### Coding `L^c`-formulas -/

def encT : Term (henkinSig L) → HCode L
  | .var x => .var x
  | .func g args => .app g (List.ofFn fun i => encT (args i))

def encF : Formula (henkinSig L) → HCode L
  | .rel P args => .rel P (List.ofFn fun i => encT (args i))
  | .tsub α β => .tsub (encF α) (encF β)
  | .neg α => .neg (encF α)
  | .half α => .half (encF α)
  | .sup x α => .sup x (encF α)

lemma encT_inj : ∀ {s t : Term (henkinSig L)}, encT s = encT t → s = t := by
  intro s
  induction s with
  | var x =>
    intro t h
    cases t with
    | var y => simp only [encT, HCode.var.injEq] at h; rw [h]
    | func g args => simp [encT] at h
  | func g args ih =>
    intro t h
    cases t with
    | var y => simp [encT] at h
    | func g' args' =>
      simp only [encT, HCode.app.injEq] at h
      obtain ⟨rfl, hl⟩ := h
      have := List.ofFn_injective hl
      congr 1
      funext i
      exact ih i (congrFun this i)

lemma encF_inj : ∀ {φ ψ : Formula (henkinSig L)}, encF φ = encF ψ → φ = ψ := by
  intro φ
  induction φ with
  | rel P args =>
    intro ψ h
    cases ψ with
    | rel P' args' =>
      simp only [encF, HCode.rel.injEq] at h
      obtain ⟨rfl, hl⟩ := h
      have := List.ofFn_injective hl
      congr 1
      funext i
      exact encT_inj (congrFun this i)
    | _ => simp [encF] at h
  | tsub α β ihα ihβ =>
    intro ψ h
    cases ψ with
    | tsub α' β' =>
      simp only [encF, HCode.tsub.injEq] at h
      rw [ihα h.1, ihβ h.2]
    | _ => simp [encF] at h
  | neg α ih =>
    intro ψ h
    cases ψ with
    | neg α' => simp only [encF, HCode.neg.injEq] at h; rw [ih h]
    | _ => simp [encF] at h
  | half α ih =>
    intro ψ h
    cases ψ with
    | half α' => simp only [encF, HCode.half.injEq] at h; rw [ih h]
    | _ => simp [encF] at h
  | sup x α ih =>
    intro ψ h
    cases ψ with
    | sup x' α' =>
      simp only [encF, HCode.sup.injEq] at h
      rw [h.1, ih h.2]
    | _ => simp [encF] at h

lemma size_encT {t : Term (henkinSig L)} {c : HCode L} (h : t.hasFunc c) :
    sizeOf c < sizeOf (encT t) := by
  induction t with
  | var x => simp [Term.hasFunc] at h
  | func g args ih =>
    simp only [Term.hasFunc] at h
    show sizeOf c < sizeOf (HCode.app g (List.ofFn fun i => encT (args i)))
    rcases h with h | ⟨i, hi⟩
    · subst h
      simp only [HCode.app.sizeOf_spec]
      omega
    · have h1 := ih i hi
      have hmem : encT (args i) ∈ List.ofFn (fun i => encT (args i)) :=
        List.mem_ofFn.mpr ⟨i, rfl⟩
      generalize List.ofFn (fun i => encT (args i)) = l at hmem ⊢
      have h2 := List.sizeOf_lt_of_mem hmem
      simp only [HCode.app.sizeOf_spec]
      omega

lemma size_encF {φ : Formula (henkinSig L)} {c : HCode L} (h : φ.hasFunc c) :
    sizeOf c < sizeOf (encF φ) := by
  induction φ with
  | rel P args =>
    simp only [Formula.hasFunc] at h
    obtain ⟨i, hi⟩ := h
    show sizeOf c < sizeOf (HCode.rel (L := L) P (List.ofFn fun i => encT (args i)))
    have h1 := size_encT hi
    have hmem : encT (args i) ∈ List.ofFn (fun i => encT (args i)) :=
      List.mem_ofFn.mpr ⟨i, rfl⟩
    generalize List.ofFn (fun i => encT (args i)) = l at hmem ⊢
    have h2 := List.sizeOf_lt_of_mem hmem
    simp only [HCode.rel.sizeOf_spec]
    omega
  | tsub α β ihα ihβ =>
    simp only [Formula.hasFunc] at h
    simp only [encF, HCode.tsub.sizeOf_spec]
    rcases h with h | h
    · have := ihα h; omega
    · have := ihβ h; omega
  | neg α ih => simp only [encF, HCode.neg.sizeOf_spec]; have := ih h; omega
  | half α ih => simp only [encF, HCode.half.sizeOf_spec]; have := ih h; omega
  | sup x α ih => simp only [encF, HCode.sup.sizeOf_spec]; have := ih h; omega

/-! #### Henkin constants and axioms -/

/-- Index tuples `(φ, x, p, q)`. -/
abbrev HTup (L : Signature) := Formula (henkinSig L) × Var × DyadicCode × DyadicCode

/-- The constant `c_(φ,x,p,q)`. -/
def hconst (τ : HTup L) : HCode L := .henkin (encF τ.1) τ.2.1 τ.2.2.1 τ.2.2.2

lemma hconst_arity (τ : HTup L) : (henkinSig L).funcArity (hconst τ) = 0 := rfl

lemma hconst_inj {τ τ' : HTup L} (h : hconst τ = hconst τ') : τ = τ' := by
  obtain ⟨φ, x, p, q⟩ := τ
  obtain ⟨φ', x', p', q'⟩ := τ'
  simp only [hconst, HCode.henkin.injEq] at h
  obtain ⟨h1, rfl, rfl, rfl⟩ := h
  rw [encF_inj h1]

lemma hconst_ne_base (τ : HTup L) (f : L.Func) : hconst τ ≠ HCode.base f := by
  simp [hconst]

/-- The Henkin axiom `ψ_(φ,x,p,q) = (sup_x φ ∸ q) ∧ (p ∸ φ[c_(φ,x,p,q)/x])`. -/
def henkinAx (τ : HTup L) : Formula (henkinSig L) :=
  Formula.minF (.tsub (.sup τ.2.1 τ.1) (Formula.dyadic _ τ.2.2.2))
    (.tsub (Formula.dyadic _ τ.2.2.1)
      (τ.1.freeSubst (.func (hconst τ) fun i => Fin.elim0 (Fin.cast (hconst_arity τ) i)) τ.2.1))

/-- `Γ^c`. -/
def henkinSet (L : Signature) : Set (Formula (henkinSig L)) :=
  henkinAx '' {τ : HTup L | τ.2.2.1.val < τ.2.2.2.val}

/-! #### Occurrences of function symbols -/

lemma Term.hasFunc_subst {L : Signature} {s t : Term L} {x : Var} {c : L.Func}
    (h : (s.subst t x).hasFunc c) : s.hasFunc c ∨ t.hasFunc c := by
  induction s with
  | var w =>
    by_cases hw : w = x
    · simp only [Term.subst, hw, ↓reduceIte] at h; exact Or.inr h
    · simp only [Term.subst, hw, ↓reduceIte] at h; exact Or.inl h
  | func f args ih =>
    simp only [Term.subst, Term.hasFunc] at h
    rcases h with h | ⟨i, hi⟩
    · left; simp only [Term.hasFunc]; exact Or.inl h
    · rcases ih i hi with h' | h'
      · left; simp only [Term.hasFunc]; exact Or.inr ⟨i, h'⟩
      · exact Or.inr h'

lemma Formula.hasFunc_freeSubst {L : Signature} {φ : Formula L} {t : Term L} {x : Var}
    {c : L.Func} (h : (φ.freeSubst t x).hasFunc c) : φ.hasFunc c ∨ t.hasFunc c := by
  induction φ with
  | rel P args =>
    simp only [Formula.freeSubst, Formula.hasFunc] at h
    obtain ⟨i, hi⟩ := h
    rcases Term.hasFunc_subst hi with h' | h'
    · left; simp only [Formula.hasFunc]; exact ⟨i, h'⟩
    · exact Or.inr h'
  | tsub α β ihα ihβ =>
    simp only [Formula.freeSubst, Formula.hasFunc] at h ⊢
    rcases h with h | h
    · rcases ihα h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inr h'
    · rcases ihβ h with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr h'
  | neg α ih => exact ih h
  | half α ih => exact ih h
  | sup w α ih =>
    by_cases hw : w = x
    · simp only [Formula.freeSubst, hw, ↓reduceIte, Formula.hasFunc] at h
      exact Or.inl h
    · simp only [Formula.freeSubst, hw, ↓reduceIte, Formula.hasFunc] at h
      exact ih h

lemma hasFunc_henkinAx {τ : HTup L} {c : HCode L} (h : (henkinAx τ).hasFunc c) :
    τ.1.hasFunc c ∨ c = hconst τ := by
  have hd : ∀ d, ¬ (Formula.dyadic (henkinSig L) d).hasFunc c :=
    fun d => not_hasFunc_dyadic (L := henkinSig L) c d
  simp only [henkinAx, Formula.minF, Formula.hasFunc] at h
  have key : ∀ θ : Formula (henkinSig L),
      θ = τ.1.freeSubst (.func (hconst τ) fun i => Fin.elim0 (Fin.cast (hconst_arity τ) i))
        τ.2.1 → θ.hasFunc c → τ.1.hasFunc c ∨ c = hconst τ := by
    rintro θ rfl hθ
    rcases Formula.hasFunc_freeSubst hθ with h' | h'
    · exact Or.inl h'
    · simp only [Term.hasFunc] at h'
      rcases h' with h' | ⟨i, _⟩
      · exact Or.inr h'.symm
      · exact Fin.elim0 (Fin.cast (hconst_arity τ) i)
  rcases h with (h | h) | ((h | h) | (h | h))
  · exact Or.inl h
  · exact absurd h (hd _)
  · exact Or.inl h
  · exact absurd h (hd _)
  · exact absurd h (hd _)
  · exact key _ rfl h

lemma not_hasFunc_mapTerm (t : Term L) {c : HCode L} (hc : ∀ f, c ≠ HCode.base f) :
    ¬ ((henkinExt L).mapTerm t).hasFunc c := by
  induction t with
  | var x => simp [SignatureExtension.mapTerm, Term.hasFunc]
  | func f args ih =>
    simp only [SignatureExtension.mapTerm, Term.hasFunc, not_or, not_exists]
    exact ⟨fun h => hc f h.symm, fun i => ih _⟩

lemma not_hasFunc_mapFormula (φ : Formula L) {c : HCode L} (hc : ∀ f, c ≠ HCode.base f) :
    ¬ ((henkinExt L).mapFormula φ).hasFunc c := by
  induction φ with
  | rel P args =>
    simp only [SignatureExtension.mapFormula, Formula.hasFunc, not_exists]
    exact fun i => not_hasFunc_mapTerm _ hc
  | tsub α β ihα ihβ =>
    simp only [SignatureExtension.mapFormula, Formula.hasFunc, not_or]
    exact ⟨ihα, ihβ⟩
  | neg α ih => exact ih
  | half α ih => exact ih
  | sup x α ih => exact ih

/-! #### Conservativity: eliminating the new constants

Replacing every new constant of `L^c` by a sufficiently fresh variable `z` turns an
`L^c`-proof from `Γ ⊆ For(L)` into an `L`-proof (cf. Lemma 8.4). -/

/-- Translation of a symbol application. -/
def trSym (z : Var) : (g : HCode L) → (Fin g.arity → Term L) → Term L
  | .base f, a => .func f a
  | .henkin _ _ _ _, _ => .var z
  | .var _, _ => .var z
  | .app _ _, _ => .var z
  | .rel _ _, _ => .var z
  | .tsub _ _, _ => .var z
  | .neg _, _ => .var z
  | .half _, _ => .var z
  | .sup _ _, _ => .var z

def trT (z : Var) : Term (henkinSig L) → Term L
  | .var x => .var x
  | .func g args => trSym z g (fun i => trT z (args i))

def trF (z : Var) : Formula (henkinSig L) → Formula L
  | .rel P args => .rel P (fun i => trT z (args i))
  | .tsub α β => .tsub (trF z α) (trF z β)
  | .neg α => .neg (trF z α)
  | .half α => .half (trF z α)
  | .sup x α => .sup x (trF z α)

lemma trT_mapTerm (z : Var) (t : Term L) : trT z ((henkinExt L).mapTerm t) = t := by
  induction t with
  | var x => rfl
  | func f args ih =>
    change Term.func f (fun i => trT z ((henkinExt L).mapTerm
      (args (Fin.cast ((henkinExt L).funcArity_eq f) i)))) = Term.func f args
    congr 1
    funext i
    exact ih _

lemma trF_mapFormula (z : Var) (φ : Formula L) : trF z ((henkinExt L).mapFormula φ) = φ := by
  induction φ with
  | rel P args =>
    change Formula.rel P (fun i => trT z ((henkinExt L).mapTerm
      (args (Fin.cast ((henkinExt L).relArity_eq P) i)))) = Formula.rel P args
    congr 1
    funext i
    exact trT_mapTerm z _
  | tsub α β ihα ihβ => simp only [SignatureExtension.mapFormula, trF, ihα, ihβ]
  | neg α ih => simp only [SignatureExtension.mapFormula, trF, ih]
  | half α ih => simp only [SignatureExtension.mapFormula, trF, ih]
  | sup x α ih => simp only [SignatureExtension.mapFormula, trF, ih]

lemma trF_one (z : Var) : trF z (Formula.one (henkinSig L)) = Formula.one L := rfl

lemma trF_dyadic (z : Var) (d : DyadicCode) :
    trF z (Formula.dyadic (henkinSig L) d) = Formula.dyadic L d := by
  induction d with
  | one => exact trF_one z
  | neg d ih => simp only [Formula.dyadic, trF, ih]
  | tsub a b iha ihb => simp only [Formula.dyadic, trF, iha, ihb]
  | half d ih => simp only [Formula.dyadic, trF, ih]

lemma trF_genList (z : Var) (xs : List Var) (ψ : Formula (henkinSig L)) :
    trF z (Formula.genList xs ψ) = Formula.genList xs (trF z ψ) := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [Formula.genList, trF, ih]

lemma vars_trT (z : Var) (t : Term (henkinSig L)) : (trT z t).vars ⊆ insert z t.vars := by
  induction t with
  | var x => simp [trT, Term.vars]
  | func g args ih =>
    cases g
    case base f =>
      intro v hv
      simp only [trT, trSym, Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and] at hv
      obtain ⟨i, hi⟩ := hv
      rcases Finset.mem_insert.mp (ih i hi) with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert_of_mem (by
          simp only [Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and]
          exact ⟨i, h⟩)
    all_goals simp [trT, trSym, Term.vars]

lemma trT_subst (z : Var) (s t : Term (henkinSig L)) (x : Var) (hzx : z ≠ x) :
    trT z (s.subst t x) = (trT z s).subst (trT z t) x := by
  induction s with
  | var w => by_cases hw : w = x <;> simp [Term.subst, trT, hw]
  | func g args ih =>
    cases g
    case base f =>
      simp only [Term.subst, trT, trSym]
      congr 1
      funext i
      exact ih i
    all_goals simp [Term.subst, trT, trSym, hzx]

lemma boundVars_trF (z : Var) (φ : Formula (henkinSig L)) :
    (trF z φ).boundVars = φ.boundVars := by
  induction φ with
  | rel _ _ => rfl
  | tsub α β ihα ihβ => simp only [trF, Formula.boundVars, ihα, ihβ]
  | neg α ih => exact ih
  | half α ih => exact ih
  | sup x α ih => simp only [trF, Formula.boundVars, ih]

lemma freeVars_trF (z : Var) (φ : Formula (henkinSig L)) :
    (trF z φ).freeVars ⊆ insert z φ.freeVars := by
  induction φ with
  | rel P args =>
    intro v hv
    simp only [trF, Formula.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at hv
    obtain ⟨i, hi⟩ := hv
    rcases Finset.mem_insert.mp (vars_trT z _ hi) with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (by
        simp only [Formula.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
        exact ⟨i, h⟩)
  | tsub α β ihα ihβ =>
    intro v hv
    simp only [trF, Formula.freeVars, Finset.mem_union] at hv
    rcases hv with h | h
    · rcases Finset.mem_insert.mp (ihα h) with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ h')
    · rcases Finset.mem_insert.mp (ihβ h) with h' | h'
      · exact Finset.mem_insert.mpr (Or.inl h')
      · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ h')
  | neg α ih => exact ih
  | half α ih => exact ih
  | sup w α ih =>
    intro v hv
    simp only [trF, Formula.freeVars, Finset.mem_erase] at hv
    rcases Finset.mem_insert.mp (ih hv.2) with h | h
    · exact Finset.mem_insert.mpr (Or.inl h)
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hv.1, h⟩)

lemma trF_freeSubst (z : Var) (φ : Formula (henkinSig L)) (t : Term (henkinSig L)) (x : Var)
    (hzx : z ≠ x) : trF z (φ.freeSubst t x) = (trF z φ).freeSubst (trT z t) x := by
  induction φ with
  | rel P args =>
    simp only [Formula.freeSubst, trF]
    congr 1
    funext i
    exact trT_subst z _ _ x hzx
  | tsub α β ihα ihβ => simp only [Formula.freeSubst, trF, ihα, ihβ]
  | neg α ih => simp only [Formula.freeSubst, trF, ih]
  | half α ih => simp only [Formula.freeSubst, trF, ih]
  | sup w α ih =>
    by_cases hw : w = x
    · simp only [Formula.freeSubst, trF, eq_true hw, ↓reduceIte]
    · simp only [Formula.freeSubst, trF, eq_false hw, ↓reduceIte, ih]

lemma trF_freeSubstCorrect (z : Var) (φ : Formula (henkinSig L)) (t : Term (henkinSig L))
    (x : Var) (hzx : z ≠ x) (hzb : z ∉ φ.boundVars) (h : φ.FreeSubstCorrect t x) :
    (trF z φ).FreeSubstCorrect (trT z t) x := by
  induction φ with
  | rel _ _ => simp [trF, Formula.FreeSubstCorrect]
  | tsub α β ihα ihβ =>
    simp only [Formula.boundVars, Finset.mem_union, not_or] at hzb
    simp only [trF, Formula.FreeSubstCorrect] at h ⊢
    exact ⟨ihα hzb.1 h.1, ihβ hzb.2 h.2⟩
  | neg α ih => exact ih hzb h
  | half α ih => exact ih hzb h
  | sup w α ih =>
    simp only [Formula.boundVars, Finset.mem_insert, not_or] at hzb
    simp only [trF]
    unfold Formula.FreeSubstCorrect at h ⊢
    by_cases hw : w = x
    · simp [hw]
    · simp only [eq_false hw, ↓reduceIte] at h ⊢
      refine ⟨fun hx hwt => ?_, ih hzb.2 h.2⟩
      rcases Finset.mem_insert.mp (freeVars_trF z α hx) with h' | h'
      · exact hzx h'.symm
      · rcases Finset.mem_insert.mp (vars_trT z t hwt) with h'' | h''
        · exact hzb.1 h''.symm
        · exact h.1 h' h''

lemma BaseAxiomSchema.trF {ψ : Formula (henkinSig L)} (h : BaseAxiomSchema ψ)
    (z : Var) (hz : z ∉ ψ.allVars) : BaseAxiomSchema (trF z ψ) := by
  cases h with
  | A1 φ ψ => exact .A1 _ _
  | A2 φ ψ χ => exact .A2 _ _ _
  | A3 φ ψ => exact .A3 _ _
  | A4 φ ψ => exact .A4 _ _
  | A5 φ => exact .A5 _
  | A6 φ => exact .A6 _
  | A7 x φ ψ => exact .A7 x _ _
  | A8 w t φ hc =>
    have hzw : z ≠ w := fun h => hz (by simp [Formula.allVars, h])
    have hzb : z ∉ φ.boundVars := fun h =>
      hz (by simp [Formula.allVars, Formula.boundVars_subset_allVars φ h])
    simp only [HenkinExt.trF]
    rw [trF_freeSubst z φ t w hzw]
    exact .A8 w _ _ (trF_freeSubstCorrect z φ t w hzw hzb hc)
  | A9 w φ hw =>
    have hzw : z ≠ w := fun h => hz (by simp [Formula.allVars, h])
    refine .A9 w _ (fun h => ?_)
    rcases Finset.mem_insert.mp (freeVars_trF z φ h) with h' | h'
    · exact hzw h'.symm
    · exact hw h'

lemma ProvableQ.trF {Γ : Set (Formula L)} {φ : Formula (henkinSig L)}
    (h : ProvableQ ((henkinExt L).mapFormula '' Γ) φ) :
    ∃ S : Finset Var, ∀ z ∉ S, ProvableQ Γ (trF z φ) := by
  induction h with
  | @ax xs ψ hax =>
    refine ⟨ψ.allVars, fun z hz => ?_⟩
    rw [trF_genList]
    exact .ax (BaseAxiomSchema.trF hax z hz)
  | @hyp ψ hmem =>
    obtain ⟨ψ₀, h₀, rfl⟩ := hmem
    exact ⟨∅, fun z _ => by rw [trF_mapFormula]; exact .hyp h₀⟩
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨S₁, h₁⟩ := ih₁
    obtain ⟨S₂, h₂⟩ := ih₂
    exact ⟨S₁ ∪ S₂, fun z hz =>
      .mp (h₁ z (fun h => hz (Finset.mem_union_left _ h)))
        (h₂ z (fun h => hz (Finset.mem_union_right _ h)))⟩

/-- `L^c` is conservative over `L` for consistency. -/
lemma consistent_map (Γ : Set (Formula L)) (hΓ : ConsistentQ Γ) :
    ConsistentQ ((henkinExt L).mapFormula '' Γ) := by
  by_contra hinc
  rw [inconsistent_iff_provable_one] at hinc
  obtain ⟨S, hS⟩ := ProvableQ.trF hinc
  have h := hS (freshAbove S) (freshAbove_not_mem S)
  rw [trF_one] at h
  exact (inconsistent_iff_provable_one Γ).mpr h hΓ

/-! #### Proposition 9.2(ii) for finitely many Henkin axioms -/

lemma size_lt_hconst (τ : HTup L) : sizeOf (encF τ.1) < sizeOf (hconst τ) := by
  simp only [hconst, HCode.henkin.sizeOf_spec]
  omega

lemma consistent_finite (Γ : Set (Formula L)) (hΓ : ConsistentQ Γ) (T : Finset (HTup L))
    (hT : ∀ τ ∈ T, τ.2.2.1.val < τ.2.2.2.val) :
    ConsistentQ ((henkinExt L).mapFormula '' Γ ∪ ↑(T.image henkinAx)) := by
  induction T using Finset.strongInduction with
  | H T ih =>
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simpa using consistent_map Γ hΓ
  obtain ⟨τ, hτT, hmax⟩ := Finset.exists_max_image T (fun τ => sizeOf (hconst τ)) hne
  have ih' := ih (T.erase τ) (Finset.erase_ssubset hτT)
    (fun τ' h => hT τ' (Finset.mem_of_mem_erase h))
  have hset : (henkinExt L).mapFormula '' Γ ∪ ↑(T.image henkinAx) =
      ((henkinExt L).mapFormula '' Γ ∪ ↑((T.erase τ).image henkinAx)) ∪ {henkinAx τ} := by
    conv_lhs => rw [← Finset.insert_erase hτT]
    rw [Finset.image_insert, Finset.coe_insert, Set.union_assoc, Set.union_comm _ {henkinAx τ},
      Set.insert_eq]
  rw [hset]
  have hcφ : ¬ τ.1.hasFunc (hconst τ) := fun h => by
    have h1 := size_encF h
    have h2 := size_lt_hconst τ
    omega
  have hcΓ : ∀ ψ ∈ (henkinExt L).mapFormula '' Γ ∪ ↑((T.erase τ).image henkinAx),
      ¬ ψ.hasFunc (hconst τ) := by
    rintro ψ (⟨ψ₀, _, rfl⟩ | hψ)
    · exact not_hasFunc_mapFormula ψ₀ (hconst_ne_base τ)
    · simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hψ
      obtain ⟨τ', hτ', rfl⟩ := hψ
      intro h
      rcases hasFunc_henkinAx h with h' | h'
      · have h1 := size_encF h'
        have h2 := size_lt_hconst τ'
        have h3 := hmax τ' (Finset.mem_of_mem_erase hτ')
        omega
      · exact Finset.ne_of_mem_erase hτ' (hconst_inj h').symm
  exact henkin_adjoin_consistent ih' τ.1 τ.2.1 τ.2.2.1 τ.2.2.2 (hT τ hτT) (hconst τ)
    (hconst_arity τ) hcΓ hcφ

/-- Proposition 9.2(ii) in the form used for both the plain and the metric case. -/
lemma consistent_union (Γ : Set (Formula L)) (hΓ : ConsistentQ Γ) :
    ConsistentQ ((henkinExt L).mapFormula '' Γ ∪ henkinSet L) := by
  by_contra hinc
  rw [inconsistent_iff_provable_one] at hinc
  obtain ⟨Γ₀, hΓ₀, hpr⟩ := ProvableQ.compact hinc
  have hF : (↑(Γ₀.filter (· ∈ henkinSet L)) : Set (Formula (henkinSig L))) ⊆
      henkinAx '' {τ : HTup L | τ.2.2.1.val < τ.2.2.2.val} :=
    fun θ hθ => (Finset.mem_filter.mp hθ).2
  obtain ⟨T, hT, hTimg⟩ := Finset.subset_set_image_iff.mp hF
  have hcons := consistent_finite Γ hΓ T (fun τ h => hT (Finset.mem_coe.mpr h))
  refine (inconsistent_iff_provable_one _).mpr (ProvableQ.mono ?_ hpr) hcons
  intro θ hθ
  by_cases h : θ ∈ henkinSet L
  · right
    rw [hTimg]
    exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hθ, h⟩)
  · rcases hΓ₀ hθ with h' | h'
    · exact Or.inl h'
    · exact absurd h' h

end HenkinExt

/-- Proposition 9.2: Existence of a conservative Henkin completion `(L^c, Γ^c)`. -/
theorem exists_henkin_extension (L : Signature) :
    ∃ (Lc : Signature) (ext : SignatureExtension L Lc) (Γc : Set (Formula Lc)),
      (∀ Γ : Set (Formula L), HenkinComplete ((ext.mapFormula '' Γ) ∪ Γc)) ∧
      (∀ Γ : Set (Formula L), ConsistentQ Γ → ConsistentQ ((ext.mapFormula '' Γ) ∪ Γc)) := by
  refine ⟨henkinSig L, henkinExt L, HenkinExt.henkinSet L, fun Γ => ?_, fun Γ hΓ => ?_⟩
  · -- (i): the Henkin axioms are in `Γ^c` by construction.
    intro φ x p q hpq
    exact ⟨HenkinExt.hconst (φ, x, p, q), HenkinExt.hconst_arity _,
      Or.inr ⟨(φ, x, p, q), hpq, rfl⟩⟩
  · -- (ii): compactness reduces to finitely many Henkin axioms.
    exact HenkinExt.consistent_union Γ hΓ

namespace HenkinExt

/-- Replace hypotheses by sets proving them. -/
lemma ProvableQ.replace_hyps {L : Signature} {A B : Set (Formula L)} {φ : Formula L}
    (h : ProvableQ A φ) (hAB : ∀ ψ ∈ A, ProvableQ B ψ) : ProvableQ B φ := by
  induction h with
  | ax hax => exact .ax hax
  | hyp hm => exact hAB _ hm
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

/-- `L^c` with the metric symbol of `LM`. -/
abbrev henkinMSig (LM : MetricSignature) : MetricSignature where
  toSignature := henkinSig LM.toSignature
  distSym := LM.distSym
  distArity := LM.distArity

lemma mapFormula_genList {L : Signature} (xs : List Var) (φ : Formula L) :
    (henkinExt L).mapFormula (Formula.genList xs φ) =
      Formula.genList xs ((henkinExt L).mapFormula φ) := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp only [Formula.genList, SignatureExtension.mapFormula, ih]

lemma mapFormula_dyadic {L : Signature} (d : DyadicCode) :
    (henkinExt L).mapFormula (Formula.dyadic L d) = Formula.dyadic (henkinSig L) d := by
  induction d with
  | one => rfl
  | neg d ih => simp only [Formula.dyadic, SignatureExtension.mapFormula, ih]
  | tsub a b iha ihb => simp only [Formula.dyadic, SignatureExtension.mapFormula, iha, ihb]
  | half d ih => simp only [Formula.dyadic, SignatureExtension.mapFormula, ih]

variable {LM : MetricSignature}

lemma mapFormula_dist (t₀ t₁ : Term LM.toSignature) :
    (henkinExt LM.toSignature).mapFormula (Formula.dist (LM := LM) t₀ t₁) =
      Formula.dist (LM := henkinMSig LM) ((henkinExt _).mapTerm t₀)
        ((henkinExt _).mapTerm t₁) := by
  simp only [Formula.dist, SignatureExtension.mapFormula]
  congr 1
  funext i
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1

lemma mapTerm_func_replaceArg (f : LM.Func) (v : Fin (LM.funcArity f) → Var)
    (i : Fin (LM.funcArity f)) (z : Var) :
    (henkinExt LM.toSignature).mapTerm (.func f (replaceArg (fun j => .var (v j)) i (.var z))) =
      (Term.func (L := henkinSig LM.toSignature) (HCode.base f)
        (replaceArg (fun j => .var (v j)) i (.var z))) := by
  simp only [SignatureExtension.mapTerm]
  congr 1
  funext j
  simp only [replaceArg]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1

lemma mapFormula_rel_replaceArg (P : LM.Rel) (v : Fin (LM.relArity P) → Var)
    (i : Fin (LM.relArity P)) (z : Var) :
    (henkinExt LM.toSignature).mapFormula (.rel P (replaceArg (fun j => .var (v j)) i (.var z))) =
      (Formula.rel (L := henkinSig LM.toSignature) P
        (replaceArg (fun j => .var (v j)) i (.var z))) := by
  simp only [SignatureExtension.mapFormula]
  congr 1
  funext j
  simp only [replaceArg]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1 h2 | exact absurd h2 h1

/-- Every metric axiom of `L^c` is provable from the images of the metric axioms of `L`. -/
lemma metric_ax_provable {ψ : Formula (henkinMSig LM).toSignature}
    (h : ψ ∈ metricAxiomSet (henkinMSig LM)) :
    ProvableQ ((henkinExt LM.toSignature).mapFormula '' metricAxiomSet LM) ψ := by
  obtain ⟨xs, χ, hχ, rfl⟩ := h
  have img : ∀ χ₀ : Formula LM.toSignature, MetricAxiomSchema (LM := LM) χ₀ →
      (henkinExt LM.toSignature).mapFormula χ₀ = χ →
      ProvableQ ((henkinExt LM.toSignature).mapFormula '' metricAxiomSet LM)
        (Formula.genList xs χ) := by
    rintro χ₀ h₀ rfl
    exact .hyp ⟨Formula.genList xs χ₀, ⟨xs, χ₀, h₀, rfl⟩, mapFormula_genList xs χ₀⟩
  cases hχ with
  | base h => exact .ax h
  | A10 x => exact img _ (.A10 x) (mapFormula_dist _ _)
  | A11 x y =>
    exact img _ (.A11 x y) (by simp only [SignatureExtension.mapFormula, mapFormula_dist]; rfl)
  | A12 x y z =>
    exact img _ (.A12 x y z) (by simp only [SignatureExtension.mapFormula, mapFormula_dist]; rfl)
  | A13 f i ε r q v z w h0 h1 hr hq =>
    cases f
    case base f₀ =>
      exact img _ (.A13 (LM := LM) f₀ i ε r q v z w h0 h1 hr hq) (by
        simp only [Formula.minF, SignatureExtension.mapFormula, mapFormula_dist,
          mapFormula_dyadic]
        erw [mapTerm_func_replaceArg f₀ v i z, mapTerm_func_replaceArg f₀ v i w]
        rfl)
    all_goals exact Fin.elim0 i
  | A14 P i ε r q v z w h0 h1 hr hq =>
    exact img (Formula.minF
        (.tsub (Formula.dyadic LM.toSignature q) (Formula.dist (LM := LM) (.var z) (.var w)))
        (.tsub (.tsub (.rel P (replaceArg (fun j => .var (v j)) i (.var z)))
                      (.rel P (replaceArg (fun j => .var (v j)) i (.var w))))
               (Formula.dyadic LM.toSignature r)))
      (.A14 (LM := LM) P i ε r q v z w h0 h1 hr hq) (by
        have e1 := mapFormula_rel_replaceArg (LM := LM) P v i z
        have e2 := mapFormula_rel_replaceArg (LM := LM) P v i w
        have e3 := mapFormula_dist (LM := LM) (.var z) (.var w)
        have e4 := mapFormula_dyadic (L := LM.toSignature) q
        have e5 := mapFormula_dyadic (L := LM.toSignature) r
        show Formula.minF (.tsub ((henkinExt LM.toSignature).mapFormula (Formula.dyadic LM.toSignature q))
            ((henkinExt LM.toSignature).mapFormula (Formula.dist (LM := LM) (.var z) (.var w))))
          (.tsub (.tsub ((henkinExt LM.toSignature).mapFormula (.rel P (replaceArg (fun j => .var (v j)) i (.var z))))
              ((henkinExt LM.toSignature).mapFormula (.rel P (replaceArg (fun j => .var (v j)) i (.var w)))))
            ((henkinExt LM.toSignature).mapFormula (Formula.dyadic LM.toSignature r))) = _
        rw [e1, e2, e3, e4, e5]
        rfl)

end HenkinExt

theorem exists_henkin_extension_metric (LM : MetricSignature) :
    ∃ (LMc : MetricSignature) (ext : SignatureExtension LM.toSignature LMc.toSignature)
      (hdist : ext.relEquiv LM.distSym = LMc.distSym)
      (Γc : Set (Formula LMc.toSignature)),
      (∀ Γ : Set (Formula LM.toSignature), HenkinComplete ((ext.mapFormula '' Γ) ∪ Γc)) ∧
      (∀ Γ : Set (Formula LM.toSignature),
        ConsistentMetricQ Γ → ConsistentMetricQ ((ext.mapFormula '' Γ) ∪ Γc)) := by
  refine ⟨HenkinExt.henkinMSig LM, henkinExt LM.toSignature, rfl,
    HenkinExt.henkinSet LM.toSignature, fun Γ => ?_, fun Γ hΓ => ?_⟩
  · -- (i): as in the non-metric case.
    intro φ x p q hpq
    exact ⟨HenkinExt.hconst (φ, x, p, q), HenkinExt.hconst_arity _,
      Or.inr ⟨(φ, x, p, q), hpq, rfl⟩⟩
  · -- (ii): apply the non-metric case to `Γ ∪ {metric axioms}`; the metric axioms of
    -- `L^c` follow from the images of those of `L`.
    have hΓ' : ConsistentQ (Γ ∪ metricAxiomSet LM) := by
      obtain ⟨φ, hφ⟩ := hΓ
      exact ⟨φ, fun h => hφ ((provableMetricQ_iff_provableQ Γ φ).mpr h)⟩
    obtain ⟨φ, hφ⟩ := HenkinExt.consistent_union _ hΓ'
    refine ⟨φ, fun h => hφ ?_⟩
    rw [provableMetricQ_iff_provableQ] at h
    refine HenkinExt.ProvableQ.replace_hyps h ?_
    rintro ψ ((hψ | hψ) | hψ)
    · obtain ⟨ψ₀, h₀, rfl⟩ := hψ
      exact .hyp (Or.inl ⟨ψ₀, Or.inl h₀, rfl⟩)
    · exact .hyp (Or.inr hψ)
    · refine ProvableQ.mono ?_ (HenkinExt.metric_ax_provable hψ)
      rintro θ ⟨θ₀, h₀, e⟩
      exact Or.inl ⟨θ₀, Or.inr h₀, e⟩

end ContinuousFOL
