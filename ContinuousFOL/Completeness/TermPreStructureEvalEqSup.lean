/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Truth Lemma / Theorem 9.4 core; vision.md page 21–23
-/
module

public import ContinuousFOL.Completeness.TermPreStructure
public import ContinuousFOL.Completeness.HenkinComplete
public import ContinuousFOL.Essentials.MaximalConsistent

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Lower dyadic cut `{p ∈ 𝔻 : p ∸ φ ∈ Δ}`. -/
def lowerCut {L : Signature} (Δ : Set (Formula L)) (φ : Formula L) : Set ℝ :=
  {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ Formula.tsub (Formula.dyadic L p) φ ∈ Δ}

/-- Upper dyadic cut `{q ∈ 𝔻 : φ ∸ q ∈ Δ}`. -/
def upperCut {L : Signature} (Δ : Set (Formula L)) (φ : Formula L) : Set ℝ :=
  {r : ℝ | ∃ q : DyadicCode, r = q.val ∧ Formula.tsub φ (Formula.dyadic L q) ∈ Δ}

/-- Instantiate a CL tautology given by an explicit propositional form. -/
lemma ProvableQ.cl_inst {L : Signature} {Γ : Set (Formula L)} {n : ℕ}
    (T : CLPropForm (Fin n)) (f : Fin n → Formula L) {θ : Formula L}
    (hθ : T.toFormula f = θ)
    (hv : ∀ v : Fin n → ℝ, (∀ i, 0 ≤ v i ∧ v i ≤ 1) → T.eval v = 0) :
    ProvableQ Γ θ := by
  subst hθ
  exact CLPropForm.toFormula_provable_of_valid f T hv

namespace MaximalConsistent

variable {L : Signature} {Δ : Set (Formula L)}

lemma mem_of_taut1 (hmc : MaximalConsistent Δ) {C H : Formula L}
    (hT : ProvableQ Δ (.tsub C H)) (hH : H ∈ Δ) : C ∈ Δ :=
  (hmc.mem_iff_provable _).mpr (ProvableQ.mp (.hyp hH) hT)

lemma mem_of_taut2 (hmc : MaximalConsistent Δ) {C H₁ H₂ : Formula L}
    (hT : ProvableQ Δ (.tsub (.tsub C H₁) H₂)) (h₁ : H₁ ∈ Δ) (h₂ : H₂ ∈ Δ) : C ∈ Δ :=
  (hmc.mem_iff_provable _).mpr (ProvableQ.mp (.hyp h₁) (ProvableQ.mp (.hyp h₂) hT))

lemma mem_of_taut3 (hmc : MaximalConsistent Δ) {C H₁ H₂ H₃ : Formula L}
    (hT : ProvableQ Δ (.tsub (.tsub (.tsub C H₁) H₂) H₃)) (h₁ : H₁ ∈ Δ) (h₂ : H₂ ∈ Δ)
    (h₃ : H₃ ∈ Δ) : C ∈ Δ :=
  (hmc.mem_iff_provable _).mpr
    (ProvableQ.mp (.hyp h₁) (ProvableQ.mp (.hyp h₂) (ProvableQ.mp (.hyp h₃) hT)))

/-- A dyadic constant of positive value is never in a maximal consistent set. -/
lemma val_nonpos_of_mem (hmc : MaximalConsistent Δ) {d : DyadicCode}
    (h : Formula.dyadic L d ∈ Δ) : d.val ≤ 0 := by
  by_contra hpos
  push Not at hpos
  exact (inconsistent_iff_provable_one Δ).mpr
    (ProvableQ.one_of_dyadic_pos d hpos (.hyp h)) hmc.consistent

lemma zero_mem_lowerCut (hmc : MaximalConsistent Δ) (φ : Formula L) :
    (0 : ℝ) ∈ lowerCut Δ φ :=
  ⟨.zero, DyadicCode.val_zero.symm, (hmc.mem_iff_provable _).mpr (ProvableQ.zero_tsub Δ φ)⟩

lemma one_mem_upperCut (hmc : MaximalConsistent Δ) (φ : Formula L) :
    (1 : ℝ) ∈ upperCut Δ φ :=
  ⟨.one, DyadicCode.val_one.symm, (hmc.mem_iff_provable _).mpr (ProvableQ.tsub_one Δ φ)⟩

lemma bddAbove_lowerCut (φ : Formula L) : BddAbove (lowerCut Δ φ) :=
  ⟨1, by rintro _ ⟨p, rfl, -⟩; exact (DyadicCode.val_mem_Icc p).2⟩

lemma bddBelow_upperCut (φ : Formula L) : BddBelow (upperCut Δ φ) :=
  ⟨0, by rintro _ ⟨q, rfl, -⟩; exact (DyadicCode.val_mem_Icc q).1⟩

lemma sSup_lowerCut_eq (hmc : MaximalConsistent Δ) (φ : Formula L) :
    sSup (lowerCut Δ φ) = sInf (upperCut Δ φ) :=
  maximal_consistent_sup_eq_inf hmc.consistent hmc (Set.Subset.rfl) φ

lemma le_sSup_lowerCut (hmc : MaximalConsistent Δ) {φ : Formula L} {p : DyadicCode}
    (h : Formula.tsub (Formula.dyadic L p) φ ∈ Δ) : p.val ≤ sSup (lowerCut Δ φ) := by
  have _ := hmc
  exact le_csSup (bddAbove_lowerCut φ) ⟨p, rfl, h⟩

lemma sSup_lowerCut_le (hmc : MaximalConsistent Δ) {φ : Formula L} {q : DyadicCode}
    (h : Formula.tsub φ (Formula.dyadic L q) ∈ Δ) : sSup (lowerCut Δ φ) ≤ q.val := by
  rw [hmc.sSup_lowerCut_eq φ]
  exact csInf_le (bddBelow_upperCut φ) ⟨q, rfl, h⟩

/-- Squeeze: a real bounded by the two cuts equals `sup {p : p ∸ φ ∈ Δ}`. -/
lemma eq_sSup_lowerCut (hmc : MaximalConsistent Δ) (φ : Formula L) (x : ℝ)
    (hl : ∀ p : DyadicCode, Formula.tsub (Formula.dyadic L p) φ ∈ Δ → p.val ≤ x)
    (hu : ∀ q : DyadicCode, Formula.tsub φ (Formula.dyadic L q) ∈ Δ → x ≤ q.val) :
    x = sSup (lowerCut Δ φ) := by
  apply le_antisymm
  · rw [hmc.sSup_lowerCut_eq φ]
    exact le_csInf ⟨1, hmc.one_mem_upperCut φ⟩ (by rintro _ ⟨q, rfl, hq⟩; exact hu q hq)
  · exact csSup_le ⟨0, hmc.zero_mem_lowerCut φ⟩ (by rintro _ ⟨p, rfl, hp⟩; exact hl p hp)

lemma exists_upper (hmc : MaximalConsistent Δ) (φ : Formula L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : DyadicCode, Formula.tsub φ (Formula.dyadic L r) ∈ Δ ∧
      r.val < sSup (lowerCut Δ φ) + δ := by
  rw [hmc.sSup_lowerCut_eq φ]
  obtain ⟨_, ⟨r, rfl, hr⟩, hlt⟩ :=
    exists_lt_of_csInf_lt ⟨1, hmc.one_mem_upperCut φ⟩ (lt_add_of_pos_right _ hδ)
  exact ⟨r, hr, hlt⟩

lemma exists_lower (hmc : MaximalConsistent Δ) (φ : Formula L) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : DyadicCode, Formula.tsub (Formula.dyadic L s) φ ∈ Δ ∧
      sSup (lowerCut Δ φ) - δ < s.val := by
  obtain ⟨_, ⟨s, rfl, hs⟩, hlt⟩ :=
    exists_lt_of_lt_csSup ⟨0, hmc.zero_mem_lowerCut φ⟩ (sub_lt_self _ hδ)
  exact ⟨s, hs, hlt⟩

end MaximalConsistent

namespace TruthLemma

variable {L : Signature} {Δ : Set (Formula L)}

open MaximalConsistent

/-- `¬`-case of the truth lemma. -/
lemma neg_case (hmc : MaximalConsistent Δ) (α : Formula L)
    (ha : ∀ p : DyadicCode, Formula.tsub (Formula.dyadic L p) α ∈ Δ →
      p.val ≤ sSup (lowerCut Δ α))
    (hb : ∀ q : DyadicCode, Formula.tsub α (Formula.dyadic L q) ∈ Δ →
      sSup (lowerCut Δ α) ≤ q.val) :
    1 - sSup (lowerCut Δ α) = sSup (lowerCut Δ (.neg α)) := by
  apply hmc.eq_sSup_lowerCut
  · intro p hp
    have hC : Formula.tsub α (Formula.dyadic L (.neg p)) ∈ Δ :=
      hmc.mem_of_taut1 (ProvableQ.cl_inst
        (.tsub (.tsub (.var 0) (.neg (.var 1))) (.tsub (.var 1) (.neg (.var 0))))
        ![α, Formula.dyadic L p] rfl (by
          intro v _
          simp only [CLPropForm.eval, tsubR, max_def]
          split_ifs <;> linarith)) hp
    have := hb _ hC
    simp only [DyadicCode.val] at this
    linarith
  · intro q hq
    have hC : Formula.tsub (Formula.dyadic L (.neg q)) α ∈ Δ :=
      hmc.mem_of_taut1 (ProvableQ.cl_inst
        (.tsub (.tsub (.neg (.var 1)) (.var 0)) (.tsub (.neg (.var 0)) (.var 1)))
        ![α, Formula.dyadic L q] rfl (by
          intro v _
          simp only [CLPropForm.eval, tsubR, max_def]
          split_ifs <;> linarith)) hq
    have := ha _ hC
    simp only [DyadicCode.val] at this
    linarith

/-- `½`-case of the truth lemma. -/
lemma half_case (hmc : MaximalConsistent Δ) (α : Formula L)
    (ha : ∀ p : DyadicCode, Formula.tsub (Formula.dyadic L p) α ∈ Δ →
      p.val ≤ sSup (lowerCut Δ α))
    (hb : ∀ q : DyadicCode, Formula.tsub α (Formula.dyadic L q) ∈ Δ →
      sSup (lowerCut Δ α) ≤ q.val) :
    sSup (lowerCut Δ α) / 2 = sSup (lowerCut Δ (.half α)) := by
  apply hmc.eq_sSup_lowerCut
  · intro p hp
    -- `¬(¬p ∸ p) ∸ α ∈ Δ` and `p ∸ ½ ∈ Δ`.
    have hC1 : Formula.tsub (Formula.dyadic L (.neg (.tsub (.neg p) p))) α ∈ Δ :=
      hmc.mem_of_taut2 (ProvableQ.cl_inst
        (.tsub (.tsub (.tsub (.neg (.tsub (.neg (.var 1)) (.var 1))) (.var 0))
          (.tsub (.var 1) (.half (.var 0)))) (.tsub (.var 1) (.half (.var 0))))
        ![α, Formula.dyadic L p] rfl (by
          intro v hv
          obtain ⟨h0, h0'⟩ := hv 0
          obtain ⟨h1, h1'⟩ := hv 1
          simp only [CLPropForm.eval, tsubR, max_def]
          split_ifs <;> linarith)) hp hp
    have hC2 : Formula.dyadic L (.tsub p (.half .one)) ∈ Δ :=
      hmc.mem_of_taut1 (ProvableQ.cl_inst
        (.tsub (.tsub (.var 1) (.half (CLPropForm.one (.var 2))))
          (.tsub (.var 1) (.half (.var 0))))
        ![α, Formula.dyadic L p, Formula.defaultAtom L] rfl (by
          intro v hv
          obtain ⟨h0, h0'⟩ := hv 0
          simp only [CLPropForm.one, CLPropForm.eval, tsubR, max_def]
          split_ifs <;> linarith)) hp
    have h1 := ha _ hC1
    have h2 := hmc.val_nonpos_of_mem hC2
    have hp0 := (DyadicCode.val_mem_Icc p).1
    simp only [DyadicCode.val, tsubR, max_def] at h1 h2
    split_ifs at h1 h2 <;> linarith
  · intro q hq
    have hC : Formula.tsub α (Formula.dyadic L (.neg (.tsub (.neg q) q))) ∈ Δ :=
      hmc.mem_of_taut2 (ProvableQ.cl_inst
        (.tsub (.tsub (.tsub (.var 0) (.neg (.tsub (.neg (.var 1)) (.var 1))))
          (.tsub (.half (.var 0)) (.var 1))) (.tsub (.half (.var 0)) (.var 1)))
        ![α, Formula.dyadic L q] rfl (by
          intro v hv
          obtain ⟨h0, h0'⟩ := hv 0
          obtain ⟨h1, h1'⟩ := hv 1
          simp only [CLPropForm.eval, tsubR, max_def]
          split_ifs <;> linarith)) hq hq
    have h1 := hb _ hC
    have hq0 := (DyadicCode.val_mem_Icc q).1
    simp only [DyadicCode.val, tsubR, max_def] at h1
    split_ifs at h1 <;> linarith

end TruthLemma

namespace TruthLemma

variable {L : Signature} {Δ : Set (Formula L)}

open MaximalConsistent

lemma tsubR3_zero {c h₁ h₂ h₃ : ℝ} (h : c ≤ h₁ + h₂ + h₃) (h₂0 : 0 ≤ h₂) (h₃0 : 0 ≤ h₃) :
    ((c ∸ h₁) ∸ h₂) ∸ h₃ = 0 := by
  simp only [tsubR, max_def]
  split_ifs <;> linarith

lemma tsub_bound_lower (p r s a b : ℝ) :
    p ∸ (r ∸ s) ≤ (p ∸ (a ∸ b)) + (a ∸ r) + (s ∸ b) := by
  simp only [tsubR]
  have e1 := le_max_left (p - max (a - b) 0) 0
  have e2 := le_max_left (a - r) 0
  have e3 := le_max_left (s - b) 0
  have e4 := le_max_right (p - max (a - b) 0) 0
  have e5 := le_max_right (a - r) 0
  have e6 := le_max_right (s - b) 0
  have e7 : max (a - b) 0 ≤ max (r - s) 0 + max (a - r) 0 + max (s - b) 0 :=
    max_le (by linarith [le_max_left (r - s) 0]) (by linarith [le_max_right (r - s) 0])
  exact max_le (by linarith) (by linarith)

lemma tsub_bound_upper (q r s a b : ℝ) :
    (r ∸ s) ∸ q ≤ ((a ∸ b) ∸ q) + (r ∸ a) + (b ∸ s) := by
  simp only [tsubR]
  have e1 := le_max_left (max (a - b) 0 - q) 0
  have e2 := le_max_left (r - a) 0
  have e3 := le_max_left (b - s) 0
  have e4 := le_max_right (max (a - b) 0 - q) 0
  have e5 := le_max_right (r - a) 0
  have e6 := le_max_right (b - s) 0
  have e7 : max (r - s) 0 ≤ max (a - b) 0 + max (r - a) 0 + max (b - s) 0 :=
    max_le (by linarith [le_max_left (a - b) 0]) (by linarith [le_max_right (a - b) 0])
  exact max_le (by linarith) (by linarith)

/-- `∸`-case of the truth lemma. -/
lemma tsub_case (hmc : MaximalConsistent Δ) (α β : Formula L) :
    sSup (lowerCut Δ α) ∸ sSup (lowerCut Δ β) = sSup (lowerCut Δ (.tsub α β)) := by
  have hab0 : 0 ≤ sSup (lowerCut Δ α) ∸ sSup (lowerCut Δ β) := tsubR.nonneg _ _
  have hab1 : sSup (lowerCut Δ α) - sSup (lowerCut Δ β) ≤
      sSup (lowerCut Δ α) ∸ sSup (lowerCut Δ β) := le_max_left _ _
  apply hmc.eq_sSup_lowerCut
  · intro p hp
    by_contra hlt
    push Not at hlt
    set a := sSup (lowerCut Δ α)
    set b := sSup (lowerCut Δ β)
    have hδ0 : 0 < (p.val - (a ∸ b)) / 3 := by linarith
    obtain ⟨r, hr, hra⟩ := hmc.exists_upper α hδ0
    obtain ⟨s, hs, hsb⟩ := hmc.exists_lower β hδ0
    have hC : Formula.dyadic L (.tsub p (.tsub r s)) ∈ Δ :=
      hmc.mem_of_taut3 (ProvableQ.cl_inst
        (.tsub (.tsub (.tsub (.tsub (.var 2) (.tsub (.var 3) (.var 4)))
          (.tsub (.var 2) (.tsub (.var 0) (.var 1)))) (.tsub (.var 0) (.var 3)))
          (.tsub (.var 4) (.var 1)))
        ![α, β, Formula.dyadic L p, Formula.dyadic L r, Formula.dyadic L s] rfl (by
          intro v _
          exact tsubR3_zero (tsub_bound_lower _ _ _ _ _) (tsubR.nonneg _ _) (tsubR.nonneg _ _))) hp hr hs
    have h := hmc.val_nonpos_of_mem hC
    simp only [DyadicCode.val] at h
    have h' : p.val - (r.val ∸ s.val) ≤ 0 := le_trans (le_max_left _ _) h
    rcases le_total (r.val - s.val) 0 with hrs | hrs
    · rw [tsubR.def_eq, max_eq_right hrs] at h'
      linarith
    · rw [tsubR.def_eq, max_eq_left hrs] at h'
      linarith
  · intro q hq
    by_contra hlt
    push Not at hlt
    set a := sSup (lowerCut Δ α)
    set b := sSup (lowerCut Δ β)
    have hq0 := (DyadicCode.val_mem_Icc q).1
    have hpos : 0 < a ∸ b := by linarith
    have hab : a ∸ b = a - b := by
      rw [tsubR.def_eq]
      apply max_eq_left
      by_contra h
      push Not at h
      rw [tsubR.def_eq, max_eq_right h.le] at hpos
      exact lt_irrefl _ hpos
    rw [hab] at hlt
    have hδ0 : 0 < (a - b - q.val) / 3 := by linarith
    obtain ⟨s, hs, hsb⟩ := hmc.exists_upper β hδ0
    obtain ⟨r, hr, hra⟩ := hmc.exists_lower α hδ0
    have hC : Formula.dyadic L (.tsub (.tsub r s) q) ∈ Δ :=
      hmc.mem_of_taut3 (ProvableQ.cl_inst
        (.tsub (.tsub (.tsub (.tsub (.tsub (.var 3) (.var 4)) (.var 2))
          (.tsub (.tsub (.var 0) (.var 1)) (.var 2))) (.tsub (.var 3) (.var 0)))
          (.tsub (.var 1) (.var 4)))
        ![α, β, Formula.dyadic L q, Formula.dyadic L r, Formula.dyadic L s] rfl (by
          intro v _
          exact tsubR3_zero (tsub_bound_upper _ _ _ _ _) (tsubR.nonneg _ _) (tsubR.nonneg _ _))) hq hr hs
    have h := hmc.val_nonpos_of_mem hC
    simp only [DyadicCode.val] at h
    have h' : (r.val ∸ s.val) - q.val ≤ 0 := le_trans (le_max_left _ _) h
    have h'' : r.val - s.val ≤ r.val ∸ s.val := le_max_left _ _
    linarith

lemma Term.vars_const (c : L.Func) (hc : L.funcArity c = 0)
    (args : Fin (L.funcArity c) → Term L) : (Term.func c args).vars = ∅ := by
  have : IsEmpty (Fin (L.funcArity c)) := by rw [hc]; infer_instance
  simp [Term.vars]

end TruthLemma

/-- Truth Lemma for the Henkin term model (core induction of Theorem 9.4):
    `𝔐(φ, σ) = sup { p ∈ D : p ∸ φ ∈ Δ }`. -/
theorem termPreStructure_eval_eq_sup {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (hhenk : HenkinComplete Δ) (φ : Formula L) :
    φ.eval (termPreStructure Δ) (idTermAssign L) =
      sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
        Formula.tsub (Formula.dyadic L p) φ ∈ Δ} := by
  change _ = sSup (lowerCut Δ φ)
  suffices key : ∀ (n : ℕ) (φ : Formula L), φ.rank = n →
      φ.eval (termPreStructure Δ) (idTermAssign L) = sSup (lowerCut Δ φ) from key _ φ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro φ hφ
  cases φ with
  | rel P args =>
    simp only [Formula.eval, term_eval_idTermAssign]
    rfl
  | tsub α β =>
    simp only [Formula.rank] at hφ
    simp only [Formula.eval]
    rw [ih _ (by omega) α rfl, ih _ (by omega) β rfl]
    exact TruthLemma.tsub_case hmc α β
  | neg α =>
    simp only [Formula.rank] at hφ
    simp only [Formula.eval]
    rw [ih _ (by omega) α rfl]
    exact TruthLemma.neg_case hmc α (fun _ h => hmc.le_sSup_lowerCut h)
      (fun _ h => hmc.sSup_lowerCut_le h)
  | half α =>
    simp only [Formula.rank] at hφ
    simp only [Formula.eval]
    rw [ih _ (by omega) α rfl]
    exact TruthLemma.half_case hmc α (fun _ h => hmc.le_sSup_lowerCut h)
      (fun _ h => hmc.sSup_lowerCut_le h)
  | sup x ψ =>
    simp only [Formula.rank] at hφ
    have IH : ∀ θ : Formula L, θ.rank = ψ.rank →
        θ.eval (termPreStructure Δ) (idTermAssign L) = sSup (lowerCut Δ θ) :=
      fun θ hθ => ih _ (by omega) θ hθ
    simp only [Formula.eval]
    have hne : (Set.range fun t : (termPreStructure Δ).Carrier =>
        ψ.eval (termPreStructure Δ) (updateAssign (idTermAssign L) x t)).Nonempty :=
      Set.range_nonempty _
    have hbdd : BddAbove (Set.range fun t : (termPreStructure Δ).Carrier =>
        ψ.eval (termPreStructure Δ) (updateAssign (idTermAssign L) x t)) :=
      ⟨1, by rintro _ ⟨t, rfl⟩; exact (Formula.eval_in_Icc _ _ ψ).2⟩
    apply hmc.eq_sSup_lowerCut
    · -- (a): Henkin witnesses.
      intro p hp
      by_contra hlt
      push Not at hlt
      have hW0 : 0 ≤ sSup (Set.range fun t : (termPreStructure Δ).Carrier =>
          ψ.eval (termPreStructure Δ) (updateAssign (idTermAssign L) x t)) :=
        le_trans (Formula.eval_in_Icc _ _ ψ).1 (le_csSup hbdd ⟨Term.var 0, rfl⟩)
      obtain ⟨p₁, hp₁W, hp₁p⟩ :=
        DyadicCode.dense_in_Icc hW0 (DyadicCode.val_mem_Icc p).2 hlt
      obtain ⟨q₁, hq₁p₁, hq₁p⟩ :=
        DyadicCode.dense_in_Icc (le_trans hW0 hp₁W.le) (DyadicCode.val_mem_Icc p).2 hp₁p
      obtain ⟨c, hc, hmin⟩ := hhenk ψ x p₁ q₁ hq₁p₁
      simp only at hmin
      rcases hmc.comparable (.tsub (.sup x ψ) (Formula.dyadic L q₁))
          (.tsub (Formula.dyadic L p₁)
            (ψ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x)) with hAB | hBA
      · have hA := hmc.mem_of_taut2 (ProvableQ.cl_inst
          (.tsub (.tsub (.var 0) (.tsub (.var 0) (.tsub (.var 0) (.var 1))))
            (.tsub (.var 0) (.var 1)))
          ![Formula.tsub (.sup x ψ) (Formula.dyadic L q₁),
            Formula.tsub (Formula.dyadic L p₁)
              (ψ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x)] rfl (by
            intro v _
            simp only [CLPropForm.eval, tsubR, max_def]
            split_ifs <;> linarith)) hmin hAB
        have hpq : Formula.dyadic L (.tsub p q₁) ∈ Δ :=
          (hmc.mem_iff_provable _).mpr (ProvableQ.tsub_trans (.hyp hp) (.hyp hA))
        have h := hmc.val_nonpos_of_mem hpq
        simp only [DyadicCode.val] at h
        have h' : p.val - q₁.val ≤ 0 := le_trans (le_max_left _ _) h
        linarith
      · have hB := hmc.mem_of_taut2 (ProvableQ.cl_inst
          (.tsub (.tsub (.var 1) (.tsub (.var 0) (.tsub (.var 0) (.var 1))))
            (.tsub (.var 1) (.var 0)))
          ![Formula.tsub (.sup x ψ) (Formula.dyadic L q₁),
            Formula.tsub (Formula.dyadic L p₁)
              (ψ.freeSubst (.func c fun i => Fin.elim0 (Fin.cast hc i)) x)] rfl (by
            intro v _
            simp only [CLPropForm.eval, tsubR, max_def]
            split_ifs <;> linarith)) hmin hBA
        have hcorr : ψ.FreeSubstCorrect (.func c fun i => Fin.elim0 (Fin.cast hc i)) x :=
          Formula.freeSubstCorrect_of_disjoint ψ _ x
            (by rw [TruthLemma.Term.vars_const c hc]; exact Finset.disjoint_empty_left _)
        have h1 := hmc.le_sSup_lowerCut hB
        have e0 := IH _ (Formula.rank_freeSubst ψ
          (Term.func c fun i => Fin.elim0 (Fin.cast hc i)) x)
        have e := substitution_lemma (termPreStructure Δ) (idTermAssign L)
          (Term.func c fun i => Fin.elim0 (Fin.cast hc i)) x ψ hcorr
        have h2 := le_csSup hbdd ⟨Term.eval (termPreStructure Δ) (idTermAssign L)
          (Term.func c fun i => Fin.elim0 (Fin.cast hc i)), rfl⟩
        linarith
    · -- (b): Lemmas 8.11 and 8.12.
      intro q hq
      apply csSup_le hne
      rintro _ ⟨t, rfl⟩
      obtain ⟨ψ', heq, hrank, hcorr, hmem⟩ := maximal_consistent_sup_instantiate_aux hmc t x ψ q hq
      have h1 := hmc.sSup_lowerCut_le hmem
      have e0 := IH _ ((Formula.rank_freeSubst ψ' t x).trans hrank)
      have e := substitution_lemma (termPreStructure Δ) (idTermAssign L) t x ψ' hcorr
      have e2 : Term.eval (termPreStructure Δ) (idTermAssign L) t = t :=
        term_eval_idTermAssign Δ t
      rw [e2] at e
      show ψ.eval (termPreStructure Δ) (updateAssign (idTermAssign L) x t) ≤ q.val
      rw [heq (termPreStructure Δ) (updateAssign (idTermAssign L) x t)]
      linarith

end ContinuousFOL
