/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Definition 6.7 and Theorem 6.8; vision.md page 12–13
-/
module

public import ContinuousFOL.LanguageAndSemantics.MetricPreStructure
public import ContinuousFOL.LanguageAndSemantics.FormulaEval
public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeVars
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-! ### Definition 6.7: induced maps on `M^n` -/

/-- An `ℳ`-assignment `σ` with `σ(xᵢ) = aᵢ`, as used in Definition 6.7.
    Off `{x₀, …, x_{n-1}}` the value is arbitrary; under the variable hypotheses
    of Definition 6.7 the induced maps do not depend on that choice. -/
def assignOfTuple {LM : MetricSignature} {n : ℕ} (M : MetricPreStructure LM)
    (xs : Fin n ↪ Var) (a : Fin n → M.Carrier) : Var → M.Carrier :=
  fun v => if h : ∃ i, xs i = v then a h.choose else Classical.arbitrary M.Carrier

lemma assignOfTuple_apply {LM : MetricSignature} {n : ℕ} (M : MetricPreStructure LM)
    (xs : Fin n ↪ Var) (a : Fin n → M.Carrier) (i : Fin n) :
    assignOfTuple M xs a (xs i) = a i := by
  simp only [assignOfTuple]
  split_ifs with h
  · have : h.choose = i := xs.injective h.choose_spec
    rw [this]
  · exact (h ⟨i, rfl⟩).elim

/-- If two assignments agree on the variables of `t`, they give the same value of `t`. -/
lemma Term.eval_eq_of_eq_on_vars {L : Signature} (M : PreStructure L)
    (σ τ : Var → M.Carrier) (t : Term L) (h : ∀ v ∈ t.vars, σ v = τ v) :
    t.eval M σ = t.eval M τ := by
  induction t with
  | var x =>
    exact h x (by simp [Term.vars])
  | func f args ih =>
    simp only [Term.eval]
    congr 1
    ext i
    exact ih i (fun v hv => h v (by
      simp only [Term.vars, Finset.mem_biUnion]
      exact ⟨i, Finset.mem_univ i, hv⟩))

/-- Definition 6.7: the induced map `t̃^{ℳ, x̄} : Mⁿ → M`.
    Requires that every variable of `t` appears among the distinct `x₀, …, x_{n-1}`
    for the value to be independent of the assignment off those variables. -/
def tildeTerm {LM : MetricSignature} {n : ℕ} (M : MetricPreStructure LM)
    (xs : Fin n ↪ Var) (t : Term LM.toSignature) (a : Fin n → M.Carrier) : M.Carrier :=
  t.eval M.toPreStructure (assignOfTuple M xs a)

/-- Definition 6.7: the induced map `φ̃^{ℳ, x̄} : Mⁿ → [0, 1]`.
    Requires that every free variable of `φ` appears among the distinct `x₀, …, x_{n-1}`
    for the value to be independent of the assignment off those variables. -/
def tildeFormula {LM : MetricSignature} {n : ℕ} (M : MetricPreStructure LM)
    (xs : Fin n ↪ Var) (φ : Formula LM.toSignature) (a : Fin n → M.Carrier) : ℝ :=
  φ.eval M.toPreStructure (assignOfTuple M xs a)

lemma tildeTerm_eq_eval {LM : MetricSignature} {n : ℕ} (M : MetricPreStructure LM)
    (xs : Fin n ↪ Var) (t : Term LM.toSignature) (a : Fin n → M.Carrier)
    (ht : ∀ v ∈ t.vars, v ∈ Set.range xs) (σ : Var → M.Carrier)
    (hσ : ∀ i, σ (xs i) = a i) :
    tildeTerm M xs t a = t.eval M.toPreStructure σ := by
  apply Term.eval_eq_of_eq_on_vars
  intro v hv
  obtain ⟨i, hi⟩ := ht v hv
  rw [← hi, assignOfTuple_apply, hσ]

lemma tildeTerm_func {LM : MetricSignature} {n : ℕ} (M : MetricPreStructure LM)
    (xs : Fin n ↪ Var) (f : LM.Func) (args : Fin (LM.funcArity f) → Term LM.toSignature)
    (a : Fin n → M.Carrier) :
    tildeTerm M xs (.func f args) a =
      M.funcInterp f (fun j => tildeTerm M xs (args j) a) :=
  rfl

lemma replaceArg_same {n : ℕ} {α : Type*} (v : Fin n → α) (i : Fin n) :
    replaceArg v i (v i) = v := by
  ext j
  simp only [replaceArg]
  split_ifs with h
  · rw [h]
  · rfl

/-- Remark 5.8: the interpretation of a function symbol is uniformly continuous
    on `M^{n_f}` with respect to the maximum metric
    `D(ā, b̄) = maxᵢ d^ℳ(aᵢ, bᵢ)`. -/
lemma funcInterp_unif_cont {LM : MetricSignature} (M : MetricPreStructure LM)
    (f : LM.Func) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ > 0, ∀ (u v : Fin (LM.funcArity f) → M.Carrier),
      (∀ i, M.distVal (u i) (v i) < δ) →
      M.distVal (M.funcInterp f u) (M.funcInterp f v) ≤ ε := by
  if hary : LM.funcArity f = 0 then
    refine ⟨1, zero_lt_one, ?_⟩
    intro u v _
    have huv : u = v := by
      ext i
      have := i.isLt
      simp [hary] at this
    rw [huv, M.dist_self]
    exact hε0.le
  else
    have hkpos : 0 < LM.funcArity f := Nat.pos_of_ne_zero hary
    have εk_pos : 0 < ε / LM.funcArity f :=
      div_pos hε0 (Nat.cast_pos.mpr hkpos)
    have εk_le : ε / LM.funcArity f ≤ 1 := by
      have hk1 : (1 : ℝ) ≤ LM.funcArity f := Nat.one_le_cast.mpr (Nat.succ_le_of_lt hkpos)
      exact (div_le_one (Nat.cast_pos.mpr hkpos)).mpr (le_trans hε1 hk1)
    have hne : (Finset.univ : Finset (Fin (LM.funcArity f))).Nonempty :=
      ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
    set δ := (Finset.univ : Finset (Fin (LM.funcArity f))).inf'
      hne (fun i => LM.funcMod f i (ε / LM.funcArity f))
    obtain ⟨i0, _, hδeq⟩ := Finset.exists_mem_eq_inf' hne
      (fun i => LM.funcMod f i (ε / LM.funcArity f))
    have hδpos : 0 < δ := by
      rw [show δ = LM.funcMod f i0 (ε / LM.funcArity f) from hδeq]
      exact (LM.funcMod_pos f i0 (ε / LM.funcArity f) εk_pos εk_le).1
    refine ⟨δ, hδpos, ?_⟩
    intro u v huv
    let w : ℕ → (Fin (LM.funcArity f) → M.Carrier) :=
      fun m i => if (i : ℕ) < m then v i else u i
    have w0 : w 0 = u := funext fun i => by simp [w]
    have wk : w (LM.funcArity f) = v := funext fun i => by
      have hi : (i : ℕ) < LM.funcArity f := i.isLt
      simp [w, hi]
    have w_succ : ∀ (m : ℕ) (hm : m < LM.funcArity f),
        w (m + 1) = replaceArg (w m) ⟨m, hm⟩ (v ⟨m, hm⟩) := by
      intro m hm
      ext j
      simp only [replaceArg, w]
      by_cases hj : j = ⟨m, hm⟩
      · subst hj
        simp
      · have hne_m : (j : ℕ) ≠ m := by
          intro hjeq
          apply hj
          ext
          exact hjeq
        have : ((j : ℕ) < m + 1) ↔ ((j : ℕ) < m) := by
          omega
        simp [hj, this]
    have step : ∀ m, m ≤ LM.funcArity f →
        M.distVal (M.funcInterp f (w 0)) (M.funcInterp f (w m)) ≤
          m * (ε / LM.funcArity f) := by
      intro m
      induction m with
      | zero =>
        intro _
        simp [M.dist_self]
      | succ m ih =>
        intro hmsucc
        have hm : m < LM.funcArity f := Nat.succ_le_iff.mp hmsucc
        have hchain := ih (le_of_lt hm)
        have hw_m : w m ⟨m, hm⟩ = u ⟨m, hm⟩ := by
          simp [w]
        have hdist : M.distVal (w m ⟨m, hm⟩) (v ⟨m, hm⟩) <
            LM.funcMod f ⟨m, hm⟩ (ε / LM.funcArity f) := by
          rw [hw_m]
          have hδle : δ ≤ LM.funcMod f ⟨m, hm⟩ (ε / LM.funcArity f) :=
            Finset.inf'_le _ (Finset.mem_univ _)
          exact (huv ⟨m, hm⟩).trans_le hδle
        have hone := M.func_unif_cont f ⟨m, hm⟩ (ε / LM.funcArity f)
          εk_pos εk_le (w m) (w m ⟨m, hm⟩) (v ⟨m, hm⟩) hdist
        have hc : replaceArg (w m) ⟨m, hm⟩ (w m ⟨m, hm⟩) = w m :=
          replaceArg_same (w m) ⟨m, hm⟩
        have he : replaceArg (w m) ⟨m, hm⟩ (v ⟨m, hm⟩) = w (m + 1) :=
          (w_succ m hm).symm
        rw [hc, he] at hone
        calc
          M.distVal (M.funcInterp f (w 0)) (M.funcInterp f (w (m + 1)))
            ≤ M.distVal (M.funcInterp f (w 0)) (M.funcInterp f (w m)) +
              M.distVal (M.funcInterp f (w m)) (M.funcInterp f (w (m + 1))) :=
            M.dist_triangle _ _ _
          _ ≤ (m : ℝ) * (ε / LM.funcArity f) + (ε / LM.funcArity f) :=
            add_le_add hchain hone
          _ = ((m + 1 : ℕ) : ℝ) * (ε / LM.funcArity f) := by
            push_cast
            ring
    have hfinal := step (LM.funcArity f) le_rfl
    rw [w0, wk] at hfinal
    have hcancel : (LM.funcArity f : ℝ) * (ε / LM.funcArity f) = ε :=
      mul_div_cancel₀ ε (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hkpos))
    rwa [hcancel] at hfinal

/-- Theorem 6.8, term half: `t̃^{ℳ, x̄} : Mⁿ → M` is uniformly continuous. -/
theorem tildeTerm_uniformly_continuous {LM : MetricSignature}
    (M : MetricPreStructure LM) (n : ℕ) (xs : Fin n ↪ Var)
    (t : Term LM.toSignature) (ht : ∀ v ∈ t.vars, v ∈ Set.range xs) :
    ∀ ε > 0, ∃ δ > 0, ∀ (a b : Fin n → M.Carrier),
      (∀ i, M.distVal (a i) (b i) < δ) →
      M.distVal (tildeTerm M xs t a) (tildeTerm M xs t b) ≤ ε := by
  induction t with
  | var x =>
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro a b hab
    obtain ⟨j, hj⟩ := ht x (by simp [Term.vars])
    have ha : tildeTerm M xs (.var x) a = a j := by
      simp only [tildeTerm, Term.eval]
      rw [← hj, assignOfTuple_apply]
    have hb : tildeTerm M xs (.var x) b = b j := by
      simp only [tildeTerm, Term.eval]
      rw [← hj, assignOfTuple_apply]
    rw [ha, hb]
    exact (hab j).le
  | func f args ih =>
    intro ε hε
    set ε' := min ε 1 with hε'def
    have hε'0 : 0 < ε' := lt_min hε zero_lt_one
    have hε'1 : ε' ≤ 1 := min_le_right _ _
    obtain ⟨δf, hδf0, hδf⟩ := funcInterp_unif_cont M f hε'0 hε'1
    have htj : ∀ j, ∀ v ∈ (args j).vars, v ∈ Set.range xs := by
      intro j v hv
      apply ht v
      simp only [Term.vars, Finset.mem_biUnion]
      exact ⟨j, Finset.mem_univ j, hv⟩
    have hδf2 : 0 < δf / 2 := half_pos hδf0
    have IHj : ∀ j, ∃ δ > 0, ∀ (a b : Fin n → M.Carrier),
        (∀ i, M.distVal (a i) (b i) < δ) →
        M.distVal (tildeTerm M xs (args j) a) (tildeTerm M xs (args j) b) ≤ δf / 2 :=
      fun j => ih j (htj j) (δf / 2) hδf2
    if hary : LM.funcArity f = 0 then
      refine ⟨1, zero_lt_one, ?_⟩
      intro a b _
      have hconst :
          (fun j => tildeTerm M xs (args j) a) =
            fun j => tildeTerm M xs (args j) b := by
        ext j
        have := j.isLt
        simp [hary] at this
      rw [tildeTerm_func, tildeTerm_func, hconst, M.dist_self]
      exact hε.le
    else
      have hne : (Finset.univ : Finset (Fin (LM.funcArity f))).Nonempty :=
        ⟨⟨0, Nat.pos_of_ne_zero hary⟩, Finset.mem_univ _⟩
      choose δj hδj0 hδj using IHj
      set δ := (Finset.univ : Finset (Fin (LM.funcArity f))).inf' hne δj
      obtain ⟨j0, _, hδeq⟩ := Finset.exists_mem_eq_inf' hne δj
      have hδpos : 0 < δ := by
        rw [show δ = δj j0 from hδeq]
        exact hδj0 j0
      refine ⟨δ, hδpos, ?_⟩
      intro a b hab
      have hcoords : ∀ j,
          M.distVal (tildeTerm M xs (args j) a) (tildeTerm M xs (args j) b) < δf := by
        intro j
        have hle : δ ≤ δj j := Finset.inf'_le _ (Finset.mem_univ j)
        have hbound := hδj j a b (fun i => (hab i).trans_le hle)
        exact hbound.trans_lt (half_lt_self hδf0)
      have hfun :
          M.distVal
            (M.funcInterp f (fun j => tildeTerm M xs (args j) a))
            (M.funcInterp f (fun j => tildeTerm M xs (args j) b)) ≤ ε' :=
        hδf _ _ hcoords
      rw [tildeTerm_func, tildeTerm_func]
      exact hfun.trans (min_le_left ε 1)

/-- Theorem 6.8: for every term `t` and formula `φ`, the induced mappings
    `t̃^{ℳ, x̄} : Mⁿ → M` and `φ̃^{ℳ, x̄} : Mⁿ → [0, 1]` are uniformly continuous.
    The term half is proved as `tildeTerm_uniformly_continuous`; the formula half
    remains `sorry`. -/
theorem eval_uniformly_continuous {LM : MetricSignature} (M : MetricPreStructure LM)
    (n : ℕ) (xs : Fin n ↪ Var) :
    (∀ (t : Term LM.toSignature), (∀ v ∈ t.vars, v ∈ Set.range xs) →
      ∀ ε > 0, ∃ δ > 0, ∀ (a b : Fin n → M.Carrier),
        (∀ i, M.distVal (a i) (b i) < δ) →
        M.distVal (tildeTerm M xs t a) (tildeTerm M xs t b) ≤ ε) ∧
    (∀ (φ : Formula LM.toSignature), (∀ v ∈ φ.freeVars, v ∈ Set.range xs) →
      ∀ ε > 0, ∃ δ > 0, ∀ (a b : Fin n → M.Carrier),
        (∀ i, M.distVal (a i) (b i) < δ) →
        |tildeFormula M xs φ a - tildeFormula M xs φ b| ≤ ε) :=
  ⟨fun t ht => tildeTerm_uniformly_continuous M n xs t ht, fun φ hφ => by
    sorry⟩

end ContinuousFOL
