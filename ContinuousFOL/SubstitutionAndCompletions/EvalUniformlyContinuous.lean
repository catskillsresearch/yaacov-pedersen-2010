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

/-- Truncated subtraction is 1-Lipschitz in each argument. -/
lemma tsubR.abs_sub_le (a b c d : ℝ) : |(a ∸ b) - (c ∸ d)| ≤ |a - c| + |b - d| := by
  have hmax : |(a ∸ b) - (c ∸ d)| ≤ |(a - b) - (c - d)| := by
    simpa [tsubR] using abs_max_sub_max_le_abs (a - b) (c - d) 0
  refine hmax.trans ?_
  have : (a - b) - (c - d) = (a - c) + -(b - d) := by ring
  rw [this]
  exact (abs_add_le (a - c) (-(b - d))).trans (by simp [abs_sub_comm])

/-- If two bounded families differ by at most `ε` pointwise, their suprema do too. -/
lemma abs_csSup_range_sub_le {ι : Type*} [Nonempty ι] (f g : ι → ℝ) {ε : ℝ}
    (_hε : 0 ≤ ε) (hfg : ∀ i, |f i - g i| ≤ ε)
    (hf1 : ∀ i, f i ≤ 1) (hg1 : ∀ i, g i ≤ 1) :
    |sSup (Set.range f) - sSup (Set.range g)| ≤ ε := by
  have bf : BddAbove (Set.range f) := ⟨1, by rintro _ ⟨i, rfl⟩; exact hf1 i⟩
  have bg : BddAbove (Set.range g) := ⟨1, by rintro _ ⟨i, rfl⟩; exact hg1 i⟩
  have hf : sSup (Set.range f) ≤ sSup (Set.range g) + ε := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    have h1 : f i ≤ g i + ε := by
      linarith [abs_le.mp (hfg i)]
    have h2 : g i ≤ sSup (Set.range g) := le_csSup bg ⟨i, rfl⟩
    linarith
  have hg : sSup (Set.range g) ≤ sSup (Set.range f) + ε := by
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨i, rfl⟩
    have h1 : g i ≤ f i + ε := by
      linarith [abs_le.mp (hfg i)]
    have h2 : f i ≤ sSup (Set.range f) := le_csSup bf ⟨i, rfl⟩
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Remark 5.8: the interpretation of a relation symbol is uniformly continuous
    on `M^{n_P}` with respect to the maximum metric, as a map into `[0, 1]`. -/
lemma relInterp_unif_cont {LM : MetricSignature} (M : MetricPreStructure LM)
    (P : LM.Rel) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ > 0, ∀ (u v : Fin (LM.relArity P) → M.Carrier),
      (∀ i, M.distVal (u i) (v i) < δ) →
      |M.relInterp P u - M.relInterp P v| ≤ ε := by
  if hary : LM.relArity P = 0 then
    refine ⟨1, zero_lt_one, ?_⟩
    intro u v _
    have huv : u = v := by
      ext i
      have := i.isLt
      simp [hary] at this
    rw [huv, sub_self, abs_zero]
    exact hε0.le
  else
    have hkpos : 0 < LM.relArity P := Nat.pos_of_ne_zero hary
    have εk_pos : 0 < ε / LM.relArity P :=
      div_pos hε0 (Nat.cast_pos.mpr hkpos)
    have εk_le : ε / LM.relArity P ≤ 1 := by
      have hk1 : (1 : ℝ) ≤ LM.relArity P := Nat.one_le_cast.mpr (Nat.succ_le_of_lt hkpos)
      exact (div_le_one (Nat.cast_pos.mpr hkpos)).mpr (le_trans hε1 hk1)
    have hne : (Finset.univ : Finset (Fin (LM.relArity P))).Nonempty :=
      ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
    set δ := (Finset.univ : Finset (Fin (LM.relArity P))).inf'
      hne (fun i => LM.relMod P i (ε / LM.relArity P))
    obtain ⟨i0, _, hδeq⟩ := Finset.exists_mem_eq_inf' hne
      (fun i => LM.relMod P i (ε / LM.relArity P))
    have hδpos : 0 < δ := by
      rw [show δ = LM.relMod P i0 (ε / LM.relArity P) from hδeq]
      exact (LM.relMod_pos P i0 (ε / LM.relArity P) εk_pos εk_le).1
    refine ⟨δ, hδpos, ?_⟩
    intro u v huv
    let w : ℕ → (Fin (LM.relArity P) → M.Carrier) :=
      fun m i => if (i : ℕ) < m then v i else u i
    have w0 : w 0 = u := funext fun i => by simp [w]
    have wk : w (LM.relArity P) = v := funext fun i => by
      have hi : (i : ℕ) < LM.relArity P := i.isLt
      simp [w, hi]
    have w_succ : ∀ (m : ℕ) (hm : m < LM.relArity P),
        w (m + 1) = replaceArg (w m) ⟨m, hm⟩ (v ⟨m, hm⟩) := by
      intro m hm
      ext j
      simp only [replaceArg, w]
      by_cases hj : j = ⟨m, hm⟩
      · subst hj
        simp
      · have : ((j : ℕ) < m + 1) ↔ ((j : ℕ) < m) := by
          have hne_m : (j : ℕ) ≠ m := by
            intro hjeq
            apply hj
            ext
            exact hjeq
          omega
        simp [hj, this]
    have step : ∀ m, m ≤ LM.relArity P →
        |M.relInterp P (w 0) - M.relInterp P (w m)| ≤
          m * (ε / LM.relArity P) := by
      intro m
      induction m with
      | zero =>
        intro _
        simp
      | succ m ih =>
        intro hmsucc
        have hm : m < LM.relArity P := Nat.succ_le_iff.mp hmsucc
        have hchain := ih (le_of_lt hm)
        have hw_m : w m ⟨m, hm⟩ = u ⟨m, hm⟩ := by
          simp [w]
        have hdist : M.distVal (w m ⟨m, hm⟩) (v ⟨m, hm⟩) <
            LM.relMod P ⟨m, hm⟩ (ε / LM.relArity P) := by
          rw [hw_m]
          have hδle : δ ≤ LM.relMod P ⟨m, hm⟩ (ε / LM.relArity P) :=
            Finset.inf'_le _ (Finset.mem_univ _)
          exact (huv ⟨m, hm⟩).trans_le hδle
        have hc : replaceArg (w m) ⟨m, hm⟩ (w m ⟨m, hm⟩) = w m :=
          replaceArg_same (w m) ⟨m, hm⟩
        have he : replaceArg (w m) ⟨m, hm⟩ (v ⟨m, hm⟩) = w (m + 1) :=
          (w_succ m hm).symm
        have hfwd := M.rel_unif_cont P ⟨m, hm⟩ (ε / LM.relArity P)
          εk_pos εk_le (w m) (w m ⟨m, hm⟩) (v ⟨m, hm⟩) hdist
        have hbwd := M.rel_unif_cont P ⟨m, hm⟩ (ε / LM.relArity P)
          εk_pos εk_le (w m) (v ⟨m, hm⟩) (w m ⟨m, hm⟩) (by
            rw [M.dist_symm]; exact hdist)
        rw [hc, he] at hfwd hbwd
        have hstep : |M.relInterp P (w m) - M.relInterp P (w (m + 1))| ≤
            ε / LM.relArity P := by
          refine abs_sub_le_iff.mpr ⟨?_, ?_⟩
          · exact (tsubR.le_iff _ _ _ εk_pos.le).mp hfwd
          · exact (tsubR.le_iff _ _ _ εk_pos.le).mp hbwd
        calc
          |M.relInterp P (w 0) - M.relInterp P (w (m + 1))|
            ≤ |M.relInterp P (w 0) - M.relInterp P (w m)| +
              |M.relInterp P (w m) - M.relInterp P (w (m + 1))| :=
            abs_sub_le _ _ _
          _ ≤ (m : ℝ) * (ε / LM.relArity P) + (ε / LM.relArity P) :=
            add_le_add hchain hstep
          _ = ((m + 1 : ℕ) : ℝ) * (ε / LM.relArity P) := by
            push_cast
            ring
    have hfinal := step (LM.relArity P) le_rfl
    rw [w0, wk] at hfinal
    have hcancel : (LM.relArity P : ℝ) * (ε / LM.relArity P) = ε :=
      mul_div_cancel₀ ε (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hkpos))
    rwa [hcancel] at hfinal

/-- Term evaluation is uniformly continuous in the assignment, in the variables
    of the term. -/
lemma term_eval_unif_cont {LM : MetricSignature} (M : MetricPreStructure LM)
    (t : Term LM.toSignature) :
    ∀ ε > 0, ∃ δ > 0, ∀ (σ τ : Var → M.Carrier),
      (∀ v ∈ t.vars, M.distVal (σ v) (τ v) < δ) →
      M.distVal (t.eval M.toPreStructure σ) (t.eval M.toPreStructure τ) ≤ ε := by
  induction t with
  | var x =>
    intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro σ τ h
    simp only [Term.eval]
    exact (h x (by simp [Term.vars])).le
  | func f args ih =>
    intro ε hε
    set ε' := min ε 1 with hε'def
    have hε'0 : 0 < ε' := lt_min hε zero_lt_one
    have hε'1 : ε' ≤ 1 := min_le_right _ _
    obtain ⟨δf, hδf0, hδf⟩ := funcInterp_unif_cont M f hε'0 hε'1
    have hδf2 : 0 < δf / 2 := half_pos hδf0
    have IHj : ∀ j, ∃ δ > 0, ∀ (σ τ : Var → M.Carrier),
        (∀ v ∈ (args j).vars, M.distVal (σ v) (τ v) < δ) →
        M.distVal ((args j).eval M.toPreStructure σ)
          ((args j).eval M.toPreStructure τ) ≤ δf / 2 :=
      fun j => ih j (δf / 2) hδf2
    if hary : LM.funcArity f = 0 then
      refine ⟨1, zero_lt_one, ?_⟩
      intro σ τ _
      have hconst :
          (fun j => (args j).eval M.toPreStructure σ) =
            fun j => (args j).eval M.toPreStructure τ := by
        ext j
        have := j.isLt
        simp [hary] at this
      simp only [Term.eval]
      rw [hconst, M.dist_self]
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
      intro σ τ hστ
      have hcoords : ∀ j,
          M.distVal ((args j).eval M.toPreStructure σ)
            ((args j).eval M.toPreStructure τ) < δf := by
        intro j
        have hle : δ ≤ δj j := Finset.inf'_le _ (Finset.mem_univ j)
        have hvars : ∀ v ∈ (args j).vars, M.distVal (σ v) (τ v) < δj j := by
          intro v hv
          exact (hστ v (by
            simp only [Term.vars, Finset.mem_biUnion]
            exact ⟨j, Finset.mem_univ j, hv⟩)).trans_le hle
        exact (hδj j σ τ hvars).trans_lt (half_lt_self hδf0)
      have hfun :
          M.distVal
            (M.funcInterp f (fun j => (args j).eval M.toPreStructure σ))
            (M.funcInterp f (fun j => (args j).eval M.toPreStructure τ)) ≤ ε' :=
        hδf _ _ hcoords
      simp only [Term.eval]
      exact hfun.trans (min_le_left ε 1)

/-- Formula evaluation is uniformly continuous in the assignment, in the free
    variables of the formula. -/
lemma formula_eval_unif_cont {LM : MetricSignature} (M : MetricPreStructure LM)
    (φ : Formula LM.toSignature) :
    ∀ ε > 0, ∃ δ > 0, ∀ (σ τ : Var → M.Carrier),
      (∀ v ∈ φ.freeVars, M.distVal (σ v) (τ v) < δ) →
      |φ.eval M.toPreStructure σ - φ.eval M.toPreStructure τ| ≤ ε := by
  induction φ with
  | rel P args =>
    intro ε hε
    set ε' := min ε 1 with hε'def
    have hε'0 : 0 < ε' := lt_min hε zero_lt_one
    have hε'1 : ε' ≤ 1 := min_le_right _ _
    obtain ⟨δP, hδP0, hδP⟩ := relInterp_unif_cont M P hε'0 hε'1
    have hδP2 : 0 < δP / 2 := half_pos hδP0
    have IHj : ∀ j, ∃ δ > 0, ∀ (σ τ : Var → M.Carrier),
        (∀ v ∈ (args j).vars, M.distVal (σ v) (τ v) < δ) →
        M.distVal ((args j).eval M.toPreStructure σ)
          ((args j).eval M.toPreStructure τ) ≤ δP / 2 :=
      fun j => term_eval_unif_cont M (args j) (δP / 2) hδP2
    if hary : LM.relArity P = 0 then
      refine ⟨1, zero_lt_one, ?_⟩
      intro σ τ _
      have hconst :
          (fun j => (args j).eval M.toPreStructure σ) =
            fun j => (args j).eval M.toPreStructure τ := by
        ext j
        have := j.isLt
        simp [hary] at this
      simp only [Formula.eval]
      rw [hconst, sub_self, abs_zero]
      exact hε.le
    else
      have hne : (Finset.univ : Finset (Fin (LM.relArity P))).Nonempty :=
        ⟨⟨0, Nat.pos_of_ne_zero hary⟩, Finset.mem_univ _⟩
      choose δj hδj0 hδj using IHj
      set δ := (Finset.univ : Finset (Fin (LM.relArity P))).inf' hne δj
      obtain ⟨j0, _, hδeq⟩ := Finset.exists_mem_eq_inf' hne δj
      have hδpos : 0 < δ := by
        rw [show δ = δj j0 from hδeq]
        exact hδj0 j0
      refine ⟨δ, hδpos, ?_⟩
      intro σ τ hστ
      have hcoords : ∀ j,
          M.distVal ((args j).eval M.toPreStructure σ)
            ((args j).eval M.toPreStructure τ) < δP := by
        intro j
        have hle : δ ≤ δj j := Finset.inf'_le _ (Finset.mem_univ j)
        have hvars : ∀ v ∈ (args j).vars, M.distVal (σ v) (τ v) < δj j := by
          intro v hv
          exact (hστ v (by
            simp only [Formula.freeVars, Finset.mem_biUnion]
            exact ⟨j, Finset.mem_univ j, hv⟩)).trans_le hle
        exact (hδj j σ τ hvars).trans_lt (half_lt_self hδP0)
      simp only [Formula.eval]
      exact (hδP _ _ hcoords).trans (min_le_left ε 1)
  | tsub α β ihα ihβ =>
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨δα, hδα, Hα⟩ := ihα (ε / 2) hε2
    obtain ⟨δβ, hδβ, Hβ⟩ := ihβ (ε / 2) hε2
    refine ⟨min δα δβ, lt_min hδα hδβ, ?_⟩
    intro σ τ hστ
    have hα : ∀ v ∈ α.freeVars, M.distVal (σ v) (τ v) < δα := by
      intro v hv
      exact (hστ v (by simp [Formula.freeVars, hv])).trans_le (min_le_left _ _)
    have hβ : ∀ v ∈ β.freeVars, M.distVal (σ v) (τ v) < δβ := by
      intro v hv
      exact (hστ v (by simp [Formula.freeVars, hv])).trans_le (min_le_right _ _)
    have := tsubR.abs_sub_le (α.eval M.toPreStructure σ) (β.eval M.toPreStructure σ)
      (α.eval M.toPreStructure τ) (β.eval M.toPreStructure τ)
    simp only [Formula.eval]
    exact this.trans <| add_le_add (Hα σ τ hα) (Hβ σ τ hβ) |>.trans (by linarith)
  | neg α ih =>
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := ih ε hε
    refine ⟨δ, hδ, ?_⟩
    intro σ τ hστ
    simp only [Formula.eval, sub_sub_sub_cancel_left, abs_sub_comm]
    exact H σ τ (by intro v hv; exact hστ v (by simpa [Formula.freeVars] using hv))
  | half α ih =>
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := ih ε hε
    refine ⟨δ, hδ, ?_⟩
    intro σ τ hστ
    simp only [Formula.eval]
    rw [← sub_div, abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2)]
    exact (div_le_self (abs_nonneg _) one_le_two).trans (H σ τ (by
      intro v hv; exact hστ v (by simpa [Formula.freeVars] using hv)))
  | sup x α ih =>
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := ih ε hε
    refine ⟨δ, hδ, ?_⟩
    intro σ τ hστ
    have inst : Nonempty M.Carrier := M.nonempty
    simp only [Formula.eval]
    refine abs_csSup_range_sub_le
      (fun a => α.eval M.toPreStructure (updateAssign σ x a))
      (fun a => α.eval M.toPreStructure (updateAssign τ x a))
      hε.le ?_ ?_ ?_
    · intro a
      apply H
      intro v hv
      by_cases hvx : v = x
      · subst hvx
        simp [updateAssign_same, M.dist_self]
        exact hδ
      · have hxv : x ≠ v := fun h => hvx h.symm
        rw [updateAssign_ne σ hxv a, updateAssign_ne τ hxv a]
        exact hστ v (by
          simp only [Formula.freeVars, Finset.mem_erase]
          exact ⟨hvx, hv⟩)
    · intro a; exact (Formula.eval_in_Icc M.toPreStructure _ _).2
    · intro a; exact (Formula.eval_in_Icc M.toPreStructure _ _).2

/-- Theorem 6.8, formula half: `φ̃^{ℳ, x̄} : Mⁿ → [0, 1]` is uniformly continuous. -/
theorem tildeFormula_uniformly_continuous {LM : MetricSignature}
    (M : MetricPreStructure LM) (n : ℕ) (xs : Fin n ↪ Var)
    (φ : Formula LM.toSignature) (hφ : ∀ v ∈ φ.freeVars, v ∈ Set.range xs) :
    ∀ ε > 0, ∃ δ > 0, ∀ (a b : Fin n → M.Carrier),
      (∀ i, M.distVal (a i) (b i) < δ) →
      |tildeFormula M xs φ a - tildeFormula M xs φ b| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := formula_eval_unif_cont M φ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro a b hab
  have hassign : ∀ v ∈ φ.freeVars,
      M.distVal (assignOfTuple M xs a v) (assignOfTuple M xs b v) < δ := by
    intro v hv
    obtain ⟨i, hi⟩ := hφ v hv
    rw [← hi, assignOfTuple_apply, assignOfTuple_apply]
    exact hab i
  simpa [tildeFormula] using H (assignOfTuple M xs a) (assignOfTuple M xs b) hassign

/-- Theorem 6.8: for every term `t` and formula `φ`, the induced mappings
    `t̃^{ℳ, x̄} : Mⁿ → M` and `φ̃^{ℳ, x̄} : Mⁿ → [0, 1]` are uniformly continuous. -/
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
  ⟨fun t ht => tildeTerm_uniformly_continuous M n xs t ht,
    fun φ hφ => tildeFormula_uniformly_continuous M n xs φ hφ⟩

end ContinuousFOL
