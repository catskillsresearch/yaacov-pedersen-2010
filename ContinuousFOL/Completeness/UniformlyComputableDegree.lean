/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Corollary 9.11; vision.md page 25
-/
module

public import ContinuousFOL.Completeness.DecidableTheory
public import ContinuousFOL.Completeness.ProvableMetricQRE
public import ContinuousFOL.Completeness.PavelkaCompleteness
public import ContinuousFOL.Completeness.ApproximatedStrongCompleteness
public import ContinuousFOL.Group2Axioms.SoundnessMetric
public import ContinuousFOL.SubstitutionAndCompletions.SubstitutionLemma
public import Mathlib.Computability.Partrec

@[expose] public section

noncomputable section
open Classical Encodable

namespace ContinuousFOL

/-! ### Computable unbounded search -/

/-- Unbounded search for the least `n` with `p a n = true` is computable when
    `p` is computable and the search is total. -/
lemma computable_nat_find {α} [Primcodable α] {p : α → ℕ → Bool}
    (hp : Computable₂ p) (htot : ∀ a, ∃ n, p a n = true) :
    Computable (fun a => Nat.find (htot a)) := by
  have hp' : Partrec₂ (fun a n => Part.some (p a n)) := hp.partrec.to₂
  have hpart : Partrec (fun a => Nat.rfind (fun n => Part.some (p a n))) :=
    Partrec.rfind hp'
  refine hpart.of_eq_tot fun a => ?_
  refine (Nat.mem_rfind (p := fun n => Part.some (p a n))).2 ?_
  constructor
  · have := Nat.find_spec (htot a)
    simpa
  · intro m hm
    have : ¬ p a m = true := Nat.find_min (htot a) hm
    cases h : p a m <;> simp_all

/-! ### Rounding a dyadic to precision `2⁻ⁿ` -/

/-- Integer nearest to `k / 2^N` at scale `2ⁿ` (ties rounded up). Requires `N ≥ 1`. -/
def approxNum (k N n : ℕ) : ℤ :=
  if N = 0 then k
  else ((k * 2 ^ n + 2 ^ (N - 1)) / 2 ^ N : ℕ)

lemma approxNum_close (k N n : ℕ) (hN : 1 ≤ N) :
    |(k : ℝ) / (2 : ℝ) ^ N - (approxNum k N n : ℝ) / (2 : ℝ) ^ n| ≤
      (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
  have hN0 : N ≠ 0 := Nat.pos_iff_ne_zero.mp hN
  set q := (k * 2 ^ n + 2 ^ (N - 1)) / 2 ^ N
  set r := (k * 2 ^ n + 2 ^ (N - 1)) % 2 ^ N
  have hdivmod : k * 2 ^ n + 2 ^ (N - 1) = 2 ^ N * q + r := by
    simpa [q, r] using (Nat.div_add_mod (k * 2 ^ n + 2 ^ (N - 1)) (2 ^ N)).symm
  have hr_lt : r < 2 ^ N := Nat.mod_lt _ (Nat.pow_pos (by norm_num : 0 < 2))
  have h2N : (0 : ℝ) < (2 : ℝ) ^ N := pow_pos (by norm_num) _
  have h2n : (0 : ℝ) < (2 : ℝ) ^ n := pow_pos (by norm_num) _
  have hy :
      (k * 2 ^ n + 2 ^ (N - 1) : ℝ) / (2 : ℝ) ^ N =
        (k : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ N + 1 / 2 := by
    have hpow : (2 : ℝ) ^ N = (2 : ℝ) ^ (N - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hN]
    have hhalf : (2 : ℝ) ^ (N - 1) / (2 : ℝ) ^ N = 1 / 2 := by
      rw [hpow, div_mul_eq_div_div, div_self (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))]
    have hcast : (k * 2 ^ n + 2 ^ (N - 1) : ℝ) = (k : ℝ) * (2 : ℝ) ^ n + (2 : ℝ) ^ (N - 1) := by
      norm_cast
    rw [hcast, add_div, hhalf]
  have hqR : (k * 2 ^ n + 2 ^ (N - 1) : ℝ) = (2 : ℝ) ^ N * q + r := by
    exact_mod_cast hdivmod
  have hrel :
      (k : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ N + 1 / 2 =
        (q : ℝ) + (r : ℝ) / (2 : ℝ) ^ N := by
    have hpos : (2 : ℝ) ^ N ≠ 0 := ne_of_gt h2N
    rw [← hy, hqR]
    field_simp [hpos]
  have hfrac : |(q : ℝ) - (k : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ N| ≤ 1 / 2 := by
    have : (q : ℝ) - (k : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ N =
        1 / 2 - (r : ℝ) / (2 : ℝ) ^ N := by linarith
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hr1 : (r : ℝ) / (2 : ℝ) ^ N < 1 := (div_lt_one h2N).2 (by exact_mod_cast hr_lt)
    have hr0' : 0 ≤ (r : ℝ) / (2 : ℝ) ^ N := div_nonneg hr0 h2N.le
    rw [this, abs_le]
    constructor <;> linarith
  have hqcast : (approxNum k N n : ℝ) = (q : ℝ) := by
    simp [approxNum, hN0, q]
    norm_cast
  have hscale :
      |(k : ℝ) / (2 : ℝ) ^ N - (q : ℝ) / (2 : ℝ) ^ n| =
        |(q : ℝ) - (k : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ N| / (2 : ℝ) ^ n := by
    have hNne : (2 : ℝ) ^ N ≠ 0 := ne_of_gt h2N
    have hnne : (2 : ℝ) ^ n ≠ 0 := ne_of_gt h2n
    have h1 : (k : ℝ) / (2 : ℝ) ^ N - (q : ℝ) / (2 : ℝ) ^ n =
        ((k : ℝ) * (2 : ℝ) ^ n - (q : ℝ) * (2 : ℝ) ^ N) /
          ((2 : ℝ) ^ N * (2 : ℝ) ^ n) := by
      field_simp [hNne, hnne]
    rw [h1, abs_div, abs_mul, abs_of_pos h2N, abs_of_pos h2n, abs_sub_comm,
      div_mul_eq_div_div]
    have h2 : |(q : ℝ) * (2 : ℝ) ^ N - (k : ℝ) * (2 : ℝ) ^ n| / (2 : ℝ) ^ N =
        |(q : ℝ) - (k : ℝ) * (2 : ℝ) ^ n / (2 : ℝ) ^ N| := by
      have habsN : |(2 : ℝ) ^ N| = (2 : ℝ) ^ N := abs_of_pos h2N
      rw [← habsN, ← abs_div, habsN, sub_div, mul_div_cancel_right₀ (q : ℝ) hNne]
    exact congrArg (fun x => x / (2 : ℝ) ^ n) h2
  have hhalf : (1 / 2 : ℝ) / (2 : ℝ) ^ n = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
    have h1 : (1 / 2 : ℝ) / (2 : ℝ) ^ n = ((2 : ℝ) ^ (n + 1))⁻¹ := by
      rw [div_div, one_div]
      congr 1
      exact (mul_comm (2 : ℝ) _).trans (pow_succ (2 : ℝ) n).symm
    have h2 : ((2 : ℝ) ^ (n + 1))⁻¹ = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
      rw [← zpow_natCast, ← zpow_neg]
    exact h1.trans h2
  rw [hqcast, hscale]
  exact (div_le_div_of_nonneg_right hfrac h2n.le).trans_eq hhalf

lemma exists_mem_lt_csInf_add {s : Set ℝ} (hne : s.Nonempty) (_hbdd : BddBelow s)
    {ε : ℝ} (hε : 0 < ε) : ∃ x ∈ s, x < sInf s + ε := by
  by_contra h
  push Not at h
  have : sInf s + ε ≤ sInf s := le_csInf hne fun x hx => h x hx
  linarith

/-! ### Evaluation depends only on free variables -/

lemma Term.eval_agree_on_vars {L : Signature} (M : PreStructure L)
    {t : Term L} {σ τ : Var → M.Carrier} (h : ∀ v ∈ t.vars, σ v = τ v) :
    t.eval M σ = t.eval M τ := by
  induction t with
  | var x =>
    exact h x (by simp [Term.vars])
  | func f args ih =>
    simp only [Term.eval]
    congr 1
    ext i
    refine ih i fun v hv => h v ?_
    simp only [Term.vars, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hv⟩

lemma Formula.eval_agree_on_freeVars {L : Signature} (M : PreStructure L)
    {φ : Formula L} {σ τ : Var → M.Carrier}
    (h : ∀ v ∈ φ.freeVars, σ v = τ v) :
    φ.eval M σ = φ.eval M τ := by
  induction φ generalizing σ τ with
  | rel P args =>
    simp only [Formula.eval]
    congr 1
    ext i
    refine Term.eval_agree_on_vars M fun v hv => h v ?_
    simp only [Formula.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, hv⟩
  | tsub α β ihα ihβ =>
    simp only [Formula.eval, ihα fun v hv => h v (Finset.mem_union_left _ hv),
      ihβ fun v hv => h v (Finset.mem_union_right _ hv)]
  | neg α ih =>
    simp only [Formula.eval, ih fun v hv => h v (by simpa [Formula.freeVars] using hv)]
  | half α ih =>
    simp only [Formula.eval, ih fun v hv => h v (by simpa [Formula.freeVars] using hv)]
  | sup x α ih =>
    simp only [Formula.eval]
    congr 1
    ext r
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨a, (ih fun v hv => ?_).symm⟩
      by_cases hvx : x = v
      · subst hvx; simp [updateAssign]
      · have hv' : v ∈ Formula.freeVars (.sup x α) := by
          simp [Formula.freeVars, Finset.mem_erase, Ne.symm hvx, hv]
        simp [updateAssign, hvx, h v hv']
    · rintro ⟨a, rfl⟩
      refine ⟨a, ih fun v hv => ?_⟩
      by_cases hvx : x = v
      · subst hvx; simp [updateAssign]
      · have hv' : v ∈ Formula.freeVars (.sup x α) := by
          simp [Formula.freeVars, Finset.mem_erase, Ne.symm hvx, hv]
        simp [updateAssign, hvx, h v hv']

lemma Formula.eval_sentence {L : Signature} (M : PreStructure L)
    {φ : Formula L} (hφ : IsSentence φ) (σ τ : Var → M.Carrier) :
    φ.eval M σ = φ.eval M τ :=
  Formula.eval_agree_on_freeVars M fun v hv => by
    have : φ.freeVars = ∅ := hφ
    rw [this] at hv
    exact (Finset.notMem_empty v hv).elim

lemma Formula.eval_sup_of_constant {L : Signature} (M : PreStructure L)
    (σ : Var → M.Carrier) (x : Var) (φ : Formula L)
    (h : ∀ a, φ.eval M (updateAssign σ x a) = φ.eval M σ) :
    (Formula.sup x φ).eval M σ = φ.eval M σ := by
  simp only [Formula.eval]
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨a, rfl⟩
    exact (h a).le
  · obtain ⟨a₀⟩ := M.nonempty
    have : φ.eval M σ ∈ Set.range fun a => φ.eval M (updateAssign σ x a) :=
      ⟨a₀, h a₀⟩
    exact le_csSup ⟨1, by rintro _ ⟨a, rfl⟩; exact (Formula.eval_in_Icc _ _ _).2⟩ this

lemma Formula.eval_foldr_sup_constant {L : Signature} (M : PreStructure L)
    {φ : Formula L} (h : ∀ σ τ, φ.eval M σ = φ.eval M τ)
    (xs : List Var) (σ : Var → M.Carrier) :
    (xs.foldr (fun x ψ => .sup x ψ) φ).eval M σ = φ.eval M σ := by
  induction xs generalizing σ with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldr_cons]
    have hconst : ∀ a, (xs.foldr (fun x ψ => .sup x ψ) φ).eval M (updateAssign σ x a) =
        (xs.foldr (fun x ψ => .sup x ψ) φ).eval M σ := by
      intro a
      rw [ih, h, ih]
    rw [Formula.eval_sup_of_constant M σ x _ hconst, ih]

lemma Formula.eval_supClosure_of_constant {L : Signature} (M : PreStructure L)
    {φ : Formula L} (h : ∀ σ τ, φ.eval M σ = φ.eval M τ)
    (σ : Var → M.Carrier) :
    φ.supClosure.eval M σ = φ.eval M σ :=
  Formula.eval_foldr_sup_constant M h _ _

lemma Formula.supClosure_isSentence {L : Signature} (φ : Formula L) :
    IsSentence φ.supClosure :=
  Formula.supClosure_freeVars φ

lemma computable_nat_pow : Computable₂ fun a b : ℕ => a ^ b :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).to_comp


/-! ### Packing six naturals into one -/

def pack6 (k N k' N' s t : ℕ) : ℕ :=
  Nat.pair (Nat.pair k N) (Nat.pair (Nat.pair k' N') (Nat.pair s t))

def unpack6 (w : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let kn := Nat.unpair (Nat.unpair w).1
  let rest := Nat.unpair (Nat.unpair w).2
  let kn' := Nat.unpair rest.1
  let st := Nat.unpair rest.2
  (kn.1, kn.2, kn'.1, kn'.2, st.1, st.2)

lemma unpack6_pack6 (k N k' N' s t : ℕ) :
    unpack6 (pack6 k N k' N' s t) = (k, N, k', N', s, t) := by
  simp [unpack6, pack6]

lemma computable_unpack6 : Computable unpack6 := by
  have hunp : Computable Nat.unpair := Computable.unpair
  have hfst : Computable fun w : ℕ => (Nat.unpair w).1 := Computable.fst.comp hunp
  have hsnd : Computable fun w : ℕ => (Nat.unpair w).2 := Computable.snd.comp hunp
  have hkn : Computable fun w : ℕ => Nat.unpair (Nat.unpair w).1 := hunp.comp hfst
  have hrest : Computable fun w : ℕ => Nat.unpair (Nat.unpair w).2 := hunp.comp hsnd
  have hkn' : Computable fun w : ℕ => Nat.unpair (Nat.unpair (Nat.unpair w).2).1 :=
    hunp.comp (Computable.fst.comp hrest)
  have hst : Computable fun w : ℕ => Nat.unpair (Nat.unpair (Nat.unpair w).2).2 :=
    hunp.comp (Computable.snd.comp hrest)
  refine (Computable.fst.comp hkn).pair ?_
  refine (Computable.snd.comp hkn).pair ?_
  refine (Computable.fst.comp hkn').pair ?_
  refine (Computable.snd.comp hkn').pair ?_
  exact (Computable.fst.comp hst).pair (Computable.snd.comp hst)

lemma computable_nat_mul : Computable₂ (fun a b : ℕ => a * b) :=
  Primrec.nat_mul.to_comp

lemma computable_nat_add : Computable₂ (fun a b : ℕ => a + b) :=
  Primrec.nat_add.to_comp

lemma computable_nat_div : Computable₂ (fun a b : ℕ => a / b) :=
  Primrec.nat_div.to_comp

lemma computable_nat_le : ComputablePred fun p : ℕ × ℕ => p.1 ≤ p.2 :=
  ⟨inferInstance, Primrec.nat_le.decide.to_comp⟩

lemma computable_nat_eq : ComputablePred fun p : ℕ × ℕ => p.1 = p.2 :=
  ⟨inferInstance, (Primrec.eq (α := ℕ)).decide.to_comp⟩

lemma encode_natCast_int (n : ℕ) : Encodable.encode (n : ℤ) = 2 * n := by
  change Equiv.intEquivNat (n : ℤ) = 2 * n
  have hsum : Equiv.intEquivNatSumNat (n : ℤ) = Sum.inl n := rfl
  simp [Equiv.intEquivNat, hsum, Equiv.natSumNatEquivNat_apply]

lemma computable_nat_cast_int : Computable fun n : ℕ => (n : ℤ) :=
  (Computable.ofNat ℤ).comp
    (computable_nat_mul.comp (Computable.const (2 : ℕ)) Computable.id) |>.of_eq fun n => by
    change Denumerable.ofNat ℤ (2 * n) = (n : ℤ)
    rw [show 2 * n = encode (n : ℤ) from (encode_natCast_int n).symm,
      Denumerable.ofNat_encode]

lemma computable_approxNum : Computable (fun p : ℕ × ℕ × ℕ => approxNum p.1 p.2.1 p.2.2) := by
  have hpow : Computable₂ fun a b : ℕ => a ^ b := computable_nat_pow
  have hk : Computable fun p : ℕ × ℕ × ℕ => p.1 := Computable.fst
  have hN : Computable fun p : ℕ × ℕ × ℕ => p.2.1 := Computable.fst.comp Computable.snd
  have hn : Computable fun p : ℕ × ℕ × ℕ => p.2.2 := Computable.snd.comp Computable.snd
  have hN0 : Computable fun p : ℕ × ℕ × ℕ => decide (p.2.1 = 0) :=
    ((Primrec.eq (α := ℕ)).comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)).decide.to_comp
  have helse : Computable fun p : ℕ × ℕ × ℕ =>
      (p.1 * 2 ^ p.2.2 + 2 ^ (p.2.1 - 1)) / 2 ^ p.2.1 := by
    have h2n : Computable fun p : ℕ × ℕ × ℕ => 2 ^ p.2.2 :=
      computable_nat_pow.comp (Computable.const 2) hn
    have h2N : Computable fun p : ℕ × ℕ × ℕ => 2 ^ p.2.1 :=
      computable_nat_pow.comp (Computable.const 2) hN
    have h2Nm : Computable fun p : ℕ × ℕ × ℕ => 2 ^ (p.2.1 - 1) :=
      computable_nat_pow.comp (Computable.const 2)
        ((Primrec.nat_sub.to_comp).comp hN (Computable.const 1))
    have hmul : Computable fun p : ℕ × ℕ × ℕ => p.1 * 2 ^ p.2.2 :=
      computable_nat_mul.comp hk h2n
    have hadd : Computable fun p : ℕ × ℕ × ℕ => p.1 * 2 ^ p.2.2 + 2 ^ (p.2.1 - 1) :=
      computable_nat_add.comp hmul h2Nm
    exact computable_nat_div.comp hadd h2N
  have hkZ : Computable fun p : ℕ × ℕ × ℕ => (p.1 : ℤ) :=
    computable_nat_cast_int.comp hk
  have helseZ : Computable fun p : ℕ × ℕ × ℕ =>
      (((p.1 * 2 ^ p.2.2 + 2 ^ (p.2.1 - 1)) / 2 ^ p.2.1 : ℕ) : ℤ) :=
    computable_nat_cast_int.comp helse
  refine (Computable.cond hN0 hkZ helseZ).of_eq ?_
  intro p
  simp [approxNum]


/-! ### Semantic facts about complete theories -/

lemma Formula.eval_tsub_dyadic {L : Signature} (M : PreStructure L)
    (σ : Var → M.Carrier) (φ : Formula L) (d : DyadicCode) :
    (Formula.tsub φ (Formula.dyadic L d)).eval M σ = φ.eval M σ ∸ d.val := by
  simp [Formula.eval, Formula.eval_dyadic]

lemma Formula.eval_dyadic_tsub {L : Signature} (M : PreStructure L)
    (σ : Var → M.Carrier) (φ : Formula L) (d : DyadicCode) :
    (Formula.tsub (Formula.dyadic L d) φ).eval M σ = d.val ∸ φ.eval M σ := by
  simp [Formula.eval, Formula.eval_dyadic]

lemma Formula.eval_supClosure_tsub_dyadic {L : Signature} (M : PreStructure L)
    {φ : Formula L} (hφ : IsSentence φ) (d : DyadicCode) (σ : Var → M.Carrier) :
    (Formula.tsub φ (Formula.dyadic L d)).supClosure.eval M σ =
      φ.eval M σ ∸ d.val := by
  rw [Formula.eval_supClosure_of_constant]
  · simp [Formula.eval, Formula.eval_dyadic]
  · intro σ τ
    simp [Formula.eval, Formula.eval_dyadic, Formula.eval_sentence M hφ σ τ]

lemma Formula.eval_supClosure_dyadic_tsub {L : Signature} (M : PreStructure L)
    {φ : Formula L} (hφ : IsSentence φ) (d : DyadicCode) (σ : Var → M.Carrier) :
    (Formula.tsub (Formula.dyadic L d) φ).supClosure.eval M σ =
      d.val ∸ φ.eval M σ := by
  rw [Formula.eval_supClosure_of_constant]
  · simp [Formula.eval, Formula.eval_dyadic]
  · intro σ τ
    simp [Formula.eval, Formula.eval_dyadic, Formula.eval_sentence M hφ σ τ]

lemma complete_theory_models_witness.{u} {LM : MetricSignature}
    {T : Set (Formula LM.toSignature)} (hcomp : IsCompleteTheory.{u} T) :
    ∃ (M : ContinuousStructure.{u} LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ T ∧
        T = {φ | IsSentence φ ∧ φ.eval M.toPreStructure σ = 0} := by
  obtain ⟨_, M, σ, hTeq⟩ := hcomp
  refine ⟨M, σ, ?_, hTeq⟩
  intro φ hφ
  have : φ ∈ {ψ | IsSentence ψ ∧ ψ.eval M.toPreStructure σ = 0} := by
    simpa [hTeq] using hφ
  exact this.2

lemma complete_theory_agree_on_sentences.{u} {LM : MetricSignature}
    {T : Set (Formula LM.toSignature)} (hcomp : IsCompleteTheory.{u} T)
    (M N : ContinuousStructure.{u} LM) (σ : Var → M.Carrier) (τ : Var → N.Carrier)
    (hM : ModelsPre M.toPreStructure σ T) (hN : ModelsPre N.toPreStructure τ T)
    {φ : Formula LM.toSignature} (hφ : IsSentence φ) :
    φ.eval M.toPreStructure σ = φ.eval N.toPreStructure τ := by
  obtain ⟨_, M0, σ0, hTeq⟩ := hcomp
  have hM0 : ModelsPre M0.toPreStructure σ0 T := by
    intro ψ hψ
    have : ψ ∈ {χ | IsSentence χ ∧ χ.eval M0.toPreStructure σ0 = 0} := by
      simpa [hTeq] using hψ
    exact this.2
  -- It is enough that every model agrees with the witnessing model `M0`.
  have agree (K : ContinuousStructure.{u} LM) (ρ : Var → K.Carrier)
      (hK : ModelsPre K.toPreStructure ρ T) :
      φ.eval K.toPreStructure ρ = φ.eval M0.toPreStructure σ0 := by
    set a := φ.eval M0.toPreStructure σ0
    set b := φ.eval K.toPreStructure ρ
    apply le_antisymm
    · by_contra hlt
      have hlt' : a < b := lt_of_not_ge hlt
      obtain ⟨d, had, hdb⟩ := DyadicCode.dense_in_Icc
        (Formula.eval_in_Icc M0.toPreStructure σ0 φ).1
        (Formula.eval_in_Icc K.toPreStructure ρ φ).2 hlt'
      set χ := (Formula.tsub φ (Formula.dyadic LM.toSignature d)).supClosure
      have hχT : χ ∈ T := by
        have : IsSentence χ ∧ χ.eval M0.toPreStructure σ0 = 0 := by
          refine ⟨Formula.supClosure_isSentence _, ?_⟩
          rw [Formula.eval_supClosure_tsub_dyadic M0.toPreStructure hφ d σ0]
          exact (tsubR.eq_zero_iff _ _).mpr had.le
        simpa [hTeq] using this
      have hχK : χ.eval K.toPreStructure ρ = 0 := hK χ hχT
      have : χ.eval K.toPreStructure ρ = b ∸ d.val :=
        Formula.eval_supClosure_tsub_dyadic K.toPreStructure hφ d ρ
      have hpos : 0 < b ∸ d.val := by
        have : 0 < b - d.val := sub_pos.mpr hdb
        simp [tsubR, le_of_lt this, this]
      exact (ne_of_gt hpos) (this ▸ hχK)
    · by_contra hlt
      have hlt' : b < a := lt_of_not_ge hlt
      obtain ⟨d, hbd, hda⟩ := DyadicCode.dense_in_Icc
        (Formula.eval_in_Icc K.toPreStructure ρ φ).1
        (Formula.eval_in_Icc M0.toPreStructure σ0 φ).2 hlt'
      set χ := (Formula.tsub (Formula.dyadic LM.toSignature d) φ).supClosure
      have hχT : χ ∈ T := by
        have : IsSentence χ ∧ χ.eval M0.toPreStructure σ0 = 0 := by
          refine ⟨Formula.supClosure_isSentence _, ?_⟩
          rw [Formula.eval_supClosure_dyadic_tsub M0.toPreStructure hφ d σ0]
          exact (tsubR.eq_zero_iff _ _).mpr hda.le
        simpa [hTeq] using this
      have hχK : χ.eval K.toPreStructure ρ = 0 := hK χ hχT
      have : χ.eval K.toPreStructure ρ = d.val ∸ b :=
        Formula.eval_supClosure_dyadic_tsub K.toPreStructure hφ d ρ
      have hpos : 0 < d.val ∸ b := by
        have : 0 < d.val - b := sub_pos.mpr hbd
        simp [tsubR, le_of_lt this, this]
      exact (ne_of_gt hpos) (this ▸ hχK)
  calc
    φ.eval M.toPreStructure σ = φ.eval M0.toPreStructure σ0 := agree M σ hM
    _ = φ.eval N.toPreStructure τ := (agree N τ hN).symm

lemma degreeOfTruthComplete_of_complete_theory.{u} {LM : MetricSignature}
    {T : Set (Formula LM.toSignature)} (hcomp : IsCompleteTheory.{u} T)
    {φ : Formula LM.toSignature} (hφ : IsSentence φ) :
    ∃ (M : ContinuousStructure.{u} LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ T ∧
        degreeOfTruthComplete.{u} T φ = φ.eval M.toPreStructure σ := by
  obtain ⟨M, σ, hM, _hTeq⟩ := complete_theory_models_witness.{u} hcomp
  refine ⟨M, σ, hM, ?_⟩
  unfold degreeOfTruthComplete
  have hset :
      {r : ℝ | ∃ (N : ContinuousStructure.{u} LM) (τ : Var → N.Carrier),
          ModelsPre N.toPreStructure τ T ∧ r = φ.eval N.toPreStructure τ} =
        {φ.eval M.toPreStructure σ} := by
    ext r
    constructor
    · rintro ⟨N, τ, hN, rfl⟩
      simpa using (complete_theory_agree_on_sentences.{u} hcomp N M τ σ hN hM hφ)
    · rintro rfl
      exact ⟨M, σ, hM, rfl⟩
  simp [hset]

lemma degreeOfTruthMetric_of_complete_theory.{u} {LM : MetricSignature}
    {T : Set (Formula LM.toSignature)} (hcomp : IsCompleteTheory.{u} T)
    {φ : Formula LM.toSignature} (hφ : IsSentence φ) :
    ∃ (M : ContinuousStructure.{u} LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ T ∧
        degreeOfTruthMetric.{u} T φ = φ.eval M.toPreStructure σ := by
  obtain ⟨M, σ, hM, hdeg⟩ := degreeOfTruthComplete_of_complete_theory.{u} hcomp hφ
  refine ⟨M, σ, hM, ?_⟩
  rwa [degreeOfTruthMetric_eq_complete]

lemma axiomatization_subset.{u} {LM : MetricSignature}
    {Ax T : Set (Formula LM.toSignature)} (hAx : IsAxiomatization.{u} Ax T) :
    Ax ⊆ T := by
  intro φ hφ
  have hsen : IsSentence φ := hAx.1 φ hφ
  exact (hAx.2 φ hsen).mpr fun M σ hM => hM φ hφ

lemma axiomatization_models.{u} {LM : MetricSignature}
    {Ax T : Set (Formula LM.toSignature)} (hT : IsTheory T)
    (hAx : IsAxiomatization.{u} Ax T)
    (M : ContinuousStructure.{u} LM) (σ : Var → M.Carrier) :
    ModelsPre M.toPreStructure σ T ↔ ModelsPre M.toPreStructure σ Ax := by
  constructor
  · intro hTm φ hφ
    exact hTm φ (axiomatization_subset.{u} hAx hφ)
  · intro hAxm φ hφ
    have hsen : IsSentence φ := hT φ hφ
    exact (hAx.2 φ hsen).mp hφ M σ hAxm

lemma degreeOfTruthComplete_axiomatization.{u} {LM : MetricSignature}
    {Ax T : Set (Formula LM.toSignature)} (hT : IsTheory T)
    (hAx : IsAxiomatization.{u} Ax T) (φ : Formula LM.toSignature) :
    degreeOfTruthComplete.{u} T φ = degreeOfTruthComplete.{u} Ax φ := by
  unfold degreeOfTruthComplete
  congr 1
  ext r
  constructor
  · rintro ⟨M, σ, hM, rfl⟩
    exact ⟨M, σ, (axiomatization_models.{u} hT hAx M σ).mp hM, rfl⟩
  · rintro ⟨M, σ, hM, rfl⟩
    exact ⟨M, σ, (axiomatization_models.{u} hT hAx M σ).mpr hM, rfl⟩

lemma degreeOfTruthMetric_axiomatization.{u} {LM : MetricSignature}
    {Ax T : Set (Formula LM.toSignature)} (hT : IsTheory T)
    (hAx : IsAxiomatization.{u} Ax T) (φ : Formula LM.toSignature) :
    degreeOfTruthMetric.{u} T φ = degreeOfTruthMetric.{u} Ax φ := by
  rw [degreeOfTruthMetric_eq_complete, degreeOfTruthMetric_eq_complete,
    degreeOfTruthComplete_axiomatization.{u} hT hAx]

lemma degreeOfTruthComplete_tsub_dyadic.{u} {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)}
    (M0 : ContinuousStructure.{u} LM) (σ0 : Var → M0.Carrier)
    (hM0 : ModelsPre M0.toPreStructure σ0 Γ)
    {φ : Formula LM.toSignature} (_hφ : IsSentence φ)
    (hagree : ∀ (N : ContinuousStructure.{u} LM) (τ : Var → N.Carrier),
      ModelsPre N.toPreStructure τ Γ →
        φ.eval N.toPreStructure τ = φ.eval M0.toPreStructure σ0)
    (d : DyadicCode) :
    degreeOfTruthComplete.{u} Γ (Formula.tsub (Formula.dyadic LM.toSignature d) φ) =
      d.val ∸ φ.eval M0.toPreStructure σ0 := by
  unfold degreeOfTruthComplete
  have hset :
      {r : ℝ | ∃ (N : ContinuousStructure.{u} LM) (τ : Var → N.Carrier),
          ModelsPre N.toPreStructure τ Γ ∧
            r = (Formula.tsub (Formula.dyadic LM.toSignature d) φ).eval
              N.toPreStructure τ} =
        {d.val ∸ φ.eval M0.toPreStructure σ0} := by
    ext r
    constructor
    · rintro ⟨N, τ, hN, rfl⟩
      simp [Formula.eval_dyadic_tsub, hagree N τ hN]
    · rintro rfl
      refine ⟨M0, σ0, hM0, ?_⟩
      simp [Formula.eval_dyadic_tsub]
  simp [hset]

lemma lift_mulPow2Neg (k N : ℕ) (hk : k ≤ 2 ^ N) :
    (2 * k ≤ 2 ^ (N + 1)) ∧
      (DyadicCode.mulPow2Neg (2 * k) (N + 1)).val = (DyadicCode.mulPow2Neg k N).val := by
  constructor
  · simpa [pow_succ, mul_comm, mul_left_comm] using Nat.mul_le_mul_left 2 hk
  · have h2 : 2 * k ≤ 2 ^ (N + 1) := by
      simpa [pow_succ, mul_comm, mul_left_comm] using Nat.mul_le_mul_left 2 hk
    rw [DyadicCode.val_mulPow2Neg_div _ _ h2, DyadicCode.val_mulPow2Neg_div _ _ hk, pow_succ,
      Nat.cast_mul, Nat.cast_ofNat]
    field_simp

lemma two_pow_neg_add (n : ℕ) :
    (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) =
      (2 : ℝ) ^ (-(n : ℤ)) := by
  have hn : -((n + 1 : ℕ) : ℤ) = -(n : ℤ) - 1 := by
    push_cast; ring
  rw [hn, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring



lemma degreeOfTruthComplete_formula_tsub_dyadic.{u} {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)}
    (M0 : ContinuousStructure.{u} LM) (σ0 : Var → M0.Carrier)
    (hM0 : ModelsPre M0.toPreStructure σ0 Γ)
    {φ : Formula LM.toSignature}
    (hagree : ∀ (N : ContinuousStructure.{u} LM) (τ : Var → N.Carrier),
      ModelsPre N.toPreStructure τ Γ →
        φ.eval N.toPreStructure τ = φ.eval M0.toPreStructure σ0)
    (d : DyadicCode) :
    degreeOfTruthComplete.{u} Γ (Formula.tsub φ (Formula.dyadic LM.toSignature d)) =
      φ.eval M0.toPreStructure σ0 ∸ d.val := by
  unfold degreeOfTruthComplete
  have hset :
      {r : ℝ | ∃ (N : ContinuousStructure.{u} LM) (τ : Var → N.Carrier),
          ModelsPre N.toPreStructure τ Γ ∧
            r = (Formula.tsub φ (Formula.dyadic LM.toSignature d)).eval
              N.toPreStructure τ} =
        {φ.eval M0.toPreStructure σ0 ∸ d.val} := by
    ext r
    constructor
    · rintro ⟨N, τ, hN, rfl⟩
      simp [Formula.eval_tsub_dyadic, hagree N τ hN]
    · rintro rfl
      refine ⟨M0, σ0, hM0, ?_⟩
      simp [Formula.eval_tsub_dyadic]
  simp [hset]

lemma provable_tsub_mulPow2Neg_of_entailsComplete.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature)
    (hent : EntailsComplete.{u} Γ φ) (n : ℕ) :
    ProvableMetricQ Γ
      (.tsub φ (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 n))) := by
  apply provable_tsub_of_inconsistent_adjoin_metric Γ φ (DyadicCode.mulPow2Neg 1 n)
  rw [completeness_metric_iff]
  rintro ⟨M, σ, hM⟩
  have hφ0 : φ.eval M.toPreStructure σ = 0 :=
    hent M σ (fun ψ hψ => hM ψ (Set.mem_union_left _ hψ))
  have hmem :
      Formula.tsub (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 n)) φ ∈
        Γ ∪ {Formula.tsub (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 n)) φ} :=
    Set.mem_union_right _ (Set.mem_singleton _)
  have hval := hM _ hmem
  have hk : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hpos : (0 : ℝ) < (1 : ℝ) / (2 : ℝ) ^ n :=
    div_pos (by norm_num) (pow_pos (by norm_num) n)
  have hval' :
      (DyadicCode.mulPow2Neg 1 n).val ∸ φ.eval M.toPreStructure σ = 0 := by
    simpa [Formula.eval, Formula.eval_dyadic] using hval
  rw [hφ0, DyadicCode.val_mulPow2Neg_div 1 n hk, tsubR] at hval'
  have hzero : (1 : ℝ) / (2 : ℝ) ^ n = 0 := by
    simp at hval'
  exact (ne_of_gt hpos) hzero

lemma exists_mulPow2Neg_near {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    {η : ℝ} (hη : 0 < η) :
    ∃ k N, 1 ≤ N ∧ k ≤ 2 ^ N ∧
      |(DyadicCode.mulPow2Neg k N).val - δ| < η := by
  set x := max (0 : ℝ) (δ - η)
  set y := min (1 : ℝ) (δ + η)
  have hx0 : 0 ≤ x := le_max_left _ _
  have hy1 : y ≤ 1 := min_le_left _ _
  have hxy : x < y := by
    refine lt_min_iff.mpr ⟨?_, ?_⟩
    · exact max_lt (by norm_num) (by linarith)
    · exact max_lt (by linarith) (by linarith)
  obtain ⟨d, hxd, hdy⟩ := DyadicCode.dense_in_Icc hx0 hy1 hxy
  obtain ⟨k0, N0, hk0, hval⟩ := DyadicCode.exists_val_eq_div d
  obtain ⟨hk, hval'⟩ := lift_mulPow2Neg k0 N0 hk0
  refine ⟨2 * k0, N0 + 1, Nat.succ_le_succ (Nat.zero_le _), hk, ?_⟩
  have hvald : (DyadicCode.mulPow2Neg (2 * k0) (N0 + 1)).val = d.val := by
    rw [hval', DyadicCode.val_mulPow2Neg_div _ _ hk0, hval]
  rw [hvald, abs_sub_lt_iff]
  have hxδ : δ - η ≤ x := le_max_right _ _
  have hyδ : y ≤ δ + η := min_le_right _ _
  constructor <;> linarith

lemma abs_le_of_tsub_le {x y ε : ℝ} (h1 : x ∸ y ≤ ε) (h2 : y ∸ x ≤ ε) :
    |x - y| ≤ ε := by
  rw [abs_sub_le_iff]
  constructor
  · exact (le_max_left (x - y) 0).trans (by simpa [tsubR] using h1)
  · exact (le_max_left (y - x) 0).trans (by simpa [tsubR] using h2)

lemma exists_two_sided_cut.{u} {LM : MetricSignature}
    {T Ax : Set (Formula LM.toSignature)}
    (hcomp : IsCompleteTheory.{u} T) (hAx : IsAxiomatization.{u} Ax T)
    {φ : Formula LM.toSignature} (hφ : IsSentence φ) (n : ℕ) :
    ∃ k N, 1 ≤ N ∧ k ≤ 2 ^ N ∧
      ProvableMetricQ Ax
        (.tsub
          (.tsub
            (.tsub φ (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg k N)))
            (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2))))
          (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2)))) ∧
      ProvableMetricQ Ax
        (.tsub
          (.tsub
            (.tsub (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg k N)) φ)
            (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2))))
          (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2)))) := by
  obtain ⟨M0, σ0, hM0T, _hdeg⟩ := degreeOfTruthMetric_of_complete_theory.{u} hcomp hφ
  have hM0Ax : ModelsPre M0.toPreStructure σ0 Ax :=
    (axiomatization_models.{u} hcomp.1 hAx M0 σ0).mp hM0T
  set δ := φ.eval M0.toPreStructure σ0
  have hδ0 := (φ.eval_in_Icc M0.toPreStructure σ0).1
  have hδ1 := (φ.eval_in_Icc M0.toPreStructure σ0).2
  have hη : 0 < (2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) := zpow_pos (by norm_num) _
  obtain ⟨k, N, hN, hk, hnear⟩ := exists_mulPow2Neg_near hδ0 hδ1 hη
  set d := DyadicCode.mulPow2Neg k N
  have hagree : ∀ (K : ContinuousStructure.{u} LM) (τ : Var → K.Carrier),
      ModelsPre K.toPreStructure τ Ax →
        φ.eval K.toPreStructure τ = δ := by
    intro K τ hKAx
    have hKT : ModelsPre K.toPreStructure τ T :=
      (axiomatization_models.{u} hcomp.1 hAx K τ).mpr hKAx
    exact complete_theory_agree_on_sentences.{u} hcomp K M0 τ σ0 hKT hM0T hφ
  have heval : (DyadicCode.mulPow2Neg 1 (n + 2)).val =
      (2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) := by
    have hk : 1 ≤ 2 ^ (n + 2) := Nat.one_le_two_pow
    rw [DyadicCode.val_mulPow2Neg_div _ _ hk, zpow_neg, zpow_natCast, Nat.cast_one, one_div]
  have hnear' : |δ - d.val| < (2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) := by
    simpa [d, abs_sub_comm] using hnear
  have hent1 : EntailsComplete.{u} Ax
      (.tsub
        (.tsub φ (Formula.dyadic LM.toSignature d))
        (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2)))) := by
    intro M σ hM
    simp only [Formula.eval, Formula.eval_dyadic, hagree M σ hM, heval]
    apply (tsubR.eq_zero_iff _ _).mpr
    have : δ ∸ d.val ≤ |δ - d.val| := by
      simpa [tsubR] using max_le (le_abs_self (δ - d.val)) (abs_nonneg _)
    exact this.trans hnear'.le
  have hent2 : EntailsComplete.{u} Ax
      (.tsub
        (.tsub (Formula.dyadic LM.toSignature d) φ)
        (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2)))) := by
    intro M σ hM
    simp only [Formula.eval, Formula.eval_dyadic, hagree M σ hM, heval]
    apply (tsubR.eq_zero_iff _ _).mpr
    have : d.val ∸ δ ≤ |δ - d.val| := by
      simpa [tsubR, abs_sub_comm] using
        max_le (le_abs_self (d.val - δ)) (abs_nonneg _)
    exact this.trans hnear'.le
  exact ⟨k, N, hN, hk,
    provable_tsub_mulPow2Neg_of_entailsComplete.{u} Ax _ hent1 (n + 2),
    provable_tsub_mulPow2Neg_of_entailsComplete.{u} Ax _ hent2 (n + 2)⟩

lemma eval_le_of_double_tsub {L : Signature} (M : PreStructure L)
    (σ : Var → M.Carrier) (ψ : Formula L) (e : DyadicCode)
    (h : (Formula.tsub (Formula.tsub ψ (Formula.dyadic L e))
      (Formula.dyadic L e)).eval M σ = 0) :
    ψ.eval M σ ≤ e.val + e.val := by
  have h0 : (ψ.eval M σ ∸ e.val) ∸ e.val = 0 := by
    simpa [Formula.eval, Formula.eval_dyadic] using h
  have h1 : ψ.eval M σ ∸ e.val ≤ e.val := (tsubR.eq_zero_iff _ _).mp h0
  have hb := (DyadicCode.val_mem_Icc e).1
  simp only [tsubR] at h1
  by_cases hle : ψ.eval M σ - e.val ≤ 0
  · linarith
  · have : ψ.eval M σ - e.val ≤ e.val := by
      simpa [max_eq_left (le_of_not_ge hle)] using h1
    linarith

lemma degreeOfTruthComplete_le_of_double_tsub.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (ψ : Formula LM.toSignature) (e : DyadicCode)
    (hpr : ProvableMetricQ Γ
      (.tsub (.tsub ψ (Formula.dyadic LM.toSignature e))
        (Formula.dyadic LM.toSignature e))) :
    degreeOfTruthComplete.{u} Γ ψ ≤ e.val + e.val := by
  unfold degreeOfTruthComplete
  by_cases hne :
      {r : ℝ | ∃ (M : ContinuousStructure.{u} LM) (σ : Var → M.Carrier),
          ModelsPre M.toPreStructure σ Γ ∧ r = ψ.eval M.toPreStructure σ}.Nonempty
  · apply csSup_le hne
    rintro _ ⟨M, σ, hM, rfl⟩
    exact eval_le_of_double_tsub M.toPreStructure σ ψ e
      (soundness_metric.{u} Γ _ hpr M σ hM)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    linarith [(DyadicCode.val_mem_Icc e).1]

def doubleTsubCode {LM : MetricSignature} (P : RecursivePresentation LM)
    (c n k N : ℕ) : ℕ :=
  let c' := P.supClosureCode c
  let dC := P.dyadicCode k N
  let eC := P.dyadicCode 1 (n + 2)
  P.tsubCode (P.tsubCode (P.tsubCode c' dC) eC) eC

def doubleTsubCode_rev {LM : MetricSignature} (P : RecursivePresentation LM)
    (c n k N : ℕ) : ℕ :=
  let c' := P.supClosureCode c
  let dC := P.dyadicCode k N
  let eC := P.dyadicCode 1 (n + 2)
  P.tsubCode (P.tsubCode (P.tsubCode dC c') eC) eC

lemma doubleTsubCode_spec {LM : MetricSignature} (P : RecursivePresentation LM)
    (φ : Formula LM.toSignature) (n k N : ℕ) :
    doubleTsubCode P (P.code φ) n k N =
      P.code
        (.tsub
          (.tsub
            (.tsub φ.supClosure
              (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg k N)))
            (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2))))
          (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2)))) := by
  simp [doubleTsubCode, P.supClosureCode_spec, P.tsubCode_spec, P.dyadicCode_spec]

lemma doubleTsubCode_rev_spec {LM : MetricSignature} (P : RecursivePresentation LM)
    (φ : Formula LM.toSignature) (n k N : ℕ) :
    doubleTsubCode_rev P (P.code φ) n k N =
      P.code
        (.tsub
          (.tsub
            (.tsub
              (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg k N))
              φ.supClosure)
            (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2))))
          (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2)))) := by
  simp [doubleTsubCode_rev, P.supClosureCode_spec, P.tsubCode_spec, P.dyadicCode_spec]

opaque computable_doubleTsubCode {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      doubleTsubCode P p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hc : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1 :=
    Computable.fst.comp Computable.fst
  have hn : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2 :=
    Computable.snd.comp Computable.fst
  have hk : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1 :=
    Computable.fst.comp Computable.snd
  have hN : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2 :=
    Computable.snd.comp Computable.snd
  have hc' := P.supClosureCode_computable.comp hc
  have hdC := P.dyadicCode_computable.comp hk hN
  have hn2 : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2 + 2 :=
    Primrec.nat_add.to_comp.comp hn (Computable.const 2)
  have heC := P.dyadicCode_computable.comp (Computable.const 1) hn2
  have h1 := P.tsubCode_computable.comp hc' hdC
  have h2 := P.tsubCode_computable.comp h1 heC
  exact (P.tsubCode_computable.comp h2 heC).of_eq fun _ => rfl

opaque computable_doubleTsubCode_rev {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
      doubleTsubCode_rev P p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hc : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1 :=
    Computable.fst.comp Computable.fst
  have hn : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2 :=
    Computable.snd.comp Computable.fst
  have hk : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1 :=
    Computable.fst.comp Computable.snd
  have hN : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2 :=
    Computable.snd.comp Computable.snd
  have hc' := P.supClosureCode_computable.comp hc
  have hdC := P.dyadicCode_computable.comp hk hN
  have hn2 : Computable fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2 + 2 :=
    Primrec.nat_add.to_comp.comp hn (Computable.const 2)
  have heC := P.dyadicCode_computable.comp (Computable.const 1) hn2
  have h1 := P.tsubCode_computable.comp hdC hc'
  have h2 := P.tsubCode_computable.comp h1 heC
  exact (P.tsubCode_computable.comp h2 heC).of_eq fun _ => rfl

lemma computable_bool_and : Computable₂ fun a b : Bool => a && b :=
  Primrec.and.to_comp


/-! ### Primitive-recursive projections of packed witnesses -/

lemma primrec_unpack6 : Primrec unpack6 := by
  have hunp : Primrec Nat.unpair := Primrec.unpair
  have hfst : Primrec fun w : ℕ => (Nat.unpair w).1 := Primrec.fst.comp hunp
  have hsnd : Primrec fun w : ℕ => (Nat.unpair w).2 := Primrec.snd.comp hunp
  have hkn : Primrec fun w : ℕ => Nat.unpair (Nat.unpair w).1 := hunp.comp hfst
  have hrest : Primrec fun w : ℕ => Nat.unpair (Nat.unpair w).2 := hunp.comp hsnd
  have hkn' : Primrec fun w : ℕ => Nat.unpair (Nat.unpair (Nat.unpair w).2).1 :=
    hunp.comp (Primrec.fst.comp hrest)
  have hst : Primrec fun w : ℕ => Nat.unpair (Nat.unpair (Nat.unpair w).2).2 :=
    hunp.comp (Primrec.snd.comp hrest)
  exact (Primrec.fst.comp hkn).pair
    ((Primrec.snd.comp hkn).pair
      ((Primrec.fst.comp hkn').pair
        ((Primrec.snd.comp hkn').pair
          ((Primrec.fst.comp hst).pair (Primrec.snd.comp hst)))))

lemma primrec_w_k : Primrec fun w : ℕ => (unpack6 w).1 :=
  Primrec.fst.comp primrec_unpack6

lemma primrec_w_N : Primrec fun w : ℕ => (unpack6 w).2.1 :=
  Primrec.fst.comp (Primrec.snd.comp primrec_unpack6)

lemma primrec_w_s : Primrec fun w : ℕ => (unpack6 w).2.2.1 :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp primrec_unpack6))

lemma primrec_w_t : Primrec fun w : ℕ => (unpack6 w).2.2.2.1 :=
  Primrec.fst.comp
    (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp primrec_unpack6)))

lemma primrec_leN : Primrec fun w : ℕ => decide (1 ≤ (unpack6 w).2.1) :=
  (Primrec.nat_le.comp (Primrec.const 1) primrec_w_N).decide

lemma primrec_pow2N : Primrec fun w : ℕ => 2 ^ (unpack6 w).2.1 :=
  (Primrec₂.unpaired'.1 Nat.Primrec.pow).comp (Primrec.const 2) primrec_w_N

lemma primrec_lek : Primrec fun w : ℕ => decide ((unpack6 w).1 ≤ 2 ^ (unpack6 w).2.1) :=
  (Primrec.nat_le.comp primrec_w_k primrec_pow2N).decide

lemma primrec_c_of_cn : Primrec fun cn : ℕ => (Nat.unpair cn).1 :=
  Primrec.fst.comp Primrec.unpair

lemma primrec_n_of_cn : Primrec fun cn : ℕ => (Nat.unpair cn).2 :=
  Primrec.snd.comp Primrec.unpair

/-- Pack `(c, n, k, N)` as a single natural, from a packed `(c, n)` and a witness `w`. -/
def packCKN (cn w : ℕ) : ℕ :=
  Nat.pair cn (Nat.pair (unpack6 w).1 (unpack6 w).2.1)

lemma primrec_nat_pair : Primrec fun p : ℕ × ℕ => Nat.pair p.1 p.2 :=
  (Primrec.encode (α := ℕ × ℕ)).of_eq fun p => by
    simpa [encode] using encode_prod_val p.1 p.2

lemma primrec_packCKN : Primrec fun p : ℕ × ℕ => packCKN p.1 p.2 :=
  primrec_nat_pair.comp
    (Primrec.fst.pair
      (primrec_nat_pair.comp
        ((primrec_w_k.comp Primrec.snd).pair (primrec_w_N.comp Primrec.snd))))

/-! ### `ℕ`-coded versions of the double-truncated codes -/

def doubleTsubCodeNat {LM : MetricSignature} (P : RecursivePresentation LM) (e : ℕ) : ℕ :=
  doubleTsubCode P
    (Nat.unpair (Nat.unpair e).1).1
    (Nat.unpair (Nat.unpair e).1).2
    (Nat.unpair (Nat.unpair e).2).1
    (Nat.unpair (Nat.unpair e).2).2

def doubleTsubCodeRevNat {LM : MetricSignature} (P : RecursivePresentation LM) (e : ℕ) : ℕ :=
  doubleTsubCode_rev P
    (Nat.unpair (Nat.unpair e).1).1
    (Nat.unpair (Nat.unpair e).1).2
    (Nat.unpair (Nat.unpair e).2).1
    (Nat.unpair (Nat.unpair e).2).2

opaque computable_c_of_e : Computable fun e : ℕ => (Nat.unpair (Nat.unpair e).1).1 :=
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp

opaque computable_n_of_e : Computable fun e : ℕ => (Nat.unpair (Nat.unpair e).1).2 :=
  (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))).to_comp

opaque computable_k_of_e : Computable fun e : ℕ => (Nat.unpair (Nat.unpair e).2).1 :=
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp

opaque computable_N_of_e : Computable fun e : ℕ => (Nat.unpair (Nat.unpair e).2).2 :=
  (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp

opaque computable_sup_of_e {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun e : ℕ => P.supClosureCode (Nat.unpair (Nat.unpair e).1).1) :=
  P.supClosureCode_computable.comp computable_c_of_e

opaque computable_dyadic_kN_of_e {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun e : ℕ =>
      P.dyadicCode (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2) :=
  P.dyadicCode_computable.comp computable_k_of_e computable_N_of_e

opaque computable_n2_of_e : Computable fun e : ℕ => (Nat.unpair (Nat.unpair e).1).2 + 2 :=
  (Primrec.nat_add.comp
    (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair)))
    (Primrec.const 2)).to_comp

opaque computable_dyadic_eps_of_e {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun e : ℕ => P.dyadicCode 1 ((Nat.unpair (Nat.unpair e).1).2 + 2)) :=
  P.dyadicCode_computable.comp (Computable.const 1) computable_n2_of_e

opaque computable_tsub_c'_d {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun e : ℕ =>
      P.tsubCode (P.supClosureCode (Nat.unpair (Nat.unpair e).1).1)
        (P.dyadicCode (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2)) :=
  P.tsubCode_computable.comp (computable_sup_of_e P) (computable_dyadic_kN_of_e P)

opaque computable_tsub_c'_d_eps {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun e : ℕ =>
      P.tsubCode
        (P.tsubCode (P.supClosureCode (Nat.unpair (Nat.unpair e).1).1)
          (P.dyadicCode (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2))
        (P.dyadicCode 1 ((Nat.unpair (Nat.unpair e).1).2 + 2))) :=
  P.tsubCode_computable.comp (computable_tsub_c'_d P) (computable_dyadic_eps_of_e P)

opaque computable_doubleTsubCodeNat {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (doubleTsubCodeNat P) :=
  (P.tsubCode_computable.comp (computable_tsub_c'_d_eps P) (computable_dyadic_eps_of_e P)).of_eq
    fun _ => rfl

opaque computable_tsub_d_c' {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun e : ℕ =>
      P.tsubCode
        (P.dyadicCode (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2)
        (P.supClosureCode (Nat.unpair (Nat.unpair e).1).1)) :=
  P.tsubCode_computable.comp (computable_dyadic_kN_of_e P) (computable_sup_of_e P)

opaque computable_tsub_d_c'_eps {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun e : ℕ =>
      P.tsubCode
        (P.tsubCode
          (P.dyadicCode (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2)
          (P.supClosureCode (Nat.unpair (Nat.unpair e).1).1))
        (P.dyadicCode 1 ((Nat.unpair (Nat.unpair e).1).2 + 2))) :=
  P.tsubCode_computable.comp (computable_tsub_d_c' P) (computable_dyadic_eps_of_e P)

opaque computable_doubleTsubCodeRevNat {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (doubleTsubCodeRevNat P) :=
  (P.tsubCode_computable.comp (computable_tsub_d_c'_eps P) (computable_dyadic_eps_of_e P)).of_eq
    fun _ => rfl


lemma doubleTsubCodeNat_packCKN {LM : MetricSignature} (P : RecursivePresentation LM)
    (cn w : ℕ) :
    doubleTsubCodeNat P (packCKN cn w) =
      doubleTsubCode P (Nat.unpair cn).1 (Nat.unpair cn).2
        (unpack6 w).1 (unpack6 w).2.1 := by
  simp [doubleTsubCodeNat, packCKN, Nat.unpair_pair]

lemma doubleTsubCodeRevNat_packCKN {LM : MetricSignature} (P : RecursivePresentation LM)
    (cn w : ℕ) :
    doubleTsubCodeRevNat P (packCKN cn w) =
      doubleTsubCode_rev P (Nat.unpair cn).1 (Nat.unpair cn).2
        (unpack6 w).1 (unpack6 w).2.1 := by
  simp [doubleTsubCodeRevNat, packCKN, Nat.unpair_pair]

/-! ### Search predicate, assembled on `ℕ` codes -/

/-- A packed witness `w` is good for a packed input `cn = Nat.pair c n` when
`k, N` are a legal dyadic and both truncated cuts are provable at stages `s, t`. -/
def goodCore {LM : MetricSignature} (P : RecursivePresentation LM)
    (qProv : ℕ → ℕ → Bool) (cn w : ℕ) : Bool :=
  (decide (1 ≤ (unpack6 w).2.1) &&
      decide ((unpack6 w).1 ≤ 2 ^ (unpack6 w).2.1)) &&
    (qProv (doubleTsubCodeNat P (packCKN cn w)) (unpack6 w).2.2.1 &&
      qProv (doubleTsubCodeRevNat P (packCKN cn w)) (unpack6 w).2.2.2.1)

/-- On formula codes, search for a good witness; on junk codes, accept `w = 0`. -/
def goodAll {LM : MetricSignature} (P : RecursivePresentation LM)
    (qProv : ℕ → ℕ → Bool) (cn w : ℕ) : Bool :=
  bif decide (∃ φ : Formula LM.toSignature, P.code φ = (Nat.unpair cn).1)
  then goodCore P qProv cn w
  else decide (w = 0)

opaque computable_packCKN : Computable (fun p : ℕ × ℕ => packCKN p.1 p.2) :=
  primrec_packCKN.to_comp

opaque computable_fwdCode {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun p : ℕ × ℕ => doubleTsubCodeNat P (packCKN p.1 p.2)) :=
  (computable_doubleTsubCodeNat P).comp computable_packCKN

opaque computable_revCode {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fun p : ℕ × ℕ => doubleTsubCodeRevNat P (packCKN p.1 p.2)) :=
  (computable_doubleTsubCodeRevNat P).comp computable_packCKN

opaque computable_s_at : Computable (fun p : ℕ × ℕ => (unpack6 p.2).2.2.1) :=
  (primrec_w_s.comp Primrec.snd).to_comp

opaque computable_t_at : Computable (fun p : ℕ × ℕ => (unpack6 p.2).2.2.2.1) :=
  (primrec_w_t.comp Primrec.snd).to_comp

opaque computable_leN_at : Computable (fun p : ℕ × ℕ => decide (1 ≤ (unpack6 p.2).2.1)) :=
  (primrec_leN.comp Primrec.snd).to_comp

opaque computable_lek_at :
    Computable (fun p : ℕ × ℕ => decide ((unpack6 p.2).1 ≤ 2 ^ (unpack6 p.2).2.1)) :=
  (primrec_lek.comp Primrec.snd).to_comp

opaque computable_unpair : Computable Nat.unpair :=
  Primrec.unpair.to_comp

opaque computable_qProv_unpaired {qProv : ℕ → ℕ → Bool} (hq : Computable₂ qProv) :
    Computable (fun e : ℕ => qProv (Nat.unpair e).1 (Nat.unpair e).2) :=
  hq.comp (Computable.fst.comp computable_unpair) (Computable.snd.comp computable_unpair)

opaque computable_nat_lt_bool : Computable₂ (fun a b : ℕ => decide (a < b)) :=
  Primrec.nat_lt.decide.to_comp

/-- Pair the values of two unary computable functions, staying on `ℕ`. -/
lemma computable_pair_of {f g : ℕ → ℕ} (hf : Computable f) (hg : Computable g) :
    Computable (fun n => Nat.pair (f n) (g n)) := by
  have hlt : Computable (fun n => decide (f n < g n)) :=
    computable_nat_lt_bool.comp hf hg
  have hbb : Computable (fun n => g n * g n) := computable_nat_mul.comp hg hg
  have hthen : Computable (fun n => g n * g n + f n) := computable_nat_add.comp hbb hf
  have haa : Computable (fun n => f n * f n) := computable_nat_mul.comp hf hf
  have haaa : Computable (fun n => f n * f n + f n) := computable_nat_add.comp haa hf
  have helse : Computable (fun n => f n * f n + f n + g n) := computable_nat_add.comp haaa hg
  exact (Computable.cond hlt hthen helse).of_eq fun n => by
    rw [Bool.cond_decide, Nat.pair]

def fwdCodeNat {LM : MetricSignature} (P : RecursivePresentation LM) (e : ℕ) : ℕ :=
  doubleTsubCodeNat P (packCKN (Nat.unpair e).1 (Nat.unpair e).2)

def revCodeNat {LM : MetricSignature} (P : RecursivePresentation LM) (e : ℕ) : ℕ :=
  doubleTsubCodeRevNat P (packCKN (Nat.unpair e).1 (Nat.unpair e).2)

def sAtNat (e : ℕ) : ℕ := (unpack6 (Nat.unpair e).2).2.2.1
def tAtNat (e : ℕ) : ℕ := (unpack6 (Nat.unpair e).2).2.2.2.1
def leNAtNat (e : ℕ) : Bool := decide (1 ≤ (unpack6 (Nat.unpair e).2).2.1)
def lekAtNat (e : ℕ) : Bool :=
  decide ((unpack6 (Nat.unpair e).2).1 ≤ 2 ^ (unpack6 (Nat.unpair e).2).2.1)

def pairFwdSNat {LM : MetricSignature} (P : RecursivePresentation LM) (e : ℕ) : ℕ :=
  Nat.pair (fwdCodeNat P e) (sAtNat e)

def pairRevTNat {LM : MetricSignature} (P : RecursivePresentation LM) (e : ℕ) : ℕ :=
  Nat.pair (revCodeNat P e) (tAtNat e)

def goodFwdNat {LM : MetricSignature} (P : RecursivePresentation LM)
    (qProv : ℕ → ℕ → Bool) (e : ℕ) : Bool :=
  qProv (fwdCodeNat P e) (sAtNat e)

def goodRevNat {LM : MetricSignature} (P : RecursivePresentation LM)
    (qProv : ℕ → ℕ → Bool) (e : ℕ) : Bool :=
  qProv (revCodeNat P e) (tAtNat e)

def isCodeCnNat {LM : MetricSignature} (P : RecursivePresentation LM) (e : ℕ) : Bool :=
  decide (∃ φ : Formula LM.toSignature, P.code φ = (Nat.unpair (Nat.unpair e).1).1)

def wEqZeroNat (e : ℕ) : Bool := decide ((Nat.unpair e).2 = 0)

def goodCoreNat {LM : MetricSignature} (P : RecursivePresentation LM)
    (qProv : ℕ → ℕ → Bool) (e : ℕ) : Bool :=
  goodCore P qProv (Nat.unpair e).1 (Nat.unpair e).2

def goodAllNat {LM : MetricSignature} (P : RecursivePresentation LM)
    (qProv : ℕ → ℕ → Bool) (e : ℕ) : Bool :=
  goodAll P qProv (Nat.unpair e).1 (Nat.unpair e).2

opaque computable_fwdCode_nat {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (fwdCodeNat P) :=
  (computable_doubleTsubCodeNat P).comp (primrec_packCKN.comp Primrec.unpair).to_comp

opaque computable_revCode_nat {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (revCodeNat P) :=
  (computable_doubleTsubCodeRevNat P).comp (primrec_packCKN.comp Primrec.unpair).to_comp

opaque computable_s_at_nat : Computable sAtNat :=
  (primrec_w_s.comp (Primrec.snd.comp Primrec.unpair)).to_comp

opaque computable_t_at_nat : Computable tAtNat :=
  (primrec_w_t.comp (Primrec.snd.comp Primrec.unpair)).to_comp

opaque computable_leN_at_nat : Computable leNAtNat :=
  (primrec_leN.comp (Primrec.snd.comp Primrec.unpair)).to_comp

opaque computable_lek_at_nat : Computable lekAtNat :=
  (primrec_lek.comp (Primrec.snd.comp Primrec.unpair)).to_comp

opaque computable_pair_fwd_s_nat {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (pairFwdSNat P) :=
  computable_pair_of (computable_fwdCode_nat P) computable_s_at_nat

opaque computable_pair_rev_t_nat {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (pairRevTNat P) :=
  computable_pair_of (computable_revCode_nat P) computable_t_at_nat

opaque computable_goodFwd_nat {LM : MetricSignature} (P : RecursivePresentation LM)
    {qProv : ℕ → ℕ → Bool} (hq : Computable₂ qProv) :
    Computable (goodFwdNat P qProv) :=
  ((computable_qProv_unpaired hq).comp (computable_pair_fwd_s_nat P)).of_eq fun e => by
    simp [pairFwdSNat, goodFwdNat, Nat.unpair_pair]

opaque computable_goodRev_nat {LM : MetricSignature} (P : RecursivePresentation LM)
    {qProv : ℕ → ℕ → Bool} (hq : Computable₂ qProv) :
    Computable (goodRevNat P qProv) :=
  ((computable_qProv_unpaired hq).comp (computable_pair_rev_t_nat P)).of_eq fun e => by
    simp [pairRevTNat, goodRevNat, Nat.unpair_pair]

opaque computable_and_nat {f g : ℕ → Bool} (hf : Computable f) (hg : Computable g) :
    Computable (fun n : ℕ => f n && g n) :=
  computable_bool_and.comp hf hg

opaque computable_goodCore_nat {LM : MetricSignature} (P : RecursivePresentation LM)
    {qProv : ℕ → ℕ → Bool} (hq : Computable₂ qProv) :
    Computable (goodCoreNat P qProv) :=
  (computable_and_nat
      (computable_and_nat computable_leN_at_nat computable_lek_at_nat)
      (computable_and_nat (computable_goodFwd_nat P hq) (computable_goodRev_nat P hq))).of_eq
    fun e => by
      simp [goodCoreNat, goodCore, leNAtNat, lekAtNat, goodFwdNat, goodRevNat,
        fwdCodeNat, revCodeNat, sAtNat, tAtNat]

opaque computable_isCode_cn_nat {LM : MetricSignature} (P : RecursivePresentation LM) :
    Computable (isCodeCnNat P) :=
  (computablePred_iff_computable_decide.mp P.isCode_computable).comp
    (primrec_c_of_cn.comp (Primrec.fst.comp Primrec.unpair)).to_comp

opaque computable_w_eq_zero_nat : Computable wEqZeroNat :=
  ((Primrec.eq (α := ℕ)).comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0)).decide.to_comp

opaque computable_goodAll_nat {LM : MetricSignature} (P : RecursivePresentation LM)
    {qProv : ℕ → ℕ → Bool} (hq : Computable₂ qProv) :
    Computable (goodAllNat P qProv) :=
  (Computable.cond (computable_isCode_cn_nat P) (computable_goodCore_nat P hq)
      computable_w_eq_zero_nat).of_eq
    fun e => by
      simp [goodAllNat, goodAll, isCodeCnNat, goodCoreNat, wEqZeroNat]


lemma goodAllNat_pair {LM : MetricSignature} (P : RecursivePresentation LM)
    (qProv : ℕ → ℕ → Bool) (cn w : ℕ) :
    goodAllNat P qProv (Nat.pair cn w) = goodAll P qProv cn w := by
  simp [goodAllNat, Nat.unpair_pair]

opaque computable_goodAll {LM : MetricSignature} (P : RecursivePresentation LM)
    {qProv : ℕ → ℕ → Bool} (hq : Computable₂ qProv) :
    Computable₂ (goodAll P qProv) :=
  ((computable_goodAll_nat P hq).comp primrec_nat_pair.to_comp).of_eq fun p =>
    goodAllNat_pair P qProv p.1 p.2

def kOfWitness (w : ℕ) : ℕ := (unpack6 w).1
def NOfWitness (w : ℕ) : ℕ := (unpack6 w).2.1

lemma primrec_kOfWitness : Primrec kOfWitness := primrec_w_k
lemma primrec_NOfWitness : Primrec NOfWitness := primrec_w_N

/-- `approxNum k N n` from a packed triple `Nat.pair k (Nat.pair N n)`. -/
def approxNumPacked (e : ℕ) : ℤ :=
  approxNum (Nat.unpair e).1 (Nat.unpair (Nat.unpair e).2).1 (Nat.unpair (Nat.unpair e).2).2

opaque computable_k_of_e2 : Computable fun e : ℕ => (Nat.unpair e).1 :=
  (Primrec.fst.comp Primrec.unpair).to_comp

opaque computable_N_of_e2 : Computable fun e : ℕ => (Nat.unpair (Nat.unpair e).2).1 :=
  (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp

opaque computable_n_of_e2 : Computable fun e : ℕ => (Nat.unpair (Nat.unpair e).2).2 :=
  (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))).to_comp

opaque computable_N_eq_zero_e2 : Computable fun e : ℕ => decide ((Nat.unpair (Nat.unpair e).2).1 = 0) :=
  ((Primrec.eq (α := ℕ)).comp
    (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair)))
    (Primrec.const 0)).decide.to_comp

opaque computable_pow2n_e2 : Computable fun e : ℕ => (2 : ℕ) ^ (Nat.unpair (Nat.unpair e).2).2 :=
  computable_nat_pow.comp (Computable.const 2) computable_n_of_e2

opaque computable_pow2N_e2 : Computable fun e : ℕ => (2 : ℕ) ^ (Nat.unpair (Nat.unpair e).2).1 :=
  computable_nat_pow.comp (Computable.const 2) computable_N_of_e2

opaque computable_Nsub1_e2 : Computable fun e : ℕ => (Nat.unpair (Nat.unpair e).2).1 - 1 :=
  Primrec.nat_sub.to_comp.comp computable_N_of_e2 (Computable.const 1)

opaque computable_pow2Nsub1_e2 : Computable fun e : ℕ => (2 : ℕ) ^ ((Nat.unpair (Nat.unpair e).2).1 - 1) :=
  computable_nat_pow.comp (Computable.const 2) computable_Nsub1_e2

opaque computable_kmul_e2 : Computable fun e : ℕ =>
    (Nat.unpair e).1 * 2 ^ (Nat.unpair (Nat.unpair e).2).2 :=
  computable_nat_mul.comp computable_k_of_e2 computable_pow2n_e2

opaque computable_num_e2 : Computable fun e : ℕ =>
    (Nat.unpair e).1 * 2 ^ (Nat.unpair (Nat.unpair e).2).2 +
      2 ^ ((Nat.unpair (Nat.unpair e).2).1 - 1) :=
  computable_nat_add.comp computable_kmul_e2 computable_pow2Nsub1_e2

opaque computable_div_e2 : Computable fun e : ℕ =>
    ((Nat.unpair e).1 * 2 ^ (Nat.unpair (Nat.unpair e).2).2 +
      2 ^ ((Nat.unpair (Nat.unpair e).2).1 - 1)) /
      2 ^ (Nat.unpair (Nat.unpair e).2).1 :=
  computable_nat_div.comp computable_num_e2 computable_pow2N_e2

opaque computable_divZ_e2 : Computable fun e : ℕ =>
    (((Nat.unpair e).1 * 2 ^ (Nat.unpair (Nat.unpair e).2).2 +
      2 ^ ((Nat.unpair (Nat.unpair e).2).1 - 1)) /
      2 ^ (Nat.unpair (Nat.unpair e).2).1 : ℕ) :=
  computable_div_e2

opaque computable_kZ_e2 : Computable fun e : ℕ => ((Nat.unpair e).1 : ℤ) :=
  computable_nat_cast_int.comp computable_k_of_e2

opaque computable_divZ'_e2 : Computable fun e : ℕ =>
    ((((Nat.unpair e).1 * 2 ^ (Nat.unpair (Nat.unpair e).2).2 +
      2 ^ ((Nat.unpair (Nat.unpair e).2).1 - 1)) /
      2 ^ (Nat.unpair (Nat.unpair e).2).1 : ℕ) : ℤ) :=
  computable_nat_cast_int.comp computable_div_e2

opaque computable_approxNumPacked : Computable approxNumPacked :=
  (Computable.cond computable_N_eq_zero_e2 computable_kZ_e2 computable_divZ'_e2).of_eq
    fun e => by
      simp [approxNumPacked, approxNum]


def packFindArgs (cn w : ℕ) : ℕ :=
  Nat.pair (unpack6 w).1 (Nat.pair (unpack6 w).2.1 (Nat.unpair cn).2)

def packFindArgsNat (e : ℕ) : ℕ :=
  packFindArgs (Nat.unpair e).1 (Nat.unpair e).2

lemma primrec_packFindArgsNat : Primrec packFindArgsNat := by
  have hk : Primrec fun e : ℕ => (unpack6 (Nat.unpair e).2).1 :=
    primrec_w_k.comp (Primrec.snd.comp Primrec.unpair)
  have hN : Primrec fun e : ℕ => (unpack6 (Nat.unpair e).2).2.1 :=
    primrec_w_N.comp (Primrec.snd.comp Primrec.unpair)
  have hn : Primrec fun e : ℕ => (Nat.unpair (Nat.unpair e).1).2 :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.unpair))
  have hNn : Primrec fun e : ℕ =>
      Nat.pair (unpack6 (Nat.unpair e).2).2.1 (Nat.unpair (Nat.unpair e).1).2 :=
    primrec_nat_pair.comp (hN.pair hn)
  exact (primrec_nat_pair.comp (hk.pair hNn)).of_eq fun e => rfl

def approxFromFind (cn w : ℕ) : ℤ :=
  approxNum (unpack6 w).1 (unpack6 w).2.1 (Nat.unpair cn).2

def approxFromFindNat (e : ℕ) : ℤ :=
  approxFromFind (Nat.unpair e).1 (Nat.unpair e).2

lemma approxFromFind_packed (cn w : ℕ) :
    approxFromFind cn w = approxNumPacked (packFindArgs cn w) := by
  simp [approxFromFind, packFindArgs, approxNumPacked, Nat.unpair_pair]

opaque computable_approxFromFindNat : Computable approxFromFindNat :=
  (computable_approxNumPacked.comp primrec_packFindArgsNat.to_comp).of_eq fun e => by
    simp [approxFromFindNat, packFindArgsNat, approxFromFind_packed]

lemma goodAll_total.{u} {LM : MetricSignature} (P : RecursivePresentation LM)
    {T Ax : Set (Formula LM.toSignature)}
    (hcomp : IsCompleteTheory.{u} T) (hAx : IsAxiomatization.{u} Ax T)
    (qProv : ℕ → ℕ → Bool)
    (hqProv_iff : ∀ c : ℕ,
      (∃ ψ, ProvableMetricQ Ax ψ ∧ P.code ψ = c) ↔ ∃ s, qProv c s = true) :
    ∀ cn : ℕ, ∃ w, goodAll P qProv cn w = true := by
  intro cn
  by_cases hc : ∃ φ : Formula LM.toSignature, P.code φ = (Nat.unpair cn).1
  · obtain ⟨φ, hφc⟩ := hc
    have hsen : IsSentence φ.supClosure := Formula.supClosure_isSentence φ
    obtain ⟨k, N, hN, hk, hpr1, hpr2⟩ :=
      exists_two_sided_cut.{u} hcomp hAx hsen (Nat.unpair cn).2
    have hcode1 :
        doubleTsubCode P (Nat.unpair cn).1 (Nat.unpair cn).2 k N =
          P.code
            (.tsub
              (.tsub
                (.tsub φ.supClosure
                  (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg k N)))
                (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 ((Nat.unpair cn).2 + 2))))
              (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 ((Nat.unpair cn).2 + 2)))) := by
      simpa [hφc] using doubleTsubCode_spec P φ (Nat.unpair cn).2 k N
    have hcode2 :
        doubleTsubCode_rev P (Nat.unpair cn).1 (Nat.unpair cn).2 k N =
          P.code
            (.tsub
              (.tsub
                (.tsub
                  (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg k N))
                  φ.supClosure)
                (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 ((Nat.unpair cn).2 + 2))))
              (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 ((Nat.unpair cn).2 + 2)))) := by
      simpa [hφc] using doubleTsubCode_rev_spec P φ (Nat.unpair cn).2 k N
    have hex1 : ∃ ψ, ProvableMetricQ Ax ψ ∧
        P.code ψ = doubleTsubCode P (Nat.unpair cn).1 (Nat.unpair cn).2 k N :=
      ⟨_, hpr1, hcode1.symm⟩
    have hex2 : ∃ ψ, ProvableMetricQ Ax ψ ∧
        P.code ψ = doubleTsubCode_rev P (Nat.unpair cn).1 (Nat.unpair cn).2 k N :=
      ⟨_, hpr2, hcode2.symm⟩
    obtain ⟨s, hs⟩ := (hqProv_iff _).mp hex1
    obtain ⟨t, ht⟩ := (hqProv_iff _).mp hex2
    refine ⟨pack6 k N s t 0 0, ?_⟩
    have hc' : decide (∃ ψ : Formula LM.toSignature,
        P.code ψ = (Nat.unpair cn).1) = true :=
      decide_eq_true ⟨φ, hφc⟩
    rw [goodAll, hc', Bool.cond_true, goodCore,
      doubleTsubCodeNat_packCKN, doubleTsubCodeRevNat_packCKN]
    simp [unpack6_pack6, hN, hk, hs, ht]
  · refine ⟨0, ?_⟩
    have hc' : decide (∃ ψ : Formula LM.toSignature,
        P.code ψ = (Nat.unpair cn).1) = false :=
      decide_eq_false hc
    simp [goodAll, hc']

/-- Corollary 9.11: Every complete theory with a recursive or recursively enumerable
axiomatization is decidable. -/
theorem complete_re_theory_decidable.{u} {LM : MetricSignature}
    (P : RecursivePresentation LM) (T : Set (Formula LM.toSignature))
    (hcomp : IsCompleteTheory.{u} T)
    (hax : ∃ Ax : Set (Formula LM.toSignature), IsAxiomatization.{u} Ax T ∧
      (ComputablePred (fun n : ℕ => ∃ φ ∈ Ax, P.code φ = n) ∨
        REPred (fun n : ℕ => ∃ φ ∈ Ax, P.code φ = n))) :
    IsDecidableTheory.{u} P T := by
  refine ⟨?deg, fun hnot => (hnot hcomp).elim⟩
  intro _
  obtain ⟨Ax, hAx, hAxRE⟩ := hax
  have hAx_re : REPred (fun n => ∃ φ ∈ Ax, P.code φ = n) :=
    hAxRE.elim ComputablePred.to_re' id
  have hprov_re := provableMetricQ_codes_re P Ax hAx_re
  obtain ⟨qProv, hqProv, hqProv_iff⟩ := REPred.exists_computable hprov_re
  have htot : ∀ cn : ℕ, ∃ w, goodAll P qProv cn w = true :=
    goodAll_total.{u} P hcomp hAx qProv hqProv_iff
  have hfind : Computable (fun cn : ℕ => Nat.find (htot cn)) :=
    computable_nat_find (computable_goodAll P hqProv) htot
  have hpair : Computable (fun cn : ℕ => Nat.pair cn (Nat.find (htot cn))) :=
    computable_pair_of Computable.id hfind
  have happ : Computable (fun cn : ℕ => approxFromFind cn (Nat.find (htot cn))) :=
    (computable_approxFromFindNat.comp hpair).of_eq fun cn => by
      simp [approxFromFindNat, Nat.unpair_pair]
  have his : Computable (fun cn : ℕ =>
      decide (∃ ψ : Formula LM.toSignature, P.code ψ = (Nat.unpair cn).1)) :=
    (computablePred_iff_computable_decide.mp P.isCode_computable).comp
      primrec_c_of_cn.to_comp
  let f : ℕ → ℕ → ℤ := fun c n =>
    bif decide (∃ ψ : Formula LM.toSignature, P.code ψ = c) then
      approxFromFind (Nat.pair c n) (Nat.find (htot (Nat.pair c n)))
    else
      0
  have hf₁ : Computable (fun cn : ℕ => f (Nat.unpair cn).1 (Nat.unpair cn).2) :=
    (Computable.cond his happ (Computable.const (0 : ℤ))).of_eq fun cn => by
      simp [f, Nat.pair_unpair]
  have hf : Computable₂ f :=
    (hf₁.comp primrec_nat_pair.to_comp).of_eq fun p => by
      simp [Nat.unpair_pair]
  refine ⟨f, hf, ?corr⟩
  intro φ hsen n
  have hc' : decide (∃ ψ : Formula LM.toSignature, P.code ψ = P.code φ) = true :=
    decide_eq_true ⟨φ, rfl⟩
  have hfval : f (P.code φ) n =
      approxFromFind (Nat.pair (P.code φ) n)
        (Nat.find (htot (Nat.pair (P.code φ) n))) := by
    simp [f]
  rw [hfval]
  set cn := Nat.pair (P.code φ) n
  set w := Nat.find (htot cn)
  set k := (unpack6 w).1
  set N := (unpack6 w).2.1
  have hcn : Nat.unpair cn = (P.code φ, n) := Nat.unpair_pair _ _
  have hw : goodAll P qProv cn w = true := Nat.find_spec (htot cn)
  have hcore : goodCore P qProv cn w = true := by
    have : decide (∃ ψ : Formula LM.toSignature,
        P.code ψ = (Nat.unpair cn).1) = true := by
      simp [cn, hcn]
    simpa [goodAll, this] using hw
  have hbits :
      (decide (1 ≤ N) && decide (k ≤ 2 ^ N)) &&
        (qProv (doubleTsubCodeNat P (packCKN cn w)) (unpack6 w).2.2.1 &&
          qProv (doubleTsubCodeRevNat P (packCKN cn w)) (unpack6 w).2.2.2.1) = true := by
    simpa [goodCore, k, N] using hcore
  have hleg_prb := Bool.and_eq_true_iff.mp hbits
  have hN : 1 ≤ N := of_decide_eq_true (Bool.and_eq_true_iff.mp hleg_prb.1).1
  have hk : k ≤ 2 ^ N := of_decide_eq_true (Bool.and_eq_true_iff.mp hleg_prb.1).2
  have hsT : qProv (doubleTsubCodeNat P (packCKN cn w)) (unpack6 w).2.2.1 = true :=
    (Bool.and_eq_true_iff.mp hleg_prb.2).1
  have htT : qProv (doubleTsubCodeRevNat P (packCKN cn w)) (unpack6 w).2.2.2.1 = true :=
    (Bool.and_eq_true_iff.mp hleg_prb.2).2
  rw [doubleTsubCodeNat_packCKN, hcn] at hsT
  rw [doubleTsubCodeRevNat_packCKN, hcn] at htT
  have hex1 := (hqProv_iff (doubleTsubCode P (P.code φ) n k N)).mpr ⟨_, hsT⟩
  have hex2 := (hqProv_iff (doubleTsubCode_rev P (P.code φ) n k N)).mpr ⟨_, htT⟩
  have hφsup : φ.supClosure = φ := Formula.supClosure_of_freeVars_empty hsen
  have hpr1 : ProvableMetricQ Ax
      (.tsub
        (.tsub
          (.tsub φ (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg k N)))
          (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2))))
        (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2)))) := by
    obtain ⟨ψ, hpr, hψc⟩ := hex1
    have hspec := doubleTsubCode_spec P φ n k N
    rw [hφsup] at hspec
    exact (P.code_injective (hψc.trans hspec)).symm ▸ hpr
  have hpr2 : ProvableMetricQ Ax
      (.tsub
        (.tsub
          (.tsub (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg k N)) φ)
          (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2))))
        (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg 1 (n + 2)))) := by
    obtain ⟨ψ, hpr, hψc⟩ := hex2
    have hspec := doubleTsubCode_rev_spec P φ n k N
    rw [hφsup] at hspec
    exact (P.code_injective (hψc.trans hspec)).symm ▸ hpr
  obtain ⟨M0, σ0, hM0T, hdeg⟩ :=
    degreeOfTruthMetric_of_complete_theory.{u} hcomp hsen
  set δ := φ.eval M0.toPreStructure σ0
  set d := DyadicCode.mulPow2Neg k N
  set e := DyadicCode.mulPow2Neg 1 (n + 2)
  have hTthy : IsTheory T := hcomp.1
  have hle1 : degreeOfTruthComplete.{u} Ax
      (.tsub φ (Formula.dyadic LM.toSignature d)) ≤ e.val + e.val :=
    degreeOfTruthComplete_le_of_double_tsub.{u} Ax _ e hpr1
  have hle2 : degreeOfTruthComplete.{u} Ax
      (.tsub (Formula.dyadic LM.toSignature d) φ) ≤ e.val + e.val :=
    degreeOfTruthComplete_le_of_double_tsub.{u} Ax _ e hpr2
  have hM0Ax : ModelsPre M0.toPreStructure σ0 Ax :=
    (axiomatization_models.{u} hTthy hAx M0 σ0).mp hM0T
  have hagree : ∀ (K : ContinuousStructure.{u} LM) (τ : Var → K.Carrier),
      ModelsPre K.toPreStructure τ Ax →
        φ.eval K.toPreStructure τ = δ := by
    intro K τ hKAx
    have hKT : ModelsPre K.toPreStructure τ T :=
      (axiomatization_models.{u} hTthy hAx K τ).mpr hKAx
    exact complete_theory_agree_on_sentences.{u} hcomp K M0 τ σ0 hKT hM0T hsen
  have hval1 : degreeOfTruthComplete.{u} Ax
      (.tsub φ (Formula.dyadic LM.toSignature d)) = δ ∸ d.val :=
    degreeOfTruthComplete_formula_tsub_dyadic.{u} M0 σ0 hM0Ax hagree d
  have hval2 : degreeOfTruthComplete.{u} Ax
      (.tsub (Formula.dyadic LM.toSignature d) φ) = d.val ∸ δ :=
    degreeOfTruthComplete_tsub_dyadic.{u} M0 σ0 hM0Ax hsen hagree d
  have hε : e.val + e.val = (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
    have hk' : 1 ≤ 2 ^ (n + 2) := Nat.one_le_two_pow
    have hv : e.val = (2 : ℝ) ^ (-((n + 2 : ℕ) : ℤ)) := by
      rw [DyadicCode.val_mulPow2Neg_div _ _ hk', zpow_neg, zpow_natCast, Nat.cast_one,
        one_div]
    rw [hv]
    exact two_pow_neg_add (n + 1)
  have hδd : |d.val - δ| ≤ (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
    apply abs_le_of_tsub_le
    · exact (hval2 ▸ hle2).trans_eq hε
    · exact (hval1 ▸ hle1).trans_eq hε
  have hround := approxNum_close k N n hN
  have hvald : d.val = (k : ℝ) / (2 : ℝ) ^ N :=
    DyadicCode.val_mulPow2Neg_div k N hk
  have htri :=
    abs_sub_le ((approxNum k N n : ℝ) / (2 : ℝ) ^ n) ((k : ℝ) / (2 : ℝ) ^ N) δ
  have hsum :
      |(approxNum k N n : ℝ) / (2 : ℝ) ^ n - (k : ℝ) / (2 : ℝ) ^ N| +
          |(k : ℝ) / (2 : ℝ) ^ N - δ| ≤
        (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) + (2 : ℝ) ^ (-((n + 1 : ℕ) : ℤ)) := by
    refine add_le_add ?_ ?_
    · simpa [abs_sub_comm] using hround
    · simpa [hvald] using hδd
  have hclose :
      |(approxNum k N n : ℝ) / (2 : ℝ) ^ n - δ| ≤ (2 : ℝ) ^ (-(n : ℤ)) :=
    (htri.trans hsum).trans_eq (two_pow_neg_add n)
  have happx : approxFromFind cn w = approxNum k N n := by
    simp [approxFromFind, cn, hcn, k, N]
  rw [happx, hdeg]
  exact hclose

end ContinuousFOL
