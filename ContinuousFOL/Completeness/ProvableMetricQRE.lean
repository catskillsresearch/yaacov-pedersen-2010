/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: supporting lemmas for Corollary 9.11
  (effectiveness of `⊢_Q` over an r.e. set of premises, §1 / §7)
-/
module

public import ContinuousFOL.Completeness.REPredBasic
public import ContinuousFOL.Completeness.RecursivePresentation
public import ContinuousFOL.Group2Axioms.ProvableMetricQ

@[expose] public section

noncomputable section
open Classical Encodable

namespace ContinuousFOL

/-- The prefix `pre` justifies `ψ` as a proof step: a hypothesis, a logical axiom
    (a generalization of (A1)–(A14)), or the result of modus ponens from formulae
    already in `pre`. -/
def IsJustifiedMetric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (pre : List (Formula LM.toSignature)) (ψ : Formula LM.toSignature) : Prop :=
  ψ ∈ Γ ∨ ψ ∈ metricAxiomSet LM ∨
    ∃ φ, φ ∈ pre ∧ Formula.tsub ψ φ ∈ pre

/-- A finite sequence is a metric proof from `Γ` if every entry is justified by
    strictly earlier entries. -/
def IsProofSeqMetric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (σ : List (Formula LM.toSignature)) : Prop :=
  ∀ (i : ℕ) (hi : i < σ.length), IsJustifiedMetric Γ (σ.take i) (σ[i]'hi)

lemma isJustifiedMetric_append_left {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} {pre₁ pre₂ : List (Formula LM.toSignature)}
    {ψ : Formula LM.toSignature} (h : IsJustifiedMetric Γ pre₂ ψ) :
    IsJustifiedMetric Γ (pre₁ ++ pre₂) ψ := by
  rcases h with hΓ | hax | ⟨φ, hφ, himp⟩
  · exact Or.inl hΓ
  · exact Or.inr (Or.inl hax)
  · exact Or.inr (Or.inr ⟨φ, List.mem_append_right _ hφ, List.mem_append_right _ himp⟩)

lemma isProofSeqMetric_append {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} {σ τ : List (Formula LM.toSignature)}
    (hσ : IsProofSeqMetric Γ σ) (hτ : IsProofSeqMetric Γ τ) :
    IsProofSeqMetric Γ (σ ++ τ) := by
  intro i hi
  by_cases hlt : i < σ.length
  · have hidx : (σ ++ τ)[i]'hi = σ[i]'hlt := List.getElem_append_left hlt
    have htake : (σ ++ τ).take i = σ.take i :=
      List.take_append_of_le_length (Nat.le_of_lt hlt)
    rw [hidx, htake]
    exact hσ i hlt
  · have hge : σ.length ≤ i := Nat.le_of_not_lt hlt
    have hltτ : i - σ.length < τ.length := by
      simp [List.length_append] at hi
      omega
    have hidx : (σ ++ τ)[i]'hi = τ[i - σ.length]'hltτ :=
      List.getElem_append_right (as := σ) (bs := τ) (i := i) (h₁ := hge) (h₂ := hi)
    have htake : (σ ++ τ).take i = σ ++ τ.take (i - σ.length) := by
      simp [List.take_append, hge]
    rw [hidx, htake]
    exact isJustifiedMetric_append_left (hτ (i - σ.length) hltτ)

lemma isProofSeqMetric_snoc {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} {σ : List (Formula LM.toSignature)}
    {ψ : Formula LM.toSignature}
    (hσ : IsProofSeqMetric Γ σ) (hψ : IsJustifiedMetric Γ σ ψ) :
    IsProofSeqMetric Γ (σ ++ [ψ]) := by
  intro i hi
  by_cases hlt : i < σ.length
  · have hidx : (σ ++ [ψ])[i]'hi = σ[i]'hlt := List.getElem_append_left hlt
    have htake : (σ ++ [ψ]).take i = σ.take i :=
      List.take_append_of_le_length (Nat.le_of_lt hlt)
    rw [hidx, htake]
    exact hσ i hlt
  · have heq : i = σ.length := by
      simp [List.length_append] at hi
      omega
    have hidx : (σ ++ [ψ])[i]'hi = ψ := by
      revert hi
      subst heq
      intro hi
      have h := List.getElem_append_right (as := σ) (bs := [ψ]) (i := σ.length)
        (h₁ := le_rfl) (h₂ := hi)
      simp
    have htake : (σ ++ [ψ]).take i = σ := by
      subst heq
      exact List.take_left
    rw [hidx, htake]
    exact hψ

lemma mem_take_exists {α} {l : List α} {n : ℕ} {a : α} (h : a ∈ l.take n) :
    ∃ i, ∃ _hi : i < n, ∃ hlen : i < l.length, l[i]'hlen = a := by
  induction l generalizing n with
  | nil => simp at h
  | cons x xs ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      simp only [List.take_succ_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact ⟨0, Nat.succ_pos _, Nat.succ_pos _, rfl⟩
      · obtain ⟨i, hi, hlen, heq⟩ := ih h
        refine ⟨i + 1, Nat.succ_lt_succ hi, Nat.succ_lt_succ hlen, ?_⟩
        simpa using heq

lemma isProofSeqMetric_singleton_ax {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} {xs : List Var} {ψ : Formula LM.toSignature}
    (hax : MetricAxiomSchema (LM := LM) ψ) :
    IsProofSeqMetric Γ [Formula.genList xs ψ] := by
  intro i hi
  have hi0 : i = 0 := Nat.lt_one_iff.mp (by simpa using hi)
  subst hi0
  exact Or.inr (Or.inl ⟨xs, ψ, hax, rfl⟩)

lemma isProofSeqMetric_singleton_hyp {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} {ψ : Formula LM.toSignature} (hmem : ψ ∈ Γ) :
    IsProofSeqMetric Γ [ψ] := by
  intro i hi
  have hi0 : i = 0 := Nat.lt_one_iff.mp (by simpa using hi)
  subst hi0
  exact Or.inl hmem

lemma provableMetricQ_of_proofSeq {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} {σ : List (Formula LM.toSignature)}
    (hσ : IsProofSeqMetric Γ σ) :
    ∀ (i : ℕ) (hi : i < σ.length), ProvableMetricQ Γ (σ[i]'hi) := by
  intro i hi
  refine Nat.strongRecOn (motive := fun n =>
      ∀ hn : n < σ.length, ProvableMetricQ Γ (σ[n]'hn)) (n := i) ?_ hi
  intro n ih hn
  have hjust := hσ n hn
  rcases hjust with hΓ | hax | ⟨φ, hφpre, himp⟩
  · exact .hyp hΓ
  · rcases hax with ⟨xs, θ, hθ, heq⟩
    have : σ[n]'hn = Formula.genList xs θ := heq
    rw [this]
    exact .ax hθ
  · obtain ⟨j, hjn, hjl, hjφ⟩ := mem_take_exists hφpre
    obtain ⟨k, hkn, hkl, hkimp⟩ := mem_take_exists himp
    have hφp : ProvableMetricQ Γ φ := by
      simpa [hjφ] using ih j hjn hjl
    have himpp : ProvableMetricQ Γ (Formula.tsub (σ[n]'hn) φ) := by
      simpa [hkimp] using ih k hkn hkl
    exact .mp hφp himpp

/-- `Γ ⊢_Q φ` if and only if there is a finite proof sequence from `Γ` ending at `φ`. -/
lemma provableMetricQ_iff_exists_proof {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    ProvableMetricQ Γ φ ↔
      ∃ σ : List (Formula LM.toSignature),
        σ ≠ [] ∧ σ.getLast? = some φ ∧ IsProofSeqMetric Γ σ := by
  constructor
  · intro h
    induction h with
    | @ax xs ψ hax =>
      exact ⟨[Formula.genList xs ψ], by simp, by simp, isProofSeqMetric_singleton_ax hax⟩
    | @hyp ψ hmem =>
      exact ⟨[ψ], by simp, by simp, isProofSeqMetric_singleton_hyp hmem⟩
    | @mp ψ χ hψ himp ihψ ihimp =>
      obtain ⟨σ, _, hσlast, hσ⟩ := ihψ
      obtain ⟨τ, _, hτlast, hτ⟩ := ihimp
      refine ⟨σ ++ τ ++ [χ], by simp, by simp, ?_⟩
      apply isProofSeqMetric_snoc (isProofSeqMetric_append hσ hτ)
      refine Or.inr (Or.inr ⟨ψ, ?_, ?_⟩)
      · exact List.mem_append.mpr <| Or.inl <| List.mem_of_mem_getLast? hσlast
      · exact List.mem_append.mpr <| Or.inr <| List.mem_of_mem_getLast? hτlast
  · rintro ⟨σ, hne, hlast, hσ⟩
    have hlen : 0 < σ.length := List.length_pos_of_ne_nil hne
    have hidx : σ[σ.length - 1]'(Nat.sub_one_lt_of_lt hlen) = φ := by
      have := List.getLast?_eq_getElem? (l := σ)
      rw [hlast, List.getElem?_eq_getElem (Nat.sub_one_lt_of_lt hlen)] at this
      exact Option.some_inj.mp this.symm
    have := provableMetricQ_of_proofSeq hσ (σ.length - 1) (Nat.sub_one_lt_of_lt hlen)
    simpa [hidx] using this


/-- The prefix of codes `pre` justifies the formula code `c`: `c` is the code of a
    hypothesis, of a logical axiom, or of a modus-ponens conclusion from codes in `pre`. -/
def IsJustifiedMetricCode {LM : MetricSignature} (P : RecursivePresentation LM)
    (Γ : Set (Formula LM.toSignature)) (pre : List ℕ) (c : ℕ) : Prop :=
  (∃ φ ∈ Γ, P.code φ = c) ∨
  (∃ φ ∈ metricAxiomSet LM, P.code φ = c) ∨
  (∃ d ∈ pre, ∃ e ∈ pre, P.tsubCode c d = e)

/-- A list of codes is a metric proof from `Γ` if every entry is a genuine formula
    code justified by strictly earlier entries. -/
def IsProofSeqMetricCode {LM : MetricSignature} (P : RecursivePresentation LM)
    (Γ : Set (Formula LM.toSignature)) (σ : List ℕ) : Prop :=
  (∀ c ∈ σ, c ∈ Set.range P.code) ∧
  ∀ (i : ℕ) (hi : i < σ.length), IsJustifiedMetricCode P Γ (σ.take i) (σ[i]'hi)

/-- Decode a list of genuine formula codes along the injective numbering. -/
def decodeFormulaCodes {LM : MetricSignature} (P : RecursivePresentation LM)
    (σ : List ℕ) (h : ∀ c ∈ σ, c ∈ Set.range P.code) :
    List (Formula LM.toSignature) :=
  σ.attach.map fun p => Classical.choose (h p.1 p.2)

lemma decodeFormulaCodes_length {LM : MetricSignature} (P : RecursivePresentation LM)
    (σ : List ℕ) (h : ∀ c ∈ σ, c ∈ Set.range P.code) :
    (decodeFormulaCodes P σ h).length = σ.length := by
  simp [decodeFormulaCodes]

lemma decodeFormulaCodes_get {LM : MetricSignature} (P : RecursivePresentation LM)
    (σ : List ℕ) (h : ∀ c ∈ σ, c ∈ Set.range P.code) (i : ℕ) (hi : i < σ.length) :
    (decodeFormulaCodes P σ h)[i]'(by simpa [decodeFormulaCodes_length] using hi) =
      Classical.choose (h (σ[i]'hi) (List.getElem_mem hi)) := by
  simp [decodeFormulaCodes, List.getElem_map, List.getElem_attach]

lemma decodeFormulaCodes_code {LM : MetricSignature} (P : RecursivePresentation LM)
    (σ : List ℕ) (h : ∀ c ∈ σ, c ∈ Set.range P.code) :
    (decodeFormulaCodes P σ h).map P.code = σ := by
  apply List.ext_getElem
  · simp [decodeFormulaCodes]
  · intro i hi hi'
    have hiσ : i < σ.length := by simpa [decodeFormulaCodes] using hi
    rw [List.getElem_map P.code, decodeFormulaCodes_get P σ h i hiσ]
    exact Classical.choose_spec (h (σ[i]'hiσ) (List.getElem_mem hiσ))

lemma decodeFormulaCodes_map_code {LM : MetricSignature} (P : RecursivePresentation LM)
    (σ : List (Formula LM.toSignature)) :
    decodeFormulaCodes P (σ.map P.code)
      (by
        intro c hc
        obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hc
        exact ⟨φ, rfl⟩) = σ := by
  refine (List.map_injective_iff.mpr P.code_injective) ?_
  simp [decodeFormulaCodes_code]

lemma isJustifiedMetric_iff_code {LM : MetricSignature} (P : RecursivePresentation LM)
    {Γ : Set (Formula LM.toSignature)} {pre : List (Formula LM.toSignature)}
    {ψ : Formula LM.toSignature} :
    IsJustifiedMetric Γ pre ψ ↔
      IsJustifiedMetricCode P Γ (pre.map P.code) (P.code ψ) := by
  constructor
  · intro h
    rcases h with hΓ | hax | ⟨φ, hφ, himp⟩
    · exact Or.inl ⟨ψ, hΓ, rfl⟩
    · exact Or.inr (Or.inl ⟨ψ, hax, rfl⟩)
    · refine Or.inr (Or.inr ⟨P.code φ, List.mem_map_of_mem hφ,
        P.code (Formula.tsub ψ φ), List.mem_map_of_mem himp, P.tsubCode_spec ψ φ⟩)
  · intro h
    rcases h with ⟨φ, hΓ, hcode⟩ | ⟨φ, hax, hcode⟩ | ⟨d, hd, e, he, htsub⟩
    · exact Or.inl (P.code_injective hcode ▸ hΓ)
    · exact Or.inr (Or.inl (P.code_injective hcode ▸ hax))
    · obtain ⟨φ, hφ, rfl⟩ := List.mem_map.mp hd
      obtain ⟨χ, hχ, rfl⟩ := List.mem_map.mp he
      have hχ' : Formula.tsub ψ φ = χ :=
        P.code_injective (by rw [← P.tsubCode_spec, htsub])
      exact Or.inr (Or.inr ⟨φ, hφ, hχ' ▸ hχ⟩)

lemma isProofSeqMetric_iff_code {LM : MetricSignature} (P : RecursivePresentation LM)
    {Γ : Set (Formula LM.toSignature)} {σ : List (Formula LM.toSignature)} :
    IsProofSeqMetric Γ σ ↔ IsProofSeqMetricCode P Γ (σ.map P.code) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro c hc
      obtain ⟨φ, _, rfl⟩ := List.mem_map.mp hc
      exact ⟨φ, rfl⟩
    · intro i hi
      have hiσ : i < σ.length := by simpa using hi
      have hidx : (σ.map P.code)[i]'hi = P.code (σ[i]'hiσ) := List.getElem_map P.code
      have htake : (σ.map P.code).take i = (σ.take i).map P.code := (List.map_take).symm
      rw [hidx, htake]
      exact (isJustifiedMetric_iff_code P).mp (h i hiσ)
  · intro ⟨_, hjust⟩ i hi
    have hi' : i < (σ.map P.code).length := by simpa using hi
    have hjusti := hjust i hi'
    have hidx : (σ.map P.code)[i]'hi' = P.code (σ[i]'hi) := List.getElem_map P.code
    have htake : (σ.map P.code).take i = (σ.take i).map P.code := (List.map_take).symm
    rw [hidx, htake] at hjusti
    exact (isJustifiedMetric_iff_code P).mpr hjusti

lemma isProofSeqMetricCode_decode {LM : MetricSignature} (P : RecursivePresentation LM)
    {Γ : Set (Formula LM.toSignature)} {σ : List ℕ}
    (h : IsProofSeqMetricCode P Γ σ) :
    IsProofSeqMetric Γ (decodeFormulaCodes P σ h.1) := by
  have hmap : (decodeFormulaCodes P σ h.1).map P.code = σ :=
    decodeFormulaCodes_code P σ h.1
  rw [isProofSeqMetric_iff_code (P := P), hmap]
  exact h

/-- `Γ ⊢_Q φ` if and only if some finite list of codes is a proof from `Γ` ending at `⌜φ⌝`. -/
lemma provableMetricQ_iff_exists_code_proof {LM : MetricSignature}
    (P : RecursivePresentation LM) (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) :
    ProvableMetricQ Γ φ ↔
      ∃ σ : List ℕ, σ ≠ [] ∧ σ.getLast? = some (P.code φ) ∧
        IsProofSeqMetricCode P Γ σ := by
  rw [provableMetricQ_iff_exists_proof]
  constructor
  · intro ⟨σ, hne, hlast, hσ⟩
    refine ⟨σ.map P.code, by simp [hne], ?_, (isProofSeqMetric_iff_code P).mp hσ⟩
    simp [List.getLast?_map, hlast]
  · intro ⟨cs, hne, hlast, hcs⟩
    refine ⟨decodeFormulaCodes P cs hcs.1, ?_, ?_, isProofSeqMetricCode_decode P hcs⟩
    · simp [decodeFormulaCodes, hne]
    · have hlen : 0 < cs.length := List.length_pos_of_ne_nil hne
      have hlast_get : cs[cs.length - 1]'(Nat.sub_one_lt_of_lt hlen) = P.code φ := by
        have := List.getLast?_eq_getElem? (l := cs)
        rw [hlast, List.getElem?_eq_getElem (Nat.sub_one_lt_of_lt hlen)] at this
        exact Option.some_inj.mp this.symm
      have hdec_len : (decodeFormulaCodes P cs hcs.1).length = cs.length :=
        decodeFormulaCodes_length P cs hcs.1
      have hdec_last :
          (decodeFormulaCodes P cs hcs.1).getLast? =
            some ((decodeFormulaCodes P cs hcs.1)[cs.length - 1]'
              (by simpa [hdec_len] using Nat.sub_one_lt_of_lt hlen)) := by
        have := List.getLast?_eq_getElem? (l := decodeFormulaCodes P cs hcs.1)
        rw [hdec_len] at this
        have hlt : cs.length - 1 < (decodeFormulaCodes P cs hcs.1).length := by
          simpa [hdec_len] using Nat.sub_one_lt_of_lt hlen
        rw [List.getElem?_eq_getElem hlt] at this
        exact this
      rw [hdec_last]
      apply congrArg some
      apply P.code_injective
      have hget := decodeFormulaCodes_get P cs hcs.1 (cs.length - 1)
        (Nat.sub_one_lt_of_lt hlen)
      rw [hget]
      exact (Classical.choose_spec
        (hcs.1 (cs[cs.length - 1]'(Nat.sub_one_lt_of_lt hlen))
          (List.getElem_mem (Nat.sub_one_lt_of_lt hlen)))).trans hlast_get

lemma isJustifiedMetricCode_mp_computable {LM : MetricSignature}
    (P : RecursivePresentation LM) :
    ComputablePred (fun p : List ℕ × ℕ =>
      ∃ d ∈ p.1, ∃ e ∈ p.1, P.tsubCode p.2 d = e) := by
  have hinter : ComputablePred (fun p : List ℕ × (ℕ × ℕ) =>
      ∃ e ∈ p.1, P.tsubCode p.2.1 p.2.2 = e) :=
    ComputablePred.exists_mem_list_rel
      (r := fun e (cd : ℕ × ℕ) => P.tsubCode cd.1 cd.2 = e)
      (ComputablePred.comp_eq
        (P.tsubCode_computable.comp (Computable.fst.comp Computable.snd)
          (Computable.snd.comp Computable.snd))
        Computable.fst)
  have houter_r : ComputablePred (fun q : ℕ × (List ℕ × ℕ) =>
      ∃ e ∈ q.2.1, P.tsubCode q.2.2 q.1 = e) :=
    ComputablePred.comp
      (p := fun p : List ℕ × (ℕ × ℕ) => ∃ e ∈ p.1, P.tsubCode p.2.1 p.2.2 = e)
      hinter
      ((Computable.fst.comp Computable.snd).pair
        ((Computable.snd.comp Computable.snd).pair Computable.fst))
  exact ComputablePred.comp
    (p := fun p : List ℕ × (List ℕ × ℕ) => ∃ d ∈ p.1, ∃ e ∈ p.2.1, P.tsubCode p.2.2 d = e)
    (ComputablePred.exists_mem_list_rel
      (r := fun d (pre_c : List ℕ × ℕ) => ∃ e ∈ pre_c.1, P.tsubCode pre_c.2 d = e)
      houter_r)
    (Computable.fst.pair (Computable.fst.pair Computable.snd))

lemma isJustifiedMetricCode_re {LM : MetricSignature} (P : RecursivePresentation LM)
    {Γ : Set (Formula LM.toSignature)}
    (hΓ : REPred (fun n => ∃ φ ∈ Γ, P.code φ = n)) :
    REPred (fun p : List ℕ × ℕ => IsJustifiedMetricCode P Γ p.1 p.2) := by
  have hhyp : REPred (fun p : List ℕ × ℕ => ∃ φ ∈ Γ, P.code φ = p.2) :=
    REPred.computable_comp
      (p := fun n : ℕ => ∃ φ ∈ Γ, P.code φ = n) Computable.snd hΓ
  have hax : REPred (fun p : List ℕ × ℕ =>
      ∃ φ ∈ metricAxiomSet LM, P.code φ = p.2) :=
    REPred.computable_comp
      (p := fun n : ℕ => ∃ φ ∈ metricAxiomSet LM, P.code φ = n)
      Computable.snd P.axioms_re
  have hmp := isJustifiedMetricCode_mp_computable P
  exact (REPred.or hhyp (REPred.or hax (ComputablePred.to_re' hmp))).of_eq
    fun _ => Iff.rfl

lemma isProofSeqMetricCode_re {LM : MetricSignature} (P : RecursivePresentation LM)
    {Γ : Set (Formula LM.toSignature)}
    (hΓ : REPred (fun n => ∃ φ ∈ Γ, P.code φ = n)) :
    REPred (fun σ : List ℕ => IsProofSeqMetricCode P Γ σ) := by
  have hcodes : ComputablePred (fun σ : List ℕ => ∀ c ∈ σ, c ∈ Set.range P.code) :=
    ComputablePred.forall_mem_list P.isCode_computable
  have hjust := isJustifiedMetricCode_re P hΓ
  have hjust_i : REPred (fun p : List ℕ × ℕ =>
      IsJustifiedMetricCode P Γ (p.1.take p.2) (p.1.getD p.2 0)) :=
    REPred.computable_comp
      (p := fun p : List ℕ × ℕ => IsJustifiedMetricCode P Γ p.1 p.2)
      ((Primrec.list_take.to_comp.comp Computable.snd Computable.fst).pair
        ((Primrec.list_getD 0).to_comp.comp Computable.fst Computable.snd))
      hjust
  have hall : REPred (fun p : List ℕ × ℕ =>
      ∀ i < p.2, IsJustifiedMetricCode P Γ (p.1.take i) (p.1.getD i 0)) :=
    REPred.forall_lt (r := fun (σ : List ℕ) i =>
      IsJustifiedMetricCode P Γ (σ.take i) (σ.getD i 0)) hjust_i
  have hallσ : REPred (fun σ : List ℕ =>
      ∀ i < σ.length, IsJustifiedMetricCode P Γ (σ.take i) (σ.getD i 0)) :=
    REPred.computable_comp
      (p := fun p : List ℕ × ℕ =>
        ∀ i < p.2, IsJustifiedMetricCode P Γ (p.1.take i) (p.1.getD i 0))
      (Computable.id.pair Computable.list_length) hall
  refine (REPred.and (ComputablePred.to_re' hcodes) hallσ).of_eq fun σ => ?_
  constructor
  · intro ⟨hc, hj⟩
    refine ⟨hc, ?_⟩
    intro i hi
    have hget : σ.getD i 0 = σ[i]'hi := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    rw [← hget]
    exact hj i hi
  · intro ⟨hc, hj⟩
    refine ⟨hc, ?_⟩
    intro i hi
    have hget : σ.getD i 0 = σ[i]'hi := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      rfl
    rw [hget]
    exact hj i hi

/-- The set of codes of formulae provable from an r.e. set of premises is r.e. -/
lemma provableMetricQ_codes_re {LM : MetricSignature} (P : RecursivePresentation LM)
    (Γ : Set (Formula LM.toSignature))
    (hΓ : REPred (fun n => ∃ φ ∈ Γ, P.code φ = n)) :
    REPred (fun n => ∃ φ, ProvableMetricQ Γ φ ∧ P.code φ = n) := by
  have hseq := isProofSeqMetricCode_re P hΓ
  have hne : ComputablePred (fun σ : List ℕ => σ ≠ []) :=
    (ComputablePred.not
      (ComputablePred.comp_eq Computable.list_length (Computable.const 0))).of_eq
      fun σ => by simp
  have hlast : ComputablePred (fun p : ℕ × List ℕ => p.2.getLast? = some p.1) :=
    ComputablePred.comp_eq
      (computable_getLast? (α := ℕ) |>.comp Computable.snd)
      (Computable.option_some.comp Computable.fst)
  have hpred : REPred (fun p : ℕ × List ℕ =>
      p.2 ≠ [] ∧ p.2.getLast? = some p.1 ∧ IsProofSeqMetricCode P Γ p.2) :=
    REPred.and
      (ComputablePred.to_re'
        (ComputablePred.comp (p := fun σ : List ℕ => σ ≠ []) hne Computable.snd))
      (REPred.and (ComputablePred.to_re' hlast)
        (REPred.computable_comp
          (p := fun σ : List ℕ => IsProofSeqMetricCode P Γ σ)
          Computable.snd hseq))
  have hiff : ∀ n, (∃ φ, ProvableMetricQ Γ φ ∧ P.code φ = n) ↔
      ∃ σ : List ℕ, σ ≠ [] ∧ σ.getLast? = some n ∧ IsProofSeqMetricCode P Γ σ := by
    intro n
    constructor
    · intro ⟨φ, hpr, hc⟩
      obtain ⟨σ, h1, h2, h3⟩ := (provableMetricQ_iff_exists_code_proof P Γ φ).mp hpr
      exact ⟨σ, h1, hc ▸ h2, h3⟩
    · intro ⟨σ, h1, h2, h3⟩
      have hn : n ∈ Set.range P.code := h3.1 n (List.mem_of_mem_getLast? h2)
      obtain ⟨φ, rfl⟩ := hn
      exact ⟨φ, (provableMetricQ_iff_exists_code_proof P Γ φ).mpr ⟨σ, h1, h2, h3⟩, rfl⟩
  exact (REPred.exists (r := fun n σ =>
      σ ≠ [] ∧ σ.getLast? = some n ∧ IsProofSeqMetricCode P Γ σ) hpred).of_eq
    fun n => (hiff n).symm

end ContinuousFOL
