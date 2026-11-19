/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: supporting lemmas for Corollary 9.11
-/
module

public import Mathlib.Computability.RE
public import Mathlib.Computability.PartrecCode

@[expose] public section

noncomputable section
open Classical Encodable
open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace ContinuousFOL

/-- `Part.assert p (fun _ => some ())` is defined if and only if `p`. -/
lemma Part.assert_unit_dom (p : Prop) :
    (Part.assert p fun _ => Part.some ()).Dom ↔ p := by
  constructor
  · intro h
    simpa [Part.assert] using h
  · intro hp
    simp [Part.assert, hp]

/-- Kleene normal form: an r.e. predicate is the projection of a computable
    binary predicate. -/
lemma REPred.exists_computable {α} [Primcodable α] {p : α → Prop} (hp : REPred p) :
    ∃ q : α → ℕ → Bool, Computable₂ q ∧ ∀ a, p a ↔ ∃ n, q a n = true := by
  have hNat : Nat.Partrec fun n =>
      Part.bind (decode (α := α) n) fun a =>
        (Part.assert (p a) fun _ => Part.some ()).map encode := hp
  obtain ⟨c, hc⟩ := exists_code.mp hNat
  refine ⟨fun a k => (evaln k c (encode a)).isSome, ?_, ?_⟩
  · change Computable fun p : α × ℕ => (evaln p.2 c (encode p.1)).isSome
    have hpack : Computable fun p : α × ℕ => ((p.2, c), encode p.1) :=
      (Computable.snd.pair (Computable.const c)).pair (Computable.encode.comp Computable.fst)
    have heval : Computable fun p : α × ℕ => evaln p.2 c (encode p.1) :=
      primrec_evaln.to_comp.comp hpack
    exact Primrec.option_isSome.to_comp.comp heval
  · intro a
    have heq : (eval c) (encode a) =
        (Part.assert (p a) fun _ => Part.some ()).map encode := by
      rw [hc]
      simp [encodek]
    have hdom : p a ↔ ((eval c) (encode a)).Dom := by
      rw [heq]
      constructor
      · intro hp; simp [Part.assert, hp]
      · intro h
        simpa [Part.assert, Part.map] using h
    have hr : (eval c) (encode a) = Nat.rfindOpt fun k => evaln k c (encode a) :=
      eval_eq_rfindOpt _ _
    have hsome : ((eval c) (encode a)).Dom ↔ ∃ k, (evaln k c (encode a)).isSome := by
      rw [hr, Nat.rfindOpt_dom]
      simp [Option.isSome_iff_exists]
    exact hdom.trans hsome

/-- A computable existential projection of a computable Boolean predicate is r.e. -/
lemma REPred.of_computable_sigma {α} [Primcodable α] {q : α → ℕ → Bool}
    (hq : Computable₂ q) : REPred (fun a => ∃ n, q a n = true) := by
  let p : α → ℕ →. Bool := fun a n => Part.some (q a n)
  have hr : Partrec fun a => Nat.rfind (p a) := Partrec.rfind hq.partrec
  exact (Partrec.dom_re hr).of_eq fun a => by
    constructor
    · intro h
      obtain ⟨n, hn⟩ := Part.dom_iff_mem.mp h
      have := Nat.rfind_spec hn
      exact ⟨n, by simpa [p] using this⟩
    · intro ⟨n, hn⟩
      have hmem : true ∈ p a n := by simp [p, hn]
      obtain ⟨m, hm, _⟩ := Nat.rfind_min' (by simpa [p] using hn : (fun k => q a k) n)
      exact Part.dom_iff_mem.mpr ⟨m, hm⟩

/-- Recursively enumerable predicates are closed under precomposition with a
    computable function. -/
lemma REPred.computable_comp {α β} [Primcodable α] [Primcodable β]
    {f : α → β} {p : β → Prop} (hf : Computable f) (hp : REPred p) :
    REPred (fun a => p (f a)) :=
  hp.comp hf

/-- Recursively enumerable predicates are closed under disjunction. -/
lemma REPred.or {α} [Primcodable α] {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun a => p a ∨ q a) := by
  obtain ⟨k, hk, hK⟩ := Partrec.merge' hp hq
  exact (Partrec.dom_re hk).of_eq fun a => by
    rw [(hK a).2]
    simp [Part.assert_unit_dom]

/-- Recursively enumerable predicates are closed under conjunction. -/
lemma REPred.and {α} [Primcodable α] {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred (fun a => p a ∧ q a) := by
  have hg : Partrec₂ fun (a : α) (_ : Unit) =>
      Part.assert (q a) fun _ => Part.some () :=
    hq.comp Computable.fst
  have h : Partrec fun a =>
      (Part.assert (p a) fun _ => Part.some ()).bind
        fun _ => Part.assert (q a) fun _ => Part.some () :=
    Partrec.bind hp hg
  exact (Partrec.dom_re h).of_eq fun a => by
    simp [Part.bind_dom, Part.assert_unit_dom]

/-- Recursively enumerable predicates are closed under existential quantification
    over a `Primcodable` type. -/
lemma REPred.exists {α β} [Primcodable α] [Primcodable β] {r : α → β → Prop}
    (hr : REPred (fun p : α × β => r p.1 p.2)) :
    REPred (fun a => ∃ b, r a b) := by
  obtain ⟨q, hq, hqiff⟩ := REPred.exists_computable hr
  let q' : α → ℕ → Bool := fun a m =>
    Option.casesOn (decode (α := β × ℕ) m) false (fun bn => q (a, bn.1) bn.2)
  have hq' : Computable₂ q' :=
    Computable.option_casesOn (Computable.decode.comp Computable.snd)
      (Computable.const false)
      (hq.comp
        (Computable.fst.comp Computable.fst |>.pair (Computable.fst.comp Computable.snd))
        (Computable.snd.comp Computable.snd))
  have hiff : ∀ a, (∃ b, r a b) ↔ ∃ m, q' a m = true := by
    intro a
    constructor
    · intro ⟨b, hb⟩
      obtain ⟨n, hn⟩ := (hqiff (a, b)).mp hb
      refine ⟨encode (b, n), ?_⟩
      simp [q', encodek, hn]
    · intro ⟨m, hm⟩
      have hm' : Option.casesOn (decode (α := β × ℕ) m) false
          (fun bn => q (a, bn.1) bn.2) = true := hm
      cases hdec : decode (α := β × ℕ) m with
      | none =>
        rw [hdec] at hm'
        exact False.elim (Bool.false_ne_true hm')
      | some bn =>
        rw [hdec] at hm'
        exact ⟨bn.1, (hqiff (a, bn.1)).mpr ⟨bn.2, hm'⟩⟩
  exact (REPred.of_computable_sigma hq').of_eq fun a => (hiff a).symm

/-- A computable predicate, viewed as r.e., after precomposition or boolean
    combination, remains r.e. -/
lemma ComputablePred.to_re' {α} [Primcodable α] {p : α → Prop}
    (hp : ComputablePred p) : REPred p :=
  hp.to_re


/-- Computable predicates are closed under conjunction. -/
lemma ComputablePred.and {α} [Primcodable α] {p q : α → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun a => p a ∧ q a) := by
  classical
  exact Computable.computablePred
    ((Primrec.and.to_comp.comp hp.decide hq.decide).of_eq fun _ => by simp)

/-- Computable predicates are closed under disjunction. -/
lemma ComputablePred.or {α} [Primcodable α] {p q : α → Prop}
    (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred (fun a => p a ∨ q a) := by
  classical
  exact Computable.computablePred
    ((Primrec.or.to_comp.comp hp.decide hq.decide).of_eq fun _ => by simp)

/-- Computable predicates are closed under precomposition with a computable function. -/
lemma ComputablePred.comp {α β} [Primcodable α] [Primcodable β]
    {f : α → β} {p : β → Prop} (hp : ComputablePred p) (hf : Computable f) :
    ComputablePred (fun a => p (f a)) := by
  classical
  exact Computable.computablePred (hp.decide.comp hf)

/-- Equality of the values of two computable functions is a computable predicate. -/
lemma ComputablePred.comp_eq {α β} [Primcodable α] [Primcodable β] [DecidableEq β]
    {f g : α → β} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun a => f a = g a) :=
  ComputablePred.comp (p := fun p : β × β => p.1 = p.2)
    (PrimrecPred.computablePred Primrec.eq) (hf.pair hg)

/-- `Option.elim False p` of a computable option-valued function is a computable predicate. -/
lemma ComputablePred.option_elim_false {α β} [Primcodable α] [Primcodable β]
    {o : α → Option β} {p : β → Prop}
    (ho : Computable o) (hp : ComputablePred p) :
    ComputablePred (fun a => (o a).elim False p) := by
  obtain ⟨dec, hcomp⟩ := hp
  let inst : DecidablePred (fun a => (o a).elim False p) := fun a =>
    Option.rec (motive := fun ox => Decidable (ox.elim False p))
      (inferInstanceAs (Decidable False)) (fun b => dec b) (o a)
  refine ⟨inst, ?_⟩
  refine (Computable.option_casesOn ho (Computable.const false)
      (hcomp.comp Computable.snd).to₂).of_eq ?_
  intro a
  cases h : o a <;> simp [h, Option.elim]

/-- Bounded universal quantification of a computable predicate is computable. -/
lemma ComputablePred.forall_lt {α} [Primcodable α] {p : α → ℕ → Prop}
    (hp : ComputablePred (fun q : α × ℕ => p q.1 q.2)) :
    ComputablePred (fun q : α × ℕ => ∀ i < q.2, p q.1 i) := by
  classical
  let step : (α × ℕ) → ℕ × Bool → Bool :=
    fun q yIH => yIH.2 && decide (p q.1 yIH.1)
  have hstep : Computable₂ step :=
    (Primrec.and.to_comp.comp (Computable.snd.comp Computable.snd)
      (hp.decide.comp
        ((Computable.fst.comp Computable.fst).pair
          (Computable.fst.comp Computable.snd))))
  have hf : Computable fun q : α × ℕ =>
      Nat.rec (motive := fun _ => Bool) true (fun y IH => step q (y, IH)) q.2 :=
    Computable.nat_rec (σ := Bool) Computable.snd (Computable.const true) hstep
  have hiff : ∀ a n,
      (Nat.rec (motive := fun _ => Bool) true
        (fun i ih => ih && decide (p a i)) n = true) ↔ ∀ i < n, p a i := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      show ((Nat.rec (motive := fun _ => Bool) true
          (fun i ih => ih && decide (p a i)) n && decide (p a n)) = true) ↔
        ∀ i < n + 1, p a i
      rw [Bool.and_eq_true, decide_eq_true_eq, ih]
      constructor
      · intro ⟨hall, hn⟩ i hi
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact hall i hlt
        · exact hn
      · intro hall
        exact ⟨fun i hi => hall i (Nat.lt_succ_of_lt hi), hall n (Nat.lt_succ_self _)⟩
  exact (Computable.computablePred hf).of_eq fun q => by
    simpa [step] using hiff q.1 q.2

/-- Bounded existential quantification of a computable predicate is computable. -/
lemma ComputablePred.exists_lt {α} [Primcodable α] {p : α → ℕ → Prop}
    (hp : ComputablePred (fun q : α × ℕ => p q.1 q.2)) :
    ComputablePred (fun q : α × ℕ => ∃ i < q.2, p q.1 i) :=
  (ComputablePred.not (ComputablePred.forall_lt (p := fun a i => ¬ p a i)
    (ComputablePred.not hp))).of_eq fun _ => by simp [not_forall]

/-- Membership-quantified “for all” over a list, for a computable predicate. -/
lemma ComputablePred.forall_mem_list {α} [Primcodable α] {p : α → Prop}
    (hp : ComputablePred p) :
    ComputablePred (fun l : List α => ∀ a ∈ l, p a) := by
  classical
  have hp' : ComputablePred (fun q : List α × ℕ => (q.1[q.2]?).elim False p) :=
    ComputablePred.option_elim_false
      (Computable.list_getElem?.comp Computable.fst Computable.snd) hp
  exact (ComputablePred.comp
      (ComputablePred.forall_lt (p := fun l i => (l[i]?).elim False p) hp')
      (Computable.id.pair Computable.list_length)).of_eq fun l => by
    change (∀ i < l.length, (l[i]?).elim False p) ↔ ∀ a ∈ l, p a
    constructor
    · intro h a ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      have hi' := h i hi
      rw [List.getElem?_eq_getElem hi] at hi'
      exact hi'
    · intro h i hi
      rw [List.getElem?_eq_getElem hi]
      exact h (l[i]'hi) (List.getElem_mem hi)

/-- Membership-quantified “there exists” over a list, for a computable predicate. -/
lemma ComputablePred.exists_mem_list {α} [Primcodable α] {p : α → Prop}
    (hp : ComputablePred p) :
    ComputablePred (fun l : List α => ∃ a ∈ l, p a) :=
  (ComputablePred.not (ComputablePred.forall_mem_list (ComputablePred.not hp))).of_eq
    fun _ => by simp [not_forall]

/-- Bounded universal quantification of an r.e. predicate is r.e. -/
lemma REPred.forall_lt {α} [Primcodable α] {r : α → ℕ → Prop}
    (hr : REPred (fun p : α × ℕ => r p.1 p.2)) :
    REPred (fun p : α × ℕ => ∀ i < p.2, r p.1 i) := by
  obtain ⟨q, hq, hqiff⟩ := REPred.exists_computable hr
  let s : (α × ℕ) × List ℕ → Prop := fun p =>
    p.2.length = p.1.2 ∧ ∀ i < p.1.2, q (p.1.1, i) (p.2.getD i 0) = true
  have hs : ComputablePred s := by
    have hlen : ComputablePred (fun p : (α × ℕ) × List ℕ => p.2.length = p.1.2) :=
      ComputablePred.comp_eq (Computable.list_length.comp Computable.snd)
        (Computable.snd.comp Computable.fst)
    have hq' : ComputablePred
        (fun t : ((α × ℕ) × List ℕ) × ℕ => q (t.1.1.1, t.2) (t.1.2.getD t.2 0) = true) :=
      ComputablePred.comp_eq
        (hq.comp
          ((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair Computable.snd)
          ((Primrec.list_getD 0).to_comp.comp
            (Computable.snd.comp Computable.fst) Computable.snd))
        (Computable.const true)
    have hqlt : ComputablePred
        (fun p : (α × ℕ) × List ℕ => ∀ i < p.1.2, q (p.1.1, i) (p.2.getD i 0) = true) :=
      ComputablePred.comp
        (ComputablePred.forall_lt
          (p := fun (p : (α × ℕ) × List ℕ) i => q (p.1.1, i) (p.2.getD i 0) = true) hq')
        (Computable.id.pair (Computable.snd.comp Computable.fst))
    exact ComputablePred.and hlen hqlt
  have hiff : ∀ p : α × ℕ, (∀ i < p.2, r p.1 i) ↔ ∃ ks : List ℕ, s (p, ks) := by
    intro p
    constructor
    · intro hall
      let ks : List ℕ := (List.range p.2).map fun i =>
        if hi : i < p.2 then
          Classical.choose ((hqiff (p.1, i)).mp (hall i hi))
        else 0
      refine ⟨ks, ?_, ?_⟩
      · simp [ks]
      · intro i hi
        have hlenks : ks.length = p.2 := by simp [ks]
        have hlt : i < ks.length := by simpa [hlenks] using hi
        have hget : ks[i]'hlt =
            Classical.choose ((hqiff (p.1, i)).mp (hall i hi)) := by
          simp [ks, List.getElem_map, List.getElem_range, hi]
        have : ks.getD i 0 = Classical.choose ((hqiff (p.1, i)).mp (hall i hi)) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, hget]
          rfl
        rw [this]
        exact Classical.choose_spec ((hqiff (p.1, i)).mp (hall i hi))
    · intro ⟨ks, hlen, hks⟩ i hi
      exact (hqiff (p.1, i)).mpr ⟨ks.getD i 0, hks i hi⟩
  have hs_re : REPred (fun p : (α × ℕ) × List ℕ => s p) := ComputablePred.to_re' hs
  exact (REPred.exists hs_re).of_eq fun p => (hiff p).symm

/-- `o.map (fun a => (a, b))` is computable in `(o, b)`. -/
lemma computable_option_pair {α β} [Primcodable α] [Primcodable β] :
    Computable₂ (fun (o : Option α) (b : β) => o.map fun a => (a, b)) :=
  (Computable.option_casesOn (f := fun _ : Option α × β => (none : Option (α × β)))
      (g := fun (p : Option α × β) a => some (a, p.2))
      Computable.fst (Computable.const none)
      ((Computable.option_some.comp
          (Computable.snd.pair (Computable.snd.comp Computable.fst))).to₂)).of_eq
    fun p => by cases p.1 <;> rfl

/-- Relational “there exists in a list”: `∃ a ∈ l, r a b`, for a computable relation. -/
lemma ComputablePred.exists_mem_list_rel {α β} [Primcodable α] [Primcodable β]
    {r : α → β → Prop} (hr : ComputablePred (fun p : α × β => r p.1 p.2)) :
    ComputablePred (fun p : List α × β => ∃ a ∈ p.1, r a p.2) := by
  have ho : Computable (fun q : (List α × β) × ℕ =>
      (q.1.1[q.2]?).map fun a => (a, q.1.2)) :=
    computable_option_pair.comp
      (Computable.list_getElem?.comp (Computable.fst.comp Computable.fst) Computable.snd)
      (Computable.snd.comp Computable.fst)
  have hp : ComputablePred (fun q : (List α × β) × ℕ =>
      ((q.1.1[q.2]?).map fun a => (a, q.1.2)).elim False fun pair => r pair.1 pair.2) :=
    ComputablePred.option_elim_false ho hr
  exact (ComputablePred.comp
      (ComputablePred.exists_lt
        (p := fun (p : List α × β) i =>
          ((p.1[i]?).map fun a => (a, p.2)).elim False fun q => r q.1 q.2) hp)
      (Computable.id.pair (Computable.list_length.comp Computable.fst))).of_eq fun p => by
    change (∃ i < p.1.length,
        ((p.1[i]?).map fun a => (a, p.2)).elim False fun q => r q.1 q.2) ↔
      ∃ a ∈ p.1, r a p.2
    constructor
    · intro ⟨i, hi, h⟩
      rw [List.getElem?_eq_getElem hi] at h
      exact ⟨p.1[i]'hi, List.getElem_mem hi, by simpa using h⟩
    · intro ⟨a, ha, hrab⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      refine ⟨i, hi, ?_⟩
      simp [List.getElem?_eq_getElem hi, hrab]

/-- `List.getLast?` is computable. -/
lemma computable_getLast? {α} [Primcodable α] :
    Computable (List.getLast? : List α → Option α) :=
  (Primrec.list_head?.to_comp.comp Primrec.list_reverse.to_comp).of_eq fun l =>
    (List.getLast?_eq_head?_reverse (xs := l)).symm

end ContinuousFOL
