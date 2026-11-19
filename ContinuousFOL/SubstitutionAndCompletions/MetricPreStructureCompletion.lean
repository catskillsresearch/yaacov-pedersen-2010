/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Theorem 6.9; vision.md page 13
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.PiCompletion
public import ContinuousFOL.SubstitutionAndCompletions.EvalUniformlyContinuous
public import ContinuousFOL.SubstitutionAndCompletions.ElementaryLMorphism
public import ContinuousFOL.LanguageAndSemantics.ContinuousStructure
public import ContinuousFOL.LanguageAndSemantics.UpdateAssign
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section

noncomputable section
open Classical
open scoped Uniformity
open UniformSpace

namespace ContinuousFOL

/-- The underlying pseudo-metric of a metric pre-structure (Definition 5.6 (iii)). -/
@[instance_reducible]
instance MetricPreStructure.instPseudoMetricSpace {LM : MetricSignature}
    (M : MetricPreStructure LM) : PseudoMetricSpace M.Carrier where
  dist := M.distVal
  dist_self := M.dist_self
  dist_comm := M.dist_symm
  dist_triangle := M.dist_triangle

lemma dist_eq_distVal {LM : MetricSignature} (M : MetricPreStructure LM)
    (x y : M.Carrier) : dist x y = M.distVal x y := rfl

lemma funcInterp_uniformContinuous {LM : MetricSignature}
    (M : MetricPreStructure LM) (f : LM.Func) :
    UniformContinuous (M.funcInterp f) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  set ε' := min (ε / 2) 1
  have hε'0 : 0 < ε' := lt_min (half_pos hε) zero_lt_one
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  obtain ⟨δ, hδ, H⟩ := funcInterp_unif_cont M f hε'0 hε'1
  refine ⟨δ, hδ, ?_⟩
  intro u v huv
  have hcoords : ∀ i, M.distVal (u i) (v i) < δ := by
    intro i
    have := (dist_pi_lt_iff hδ).mp huv i
    simpa [dist_eq_distVal] using this
  have hle := H u v hcoords
  have hlt : (ε' : ℝ) < ε :=
    (min_le_left (ε / 2) 1).trans_lt (half_lt_self hε)
  have : dist (M.funcInterp f u) (M.funcInterp f v) ≤ ε' := by
    simpa [dist_eq_distVal] using hle
  exact this.trans_lt hlt

lemma relInterp_uniformContinuous {LM : MetricSignature}
    (M : MetricPreStructure LM) (P : LM.Rel) :
    UniformContinuous (M.relInterp P) := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  set ε' := min (ε / 2) 1
  have hε'0 : 0 < ε' := lt_min (half_pos hε) zero_lt_one
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  obtain ⟨δ, hδ, H⟩ := relInterp_unif_cont M P hε'0 hε'1
  refine ⟨δ, hδ, ?_⟩
  intro u v huv
  have hcoords : ∀ i, M.distVal (u i) (v i) < δ := by
    intro i
    have := (dist_pi_lt_iff hδ).mp huv i
    simpa [dist_eq_distVal] using this
  have hle := H u v hcoords
  have hlt : (ε' : ℝ) < ε :=
    (min_le_left (ε / 2) 1).trans_lt (half_lt_self hε)
  have : |M.relInterp P u - M.relInterp P v| ≤ ε' := hle
  exact this.trans_lt hlt

lemma funcInterp_coe_uniformContinuous {LM : MetricSignature}
    (M : MetricPreStructure LM) (f : LM.Func) :
    UniformContinuous (fun v => (M.funcInterp f v : Completion M.Carrier)) := by
  have hf := funcInterp_uniformContinuous M f
  rw [Metric.uniformContinuous_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hf ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u v huv
  simpa [Completion.dist_eq] using H huv

/-- The unique uniformly continuous extension of `f^ℳ` to the metric completion
    (with the same modulus, by the fact recorded in the proof of Theorem 6.9). -/
def funcInterpHat {LM : MetricSignature} (M : MetricPreStructure LM) (f : LM.Func) :
    (Fin (LM.funcArity f) → Completion M.Carrier) → Completion M.Carrier :=
  (finPiCompletion (LM.funcArity f)).extend
    (fun v => (M.funcInterp f v : Completion M.Carrier))

/-- The unique uniformly continuous extension of `P^ℳ` to the metric completion. -/
def relInterpHat {LM : MetricSignature} (M : MetricPreStructure LM) (P : LM.Rel) :
    (Fin (LM.relArity P) → Completion M.Carrier) → ℝ :=
  (finPiCompletion (LM.relArity P)).extend (M.relInterp P)

lemma funcInterpHat_coe {LM : MetricSignature} (M : MetricPreStructure LM)
    (f : LM.Func) (v : Fin (LM.funcArity f) → M.Carrier) :
    funcInterpHat M f (piCoe (LM.funcArity f) v) =
      (M.funcInterp f v : Completion M.Carrier) := by
  exact AbstractCompletion.extend_coe (finPiCompletion (LM.funcArity f))
    (funcInterp_coe_uniformContinuous M f) v

lemma relInterpHat_coe {LM : MetricSignature} (M : MetricPreStructure LM)
    (P : LM.Rel) (v : Fin (LM.relArity P) → M.Carrier) :
    relInterpHat M P (piCoe (LM.relArity P) v) = M.relInterp P v := by
  exact AbstractCompletion.extend_coe (finPiCompletion (LM.relArity P))
    (relInterp_uniformContinuous M P) v

lemma continuous_funcInterpHat {LM : MetricSignature} (M : MetricPreStructure LM)
    (f : LM.Func) : Continuous (funcInterpHat M f) := by
  exact AbstractCompletion.continuous_extend (finPiCompletion (LM.funcArity f))

lemma continuous_relInterpHat {LM : MetricSignature} (M : MetricPreStructure LM)
    (P : LM.Rel) : Continuous (relInterpHat M P) := by
  exact AbstractCompletion.continuous_extend (finPiCompletion (LM.relArity P))

lemma relInterpHat_mem_Icc {LM : MetricSignature} (M : MetricPreStructure LM)
    (P : LM.Rel) (v : Fin (LM.relArity P) → Completion M.Carrier) :
    0 ≤ relInterpHat M P v ∧ relInterpHat M P v ≤ 1 := by
  have hp : IsClosed { w : Fin (LM.relArity P) → Completion M.Carrier |
      0 ≤ relInterpHat M P w ∧ relInterpHat M P w ≤ 1 } := by
    have hI : IsClosed (Set.Icc (0 : ℝ) 1) := isClosed_Icc
    exact hI.preimage (continuous_relInterpHat M P)
  have hdense := isClosed_property (denseRange_piCoe (LM.relArity P)) hp ?_
  · exact hdense v
  · intro a
    rw [relInterpHat_coe]
    exact M.rel_in_Icc P a

lemma replaceArg_piCoe {α : Type*} [PseudoMetricSpace α] {n : ℕ}
    (v : Fin n → α) (i : Fin n) (c : α) :
    piCoe n (replaceArg v i c) = replaceArg (piCoe n v) i (c : Completion α) := by
  ext j
  simp only [piCoe, replaceArg]
  split_ifs <;> rfl

lemma continuous_replaceArg {β : Type*} [TopologicalSpace β] {n : ℕ} (i : Fin n) :
    Continuous (fun p : (Fin n → β) × β => replaceArg p.1 i p.2) := by
  refine continuous_pi fun j => ?_
  simp only [replaceArg]
  by_cases hj : j = i
  · subst hj
    simpa using continuous_snd
  · simp [hj]
    exact (continuous_apply j).comp continuous_fst

/-- The distance relation, extended to the completion, agrees with the metric
    already present on `Completion`. -/
lemma relInterpHat_dist {LM : MetricSignature} (M : MetricPreStructure LM)
    (x y : Completion M.Carrier) :
    relInterpHat M LM.distSym
        (fun i =>
          let j : Fin 2 := Fin.cast LM.distArity i
          if j = 0 then x else y) =
      dist x y := by
  let pair : Completion M.Carrier → Completion M.Carrier →
      (Fin (LM.relArity LM.distSym) → Completion M.Carrier) :=
    fun x y i =>
      let j : Fin 2 := Fin.cast LM.distArity i
      if j = 0 then x else y
  have hcont : Continuous (fun p : Completion M.Carrier × Completion M.Carrier =>
      relInterpHat M LM.distSym (pair p.1 p.2) - dist p.1 p.2) := by
    have hp : Continuous (fun p : Completion M.Carrier × Completion M.Carrier =>
        pair p.1 p.2) :=
      continuous_pi fun i => by
        simp only [pair]
        by_cases hj : (Fin.cast LM.distArity i : Fin 2) = 0
        · simp [hj]; exact continuous_fst
        · simp [hj]; exact continuous_snd
    exact (continuous_relInterpHat M LM.distSym).comp hp |>.sub
      (Completion.continuous_dist continuous_fst continuous_snd)
  have hp : IsClosed { p : Completion M.Carrier × Completion M.Carrier |
      relInterpHat M LM.distSym (pair p.1 p.2) = dist p.1 p.2 } :=
    isClosed_eq
      ((continuous_relInterpHat M LM.distSym).comp (by
        refine continuous_pi fun i => ?_
        simp only [pair]
        by_cases hj : (Fin.cast LM.distArity i : Fin 2) = 0
        · simp [hj]; exact continuous_fst
        · simp [hj]; exact continuous_snd))
      (Completion.continuous_dist continuous_fst continuous_snd)
  have hdense := isClosed_property
      (Completion.denseRange_coe.prodMap (Completion.denseRange_coe (α := M.Carrier)))
      hp ?_
  · exact hdense (x, y)
  · rintro ⟨a, b⟩
    have hpair :
        pair (a : Completion M.Carrier) b =
          piCoe (LM.relArity LM.distSym)
            (fun i =>
              let j : Fin 2 := Fin.cast LM.distArity i
              if j = 0 then a else b) := by
      ext i
      simp only [pair, piCoe]
      split_ifs <;> rfl
    change relInterpHat M LM.distSym (pair (a : Completion M.Carrier) b) =
      dist (a : Completion M.Carrier) b
    rw [hpair, relInterpHat_coe, Completion.dist_eq, dist_eq_distVal]
    exact (M.distVal_eq a b).symm

/-- The same one-argument modulus of `f^ℳ` remains a modulus after extension,
    even when the remaining arguments lie in the completion (proof of Theorem 6.9). -/
lemma funcInterpHat_unif_cont {LM : MetricSignature} (M : MetricPreStructure LM)
    (f : LM.Func) (i : Fin (LM.funcArity f)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin (LM.funcArity f) → Completion M.Carrier)
    (c e : Completion M.Carrier)
    (hd : dist c e <
      LM.funcMod f i ε) :
    dist (funcInterpHat M f (replaceArg v i c))
      (funcInterpHat M f (replaceArg v i e)) ≤ ε := by
  set δ := LM.funcMod f i ε
  let p : (Fin (LM.funcArity f) → Completion M.Carrier) →
      Completion M.Carrier → Completion M.Carrier → Prop :=
    fun v c e => δ ≤ dist c e ∨
      dist (funcInterpHat M f (replaceArg v i c))
        (funcInterpHat M f (replaceArg v i e)) ≤ ε
  have hp : IsClosed { q : (Fin (LM.funcArity f) → Completion M.Carrier) ×
      Completion M.Carrier × Completion M.Carrier | p q.1 q.2.1 q.2.2 } := by
    have h1 : IsClosed { q : (Fin (LM.funcArity f) → Completion M.Carrier) ×
        Completion M.Carrier × Completion M.Carrier | δ ≤ dist q.2.1 q.2.2 } :=
      isClosed_le continuous_const
        (Completion.continuous_dist (continuous_fst.comp continuous_snd)
          (continuous_snd.comp continuous_snd))
    have hF : Continuous (fun q : (Fin (LM.funcArity f) → Completion M.Carrier) ×
        Completion M.Carrier × Completion M.Carrier =>
        dist (funcInterpHat M f (replaceArg q.1 i q.2.1))
          (funcInterpHat M f (replaceArg q.1 i q.2.2))) :=
      Completion.continuous_dist
        ((continuous_funcInterpHat M f).comp
          ((continuous_replaceArg i).comp (continuous_fst.prodMk
            (continuous_fst.comp continuous_snd))))
        ((continuous_funcInterpHat M f).comp
          ((continuous_replaceArg i).comp (continuous_fst.prodMk
            (continuous_snd.comp continuous_snd))))
    have h2 : IsClosed { q : (Fin (LM.funcArity f) → Completion M.Carrier) ×
        Completion M.Carrier × Completion M.Carrier |
        dist (funcInterpHat M f (replaceArg q.1 i q.2.1))
          (funcInterpHat M f (replaceArg q.1 i q.2.2)) ≤ ε } :=
      isClosed_le hF continuous_const
    exact h1.union h2
  have hmap :
      DenseRange (fun t : (Fin (LM.funcArity f) → M.Carrier) × M.Carrier × M.Carrier =>
        (piCoe (LM.funcArity f) t.1, ((t.2.1 : Completion M.Carrier),
          (t.2.2 : Completion M.Carrier)))) :=
    (denseRange_piCoe (LM.funcArity f)).prodMap
      (Completion.denseRange_coe.prodMap Completion.denseRange_coe)
  have hall := isClosed_property hmap hp ?_
  · have := hall (v, (c, e))
    exact this.resolve_left (not_le.mpr hd)
  · intro t
    change p (piCoe _ t.1) ↑t.2.1 ↑t.2.2
    by_cases hge : δ ≤ dist (t.2.1 : Completion M.Carrier) (t.2.2 : Completion M.Carrier)
    · exact Or.inl hge
    · refine Or.inr ?_
      have hd0 : M.distVal t.2.1 t.2.2 < δ := by
        have : dist (t.2.1 : Completion M.Carrier) t.2.2 < δ := lt_of_not_ge hge
        simpa [Completion.dist_eq, dist_eq_distVal] using this
      have hmod := M.func_unif_cont f i ε hε0 hε1 t.1 t.2.1 t.2.2 hd0
      rw [← replaceArg_piCoe, ← replaceArg_piCoe, funcInterpHat_coe, funcInterpHat_coe]
      simpa [Completion.dist_eq, dist_eq_distVal] using hmod

lemma relInterpHat_unif_cont {LM : MetricSignature} (M : MetricPreStructure LM)
    (P : LM.Rel) (i : Fin (LM.relArity P)) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (v : Fin (LM.relArity P) → Completion M.Carrier)
    (c e : Completion M.Carrier)
    (hd : dist c e <
      LM.relMod P i ε) :
    relInterpHat M P (replaceArg v i c) ∸ relInterpHat M P (replaceArg v i e) ≤ ε := by
  set δ := LM.relMod P i ε
  let p : (Fin (LM.relArity P) → Completion M.Carrier) →
      Completion M.Carrier → Completion M.Carrier → Prop :=
    fun v c e => δ ≤ dist c e ∨
      relInterpHat M P (replaceArg v i c) ∸ relInterpHat M P (replaceArg v i e) ≤ ε
  have hp : IsClosed { q : (Fin (LM.relArity P) → Completion M.Carrier) ×
      Completion M.Carrier × Completion M.Carrier | p q.1 q.2.1 q.2.2 } := by
    have h1 : IsClosed { q : (Fin (LM.relArity P) → Completion M.Carrier) ×
        Completion M.Carrier × Completion M.Carrier | δ ≤ dist q.2.1 q.2.2 } :=
      isClosed_le continuous_const
        (Completion.continuous_dist (continuous_fst.comp continuous_snd)
          (continuous_snd.comp continuous_snd))
    have hc : Continuous (fun q : (Fin (LM.relArity P) → Completion M.Carrier) ×
        Completion M.Carrier × Completion M.Carrier =>
        relInterpHat M P (replaceArg q.1 i q.2.1)) :=
      (continuous_relInterpHat M P).comp
        ((continuous_replaceArg i).comp (continuous_fst.prodMk
          (continuous_fst.comp continuous_snd)))
    have he : Continuous (fun q : (Fin (LM.relArity P) → Completion M.Carrier) ×
        Completion M.Carrier × Completion M.Carrier =>
        relInterpHat M P (replaceArg q.1 i q.2.2)) :=
      (continuous_relInterpHat M P).comp
        ((continuous_replaceArg i).comp (continuous_fst.prodMk
          (continuous_snd.comp continuous_snd)))
    have hF : Continuous (fun q : (Fin (LM.relArity P) → Completion M.Carrier) ×
        Completion M.Carrier × Completion M.Carrier =>
        relInterpHat M P (replaceArg q.1 i q.2.1) ∸
          relInterpHat M P (replaceArg q.1 i q.2.2)) :=
      (hc.sub he).max continuous_const
    have h2 : IsClosed { q : (Fin (LM.relArity P) → Completion M.Carrier) ×
        Completion M.Carrier × Completion M.Carrier |
        relInterpHat M P (replaceArg q.1 i q.2.1) ∸
          relInterpHat M P (replaceArg q.1 i q.2.2) ≤ ε } :=
      isClosed_le hF continuous_const
    exact h1.union h2
  have hmap :
      DenseRange (fun t : (Fin (LM.relArity P) → M.Carrier) × M.Carrier × M.Carrier =>
        (piCoe (LM.relArity P) t.1, ((t.2.1 : Completion M.Carrier),
          (t.2.2 : Completion M.Carrier)))) :=
    (denseRange_piCoe (LM.relArity P)).prodMap
      (Completion.denseRange_coe.prodMap Completion.denseRange_coe)
  have hall := isClosed_property hmap hp ?_
  · have := hall (v, (c, e))
    exact this.resolve_left (not_le.mpr hd)
  · intro t
    change p (piCoe _ t.1) ↑t.2.1 ↑t.2.2
    by_cases hge : δ ≤ dist (t.2.1 : Completion M.Carrier) (t.2.2 : Completion M.Carrier)
    · exact Or.inl hge
    · refine Or.inr ?_
      have hd0 : M.distVal t.2.1 t.2.2 < δ := by
        have : dist (t.2.1 : Completion M.Carrier) t.2.2 < δ := lt_of_not_ge hge
        simpa [Completion.dist_eq, dist_eq_distVal] using this
      have hmod := M.rel_unif_cont P i ε hε0 hε1 t.1 t.2.1 t.2.2 hd0
      rw [← replaceArg_piCoe, ← replaceArg_piCoe, relInterpHat_coe, relInterpHat_coe]
      exact hmod

lemma bddAbove_closure {s : Set ℝ} (hbdd : BddAbove s) : BddAbove (closure s) :=
  ⟨sSup s, fun _ hx =>
    (isClosed_Iic.closure_subset_iff.mpr fun _ hy => le_csSup hbdd hy) hx⟩

lemma csSup_closure_eq {s : Set ℝ} (hne : s.Nonempty) (hbdd : BddAbove s) :
    sSup (closure s) = sSup s := by
  apply le_antisymm
  · apply csSup_le (hne.mono subset_closure)
    intro x hx
    have : closure s ⊆ Set.Iic (sSup s) :=
      isClosed_Iic.closure_subset_iff.mpr fun y hy => le_csSup hbdd hy
    exact this hx
  · exact csSup_le_csSup (bddAbove_closure hbdd) hne subset_closure

lemma sSup_image_eq_of_continuous_dense {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} (hf : Continuous f) {s : Set X} (hs : Dense s) (hne : s.Nonempty)
    (hbdd : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) :
    sSup (f '' s) = sSup (Set.range f) := by
  have hX : Nonempty X := ⟨hne.some⟩
  have hne' : (f '' s).Nonempty := hne.image f
  have hbdds : BddAbove (f '' s) := ⟨1, by rintro _ ⟨x, _, rfl⟩; exact (hbdd x).2⟩
  have hbddr : BddAbove (Set.range f) := ⟨1, by rintro _ ⟨x, rfl⟩; exact (hbdd x).2⟩
  have hsub : f '' s ⊆ Set.range f := Set.image_subset_range _ _
  have hcls : Set.range f ⊆ closure (f '' s) :=
    hf.range_subset_closure_image_dense hs
  apply le_antisymm
  · exact csSup_le_csSup hbddr hne' hsub
  · have : sSup (Set.range f) ≤ sSup (closure (f '' s)) :=
      csSup_le_csSup (bddAbove_closure hbdds) (Set.range_nonempty (h := hX) f) hcls
    exact this.trans_eq (csSup_closure_eq hne' hbdds)

/-- The metric completion of a continuous pre-structure, as a complete continuous
    `𝓛`-structure (Theorem 6.9). The signature, including its moduli of uniform
    continuity, is unchanged. -/
def metricCompletion.{u} {LM : MetricSignature} (M : MetricPreStructure.{u} LM) :
    ContinuousStructure.{u} LM where
  Carrier := Completion M.Carrier
  nonempty := (Completion.nonempty_completion_iff (α := M.Carrier)).mpr M.nonempty
  funcInterp := funcInterpHat M
  relInterp := relInterpHat M
  rel_in_Icc := relInterpHat_mem_Icc M
  distVal := fun x y => dist x y
  distVal_eq := fun x y => (relInterpHat_dist M x y).symm
  dist_self := fun a => dist_self a
  dist_symm := fun a b => dist_comm a b
  dist_triangle := fun a b c => dist_triangle a b c
  func_unif_cont := funcInterpHat_unif_cont M
  rel_unif_cont := relInterpHat_unif_cont M
  metricSpace := inferInstance
  dist_eq := fun _ _ => rfl
  completeSpace := inferInstance

/-- Inclusion of the original carrier into the packed completion. This is
    definitionally `Completion.coe`, but is typed as a map into
    `(metricCompletion M).Carrier` so later lemmas do not depend on unfolding
    the `Carrier` field (which is not reducible). -/
def toCompletion.{u} {LM : MetricSignature} (M : MetricPreStructure.{u} LM)
    (a : M.Carrier) : (metricCompletion M).Carrier :=
  (a : Completion M.Carrier)

lemma denseRange_toCompletion {LM : MetricSignature} (M : MetricPreStructure LM) :
    DenseRange (toCompletion M) := by
  intro x
  let x' : Completion M.Carrier := x
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨y, ⟨a, rfl⟩, hay⟩ :=
    (Metric.mem_closure_iff.mp
      (Completion.denseRange_coe (α := M.Carrier) x')) ε hε
  refine ⟨toCompletion M a, ⟨a, rfl⟩, ?_⟩
  -- `hay` is `dist x' ↑a < ε`; the packed distance agrees definitionally.
  exact hay

/-- The inclusion of a pre-structure into its metric completion is an `𝓛`-morphism
    (and an isometry, as every `𝓛`-morphism of metric signatures is). -/
def metricCompletionMorphism.{u} {LM : MetricSignature} (M : MetricPreStructure.{u} LM) :
    LMorphism M.toPreStructure (metricCompletion M).toPreStructure where
  toFun := toCompletion M
  map_func := fun f args => (funcInterpHat_coe M f args).symm
  map_rel := fun P args => (relInterpHat_coe M P args).symm

lemma updateAssign_toCompletion {LM : MetricSignature} (M : MetricPreStructure LM)
    (σ : Var → M.Carrier) (x : Var) (a : M.Carrier) :
    updateAssign (toCompletion M ∘ σ) x (toCompletion M a) =
      toCompletion M ∘ updateAssign σ x a := by
  funext y
  by_cases hxy : x = y
  · subst hxy
    simp [updateAssign]
  · simp [updateAssign, hxy]

lemma metricCompletion_distVal_eq_dist {LM : MetricSignature}
    (M : MetricPreStructure LM) (x y : (metricCompletion M).Carrier) :
    (metricCompletion M).distVal x y = dist x y := rfl

lemma metricCompletion_eval_update_continuous {LM : MetricSignature}
    (M : MetricPreStructure LM) (σ : Var → M.Carrier) (x : Var)
    (α : Formula LM.toSignature) :
    Continuous fun b : (metricCompletion M).Carrier =>
      α.eval (metricCompletion M).toPreStructure
        (updateAssign (toCompletion M ∘ σ) x b) := by
  have hUC : UniformContinuous fun b : (metricCompletion M).Carrier =>
      α.eval (metricCompletion M).toPreStructure
        (updateAssign (toCompletion M ∘ σ) x b) := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    have hε2 : 0 < ε / 2 := half_pos hε
    obtain ⟨δ, hδ, H⟩ :=
      formula_eval_unif_cont (metricCompletion M).toMetricPreStructure α (ε / 2) hε2
    refine ⟨δ, hδ, ?_⟩
    intro b b' hbb
    have hassign : ∀ v ∈ α.freeVars,
        (metricCompletion M).distVal
          (updateAssign (toCompletion M ∘ σ) x b v)
          (updateAssign (toCompletion M ∘ σ) x b' v) < δ := by
      intro v _hv
      by_cases hvx : x = v
      · subst hvx
        rw [updateAssign_same, updateAssign_same, metricCompletion_distVal_eq_dist]
        exact hbb
      · rw [updateAssign_ne (σ := toCompletion M ∘ σ) hvx,
            updateAssign_ne (σ := toCompletion M ∘ σ) hvx,
            metricCompletion_distVal_eq_dist, dist_self]
        exact hδ
    have := H (updateAssign (toCompletion M ∘ σ) x b)
      (updateAssign (toCompletion M ∘ σ) x b') hassign
    exact this.trans_lt (half_lt_self hε)
  exact hUC.continuous

/-- The inclusion of a pre-structure into its metric completion is elementary
    (Theorem 6.9), using Theorem 6.8 for the quantifier step and density of the
    image. -/
def metricCompletionElementary.{u} {LM : MetricSignature} (M : MetricPreStructure.{u} LM) :
    ElementaryLMorphism M.toPreStructure (metricCompletion M).toPreStructure where
  toLMorphism := metricCompletionMorphism M
  map_eval := by
    intro σ φ
    induction φ generalizing σ with
    | rel P args =>
      simp only [Formula.eval, (metricCompletionMorphism M).map_rel]
      congr 1
      ext i
      exact (metricCompletionMorphism M).map_term σ (args i)
    | tsub α β ihα ihβ =>
      simp [Formula.eval, ihα σ, ihβ σ]
    | neg α ih =>
      simp [Formula.eval, ih σ]
    | half α ih =>
      simp [Formula.eval, ih σ]
    | sup x α ih =>
      simp only [Formula.eval]
      let g : (metricCompletion M).Carrier → ℝ :=
        fun b => α.eval (metricCompletion M).toPreStructure
          (updateAssign (toCompletion M ∘ σ) x b)
      have hg_coe : ∀ (a : M.Carrier), g (toCompletion M a) =
          α.eval M.toPreStructure (updateAssign σ x a) := by
        intro a
        dsimp only [g]
        rw [updateAssign_toCompletion M σ x a]
        have hfun : (metricCompletionMorphism M).toFun = toCompletion M := rfl
        rw [← hfun, ← ih (updateAssign σ x a)]
      have hL :
          sSup (Set.range fun a : M.Carrier =>
              α.eval M.toPreStructure (updateAssign σ x a)) =
            sSup (g '' Set.range (toCompletion M)) := by
        refine congrArg sSup ?_
        ext r
        constructor
        · rintro ⟨a, rfl⟩
          exact ⟨toCompletion M a, ⟨a, rfl⟩, hg_coe a⟩
        · rintro ⟨b, ⟨a, rfl⟩, rfl⟩
          exact ⟨a, (hg_coe a).symm⟩
      have hto : (metricCompletionMorphism M).toFun ∘ σ = toCompletion M ∘ σ := rfl
      rw [hL, hto]
      have hneM : Nonempty M.Carrier := M.nonempty
      exact sSup_image_eq_of_continuous_dense
        (metricCompletion_eval_update_continuous M σ x α)
        (denseRange_toCompletion M)
        (Set.range_nonempty (h := hneM) _)
        (fun b => Formula.eval_in_Icc (metricCompletion M).toPreStructure _ _)

end ContinuousFOL
