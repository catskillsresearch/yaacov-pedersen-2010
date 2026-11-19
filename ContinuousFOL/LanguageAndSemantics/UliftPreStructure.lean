/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: helper for universe transport of pre-structures (Definition 5.6 / 5.9)
-/
module

public import ContinuousFOL.LanguageAndSemantics.ContinuousStructure
public import ContinuousFOL.LanguageAndSemantics.TermEval
public import ContinuousFOL.LanguageAndSemantics.FormulaEval
public import ContinuousFOL.LanguageAndSemantics.UpdateAssign
public import ContinuousFOL.LanguageAndSemantics.ReplaceArg
public import ContinuousFOL.LanguageAndSemantics.ModelsPre
public import ContinuousFOL.LanguageAndSemantics.EntailsPre
public import ContinuousFOL.LanguageAndSemantics.CompletelySatisfiable
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Lift a universe-0 pre-structure to universe `u` by wrapping the carrier in `ULift`.
    This is an elementary isomorphism, so evaluation of terms and formulas is preserved. -/
def PreStructure.ulift.{u} {L : Signature} (M : PreStructure.{0} L) : PreStructure.{u} L where
  Carrier := ULift.{u, 0} M.Carrier
  nonempty := M.nonempty.map ULift.up
  funcInterp f args := ULift.up (M.funcInterp f (fun i => (args i).down))
  relInterp P args := M.relInterp P (fun i => (args i).down)
  rel_in_Icc P args := M.rel_in_Icc P (fun i => (args i).down)

/-- The inclusion of a universe-0 carrier into its `ULift` in universe `u`. -/
def uliftUp.{u} {L : Signature} (M : PreStructure.{0} L) :
    M.Carrier → (PreStructure.ulift.{u} M).Carrier :=
  ULift.up

/-- The projection of a lifted carrier back to universe 0. -/
def uliftDown.{u} {L : Signature} (M : PreStructure.{0} L) :
    (PreStructure.ulift.{u} M).Carrier → M.Carrier :=
  ULift.down

@[simp] lemma uliftDown_up.{u} {L : Signature} (M : PreStructure.{0} L) (a : M.Carrier) :
    uliftDown.{u} M (uliftUp.{u} M a) = a :=
  rfl

@[simp] lemma uliftUp_down.{u} {L : Signature} (M : PreStructure.{0} L)
    (a : (PreStructure.ulift.{u} M).Carrier) :
    uliftUp.{u} M (uliftDown.{u} M a) = a :=
  rfl

lemma uliftDown_injective.{u} {L : Signature} (M : PreStructure.{0} L) :
    Function.Injective (uliftDown.{u} M) :=
  ULift.down_injective

lemma updateAssign_uliftUp.{u} {L : Signature} (M : PreStructure.{0} L)
    (σ : Var → M.Carrier) (x : Var) (a : M.Carrier) :
    updateAssign (uliftUp.{u} M ∘ σ) x (uliftUp.{u} M a) =
      uliftUp.{u} M ∘ updateAssign σ x a := by
  ext y
  by_cases h : x = y <;> simp [updateAssign, h]

lemma funcInterp_ulift.{u} {L : Signature} (M : PreStructure.{0} L)
    (f : L.Func) (args : Fin (L.funcArity f) → (PreStructure.ulift.{u} M).Carrier) :
    uliftDown.{u} M ((PreStructure.ulift.{u} M).funcInterp f args) =
      M.funcInterp f (fun i => uliftDown.{u} M (args i)) :=
  ULift.down_up _

lemma relInterp_ulift.{u} {L : Signature} (M : PreStructure.{0} L)
    (P : L.Rel) (args : Fin (L.relArity P) → (PreStructure.ulift.{u} M).Carrier) :
    (PreStructure.ulift.{u} M).relInterp P args =
      M.relInterp P (fun i => uliftDown.{u} M (args i)) :=
  rfl

lemma Term.eval_ulift.{u} {L : Signature} (M : PreStructure.{0} L)
    (σ : Var → M.Carrier) (t : Term L) :
    t.eval (PreStructure.ulift.{u} M) (uliftUp.{u} M ∘ σ) =
      uliftUp.{u} M (t.eval M σ) := by
  induction t with
  | var x => rfl
  | func f args ih =>
    change uliftUp.{u} M
        (M.funcInterp f (fun i =>
          uliftDown.{u} M ((args i).eval (PreStructure.ulift.{u} M) (uliftUp.{u} M ∘ σ)))) =
      uliftUp.{u} M (M.funcInterp f (fun i => (args i).eval M σ))
    refine congrArg (uliftUp.{u} M) ?_
    refine congrArg (M.funcInterp f) ?_
    ext i
    simp [ih i]

lemma Formula.eval_ulift.{u} {L : Signature} (M : PreStructure.{0} L)
    (σ : Var → M.Carrier) (φ : Formula L) :
    φ.eval (PreStructure.ulift.{u} M) (uliftUp.{u} M ∘ σ) = φ.eval M σ := by
  induction φ generalizing σ with
  | rel P args =>
    change M.relInterp P (fun i =>
        uliftDown.{u} M ((args i).eval (PreStructure.ulift.{u} M) (uliftUp.{u} M ∘ σ))) =
      M.relInterp P (fun i => (args i).eval M σ)
    refine congrArg (M.relInterp P) ?_
    ext i
    simp [Term.eval_ulift]
  | tsub α β ihα ihβ => simp [Formula.eval, ihα, ihβ]
  | neg α ih => simp [Formula.eval, ih]
  | half α ih => simp [Formula.eval, ih]
  | sup x α ih =>
    change sSup (Set.range (fun a : (PreStructure.ulift.{u} M).Carrier =>
        α.eval (PreStructure.ulift.{u} M) (updateAssign (uliftUp.{u} M ∘ σ) x a))) =
      sSup (Set.range (fun a : M.Carrier => α.eval M (updateAssign σ x a)))
    congr 1
    ext r
    simp only [Set.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨uliftDown.{u} M a, ?_⟩
      have hτ : updateAssign (uliftUp.{u} M ∘ σ) x a =
          uliftUp.{u} M ∘ updateAssign σ x (uliftDown.{u} M a) := by
        rw [← updateAssign_uliftUp, uliftUp_down]
      rw [hτ, ih]
    · rintro ⟨a, rfl⟩
      refine ⟨uliftUp.{u} M a, ?_⟩
      rw [updateAssign_uliftUp, ih]

lemma Formula.eval_ulift_down.{u} {L : Signature} (M : PreStructure.{0} L)
    (τ : Var → (PreStructure.ulift.{u} M).Carrier) (φ : Formula L) :
    φ.eval (PreStructure.ulift.{u} M) τ = φ.eval M (uliftDown.{u} M ∘ τ) := by
  have hτ : τ = uliftUp.{u} M ∘ (uliftDown.{u} M ∘ τ) := by
    ext x
    exact (uliftUp_down.{u} M (τ x)).symm
  rw [hτ, Formula.eval_ulift]
  have hcomp : uliftDown.{u} M ∘ uliftUp.{u} M ∘ uliftDown.{u} M ∘ τ =
      uliftDown.{u} M ∘ τ := by
    ext x
    simp
  rw [hcomp]

lemma ModelsPre.ulift_iff.{u} {L : Signature} {M : PreStructure.{0} L}
    {σ : Var → M.Carrier} {Γ : Set (Formula L)} :
    ModelsPre (PreStructure.ulift.{u} M) (uliftUp.{u} M ∘ σ) Γ ↔ ModelsPre M σ Γ := by
  constructor
  · intro h φ hφ
    rw [← Formula.eval_ulift M σ φ]
    exact h φ hφ
  · intro h φ hφ
    rw [Formula.eval_ulift]
    exact h φ hφ

lemma SatisfiablePre.of_universe0.{u} {L : Signature} {Γ : Set (Formula L)}
    (h : SatisfiablePre.{0} Γ) : SatisfiablePre.{u} Γ := by
  obtain ⟨M, σ, hM⟩ := h
  exact ⟨PreStructure.ulift.{u} M, uliftUp.{u} M ∘ σ, (ModelsPre.ulift_iff).mpr hM⟩

lemma replaceArg_uliftDown.{u} {L : Signature} (M : PreStructure.{0} L) {n : ℕ}
    (v : Fin n → (PreStructure.ulift.{u} M).Carrier) (i : Fin n)
    (c : (PreStructure.ulift.{u} M).Carrier) :
    (fun j => uliftDown.{u} M (replaceArg v i c j)) =
      replaceArg (fun j => uliftDown.{u} M (v j)) i (uliftDown.{u} M c) := by
  ext j
  by_cases h : j = i <;> simp [replaceArg, h]

/-- Lift a universe-0 metric pre-structure to universe `u`. -/
def MetricPreStructure.ulift.{u} {LM : MetricSignature} (M : MetricPreStructure.{0} LM) :
    MetricPreStructure.{u} LM where
  toPreStructure := PreStructure.ulift.{u} M.toPreStructure
  distVal x y := M.distVal (uliftDown.{u} M.toPreStructure x) (uliftDown.{u} M.toPreStructure y)
  distVal_eq x y := by
    rw [M.distVal_eq]
    change M.relInterp LM.distSym
        (fun i =>
          let j : Fin 2 := Fin.cast LM.distArity i
          if j = 0 then uliftDown.{u} M.toPreStructure x
          else uliftDown.{u} M.toPreStructure y) =
      M.relInterp LM.distSym
        (fun i => uliftDown.{u} M.toPreStructure
          (let j : Fin 2 := Fin.cast LM.distArity i
          if j = 0 then x else y))
    congr 1
    funext i
    by_cases h : Fin.cast LM.distArity i = 0 <;> simp [h]
  dist_self a := M.dist_self (uliftDown.{u} M.toPreStructure a)
  dist_symm a b :=
    M.dist_symm (uliftDown.{u} M.toPreStructure a) (uliftDown.{u} M.toPreStructure b)
  dist_triangle a b c :=
    M.dist_triangle (uliftDown.{u} M.toPreStructure a) (uliftDown.{u} M.toPreStructure b)
      (uliftDown.{u} M.toPreStructure c)
  func_unif_cont f i ε hε hε1 v c e hdist := by
    have h := M.func_unif_cont f i ε hε hε1
      (fun j => uliftDown.{u} M.toPreStructure (v j))
      (uliftDown.{u} M.toPreStructure c) (uliftDown.{u} M.toPreStructure e)
      (by simpa [MetricPreStructure.distVal] using hdist)
    have hfun :
        uliftDown.{u} M.toPreStructure
            ((PreStructure.ulift.{u} M.toPreStructure).funcInterp f (replaceArg v i c)) =
          M.funcInterp f (replaceArg (fun j => uliftDown.{u} M.toPreStructure (v j)) i
            (uliftDown.{u} M.toPreStructure c)) := by
      rw [funcInterp_ulift, replaceArg_uliftDown]
    have hfun' :
        uliftDown.{u} M.toPreStructure
            ((PreStructure.ulift.{u} M.toPreStructure).funcInterp f (replaceArg v i e)) =
          M.funcInterp f (replaceArg (fun j => uliftDown.{u} M.toPreStructure (v j)) i
            (uliftDown.{u} M.toPreStructure e)) := by
      rw [funcInterp_ulift, replaceArg_uliftDown]
    simpa [MetricPreStructure.distVal, hfun, hfun'] using h
  rel_unif_cont P i ε hε hε1 v c e hdist := by
    have h := M.rel_unif_cont P i ε hε hε1
      (fun j => uliftDown.{u} M.toPreStructure (v j))
      (uliftDown.{u} M.toPreStructure c) (uliftDown.{u} M.toPreStructure e)
      (by simpa [MetricPreStructure.distVal] using hdist)
    simpa [relInterp_ulift, replaceArg_uliftDown] using h

lemma MetricPreStructure.toPreStructure_ulift.{u} {LM : MetricSignature}
    (M : MetricPreStructure.{0} LM) :
    (MetricPreStructure.ulift.{u} M).toPreStructure =
      PreStructure.ulift.{u} M.toPreStructure :=
  rfl

lemma SatisfiableMetricPre.of_universe0.{u} {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (h : SatisfiableMetricPre.{0} Γ) :
    SatisfiableMetricPre.{u} Γ := by
  obtain ⟨M, σ, hM⟩ := h
  refine ⟨MetricPreStructure.ulift.{u} M, uliftUp.{u} M.toPreStructure ∘ σ, ?_⟩
  exact (ModelsPre.ulift_iff (M := M.toPreStructure) (σ := σ)).mpr hM

/-- Lift a universe-0 complete continuous structure to universe `u`. -/
def ContinuousStructure.ulift.{u} {LM : MetricSignature} (M : ContinuousStructure.{0} LM) :
    ContinuousStructure.{u} LM := by
  letI instMet : MetricSpace M.Carrier := M.metricSpace
  letI instComp : CompleteSpace M.Carrier := M.completeSpace
  refine
    { toMetricPreStructure := MetricPreStructure.ulift.{u} M.toMetricPreStructure
      metricSpace := ?met
      dist_eq := ?deq
      completeSpace := ?cmp }
  · change MetricSpace (ULift.{u, 0} M.Carrier)
    infer_instance
  · intro a b
    change Dist.dist (α := ULift.{u, 0} M.Carrier) a b =
      M.distVal (ULift.down a) (ULift.down b)
    have hinst : Dist.dist (α := ULift.{u, 0} M.Carrier) a b =
        Dist.dist (α := M.Carrier) (ULift.down a) (ULift.down b) := rfl
    rw [hinst]
    exact M.dist_eq (ULift.down a) (ULift.down b)
  · change CompleteSpace (ULift.{u, 0} M.Carrier)
    exact (completeSpace_ulift_iff (α := M.Carrier)).2 instComp

lemma ContinuousStructure.toPreStructure_ulift.{u} {LM : MetricSignature}
    (M : ContinuousStructure.{0} LM) :
    (ContinuousStructure.ulift.{u} M).toPreStructure =
      PreStructure.ulift.{u} M.toPreStructure :=
  rfl

lemma CompletelySatisfiable.of_universe0.{u} {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (h : CompletelySatisfiable.{0} Γ) :
    CompletelySatisfiable.{u} Γ := by
  obtain ⟨M, σ, hM⟩ := h
  refine ⟨ContinuousStructure.ulift.{u} M, uliftUp.{u} M.toPreStructure ∘ σ, ?_⟩
  exact (ModelsPre.ulift_iff (M := M.toPreStructure) (σ := σ)).mpr hM

lemma ContinuousStructure.eval_ulift.{u} {LM : MetricSignature}
    (M : ContinuousStructure.{0} LM) (σ : Var → M.Carrier)
    (φ : Formula LM.toSignature) :
    φ.eval (ContinuousStructure.ulift.{u} M).toPreStructure
      (uliftUp.{u} M.toPreStructure ∘ σ) =
    φ.eval M.toPreStructure σ :=
  Formula.eval_ulift.{u} M.toPreStructure σ φ

end ContinuousFOL
