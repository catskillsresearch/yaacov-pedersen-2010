/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Theorem 6.9 (metric completions of finite products);
  vision.md page 13
-/
module

public import Mathlib.Topology.MetricSpace.Completion
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Topology.UniformSpace.AbstractCompletion
public import Mathlib.Topology.NhdsWithin

@[expose] public section

noncomputable section
open Classical
open scoped Uniformity
open UniformSpace

namespace ContinuousFOL

variable {α : Type*} [PseudoMetricSpace α]

/-- Componentwise inclusion of an `n`-tuple into the completions of its
    coordinates. For finite `n` this realises the completion of the product. -/
def piCoe (n : ℕ) : (Fin n → α) → (Fin n → Completion α) :=
  fun v i => (v i : Completion α)

lemma piCoe_eq_piMap (n : ℕ) :
    piCoe (α := α) n = Pi.map (fun _ : Fin n => fun a : α => (a : Completion α)) :=
  rfl

lemma nndist_piCoe (n : ℕ) (v w : Fin n → α) (i : Fin n) :
    nndist (piCoe n v i) (piCoe n w i) = nndist (v i) (w i) := by
  ext
  exact Completion.dist_eq (v i) (w i)

lemma isometry_piCoe (n : ℕ) : Isometry (piCoe (α := α) n) := by
  refine Isometry.of_dist_eq fun v w => ?_
  have h : (fun b => nndist (piCoe (α := α) n v b) (piCoe (α := α) n w b)) =
      fun b => nndist (v b) (w b) :=
    funext fun b => nndist_piCoe n v w b
  simp [dist_pi_def, h]

lemma denseRange_piCoe (n : ℕ) : DenseRange (piCoe (α := α) n) := by
  simpa [piCoe_eq_piMap] using
    DenseRange.piMap (fun _ : Fin n => Completion.denseRange_coe (α := α))

/-- The product of `n` copies of `Completion α` is an abstract completion of
    `Fin n → α`, with the componentwise inclusion. -/
def finPiCompletion (n : ℕ) : AbstractCompletion (Fin n → α) where
  space := Fin n → Completion α
  coe := piCoe n
  uniformStruct := inferInstance
  complete := inferInstance
  separation := inferInstance
  isUniformInducing := (isometry_piCoe n).isUniformInducing
  dense := denseRange_piCoe n

lemma finPiCompletion_coe (n : ℕ) (v : Fin n → α) :
    (finPiCompletion (α := α) n).coe v = piCoe n v :=
  rfl

end ContinuousFOL
