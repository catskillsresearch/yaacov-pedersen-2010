/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §2 Definition 2.1 evaluation
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukPropForm
public import ContinuousFOL.Introduction.UnitInterval

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

def eval {I : Type*} (v₀ : I → ℝ) : LukPropForm I → ℝ
  | .var i    => v₀ i
  | .tsub φ ψ => eval v₀ φ ∸ eval v₀ ψ
  | .neg φ    => 1 - eval v₀ φ

lemma eval_mem_Icc {I : Type*} (v₀ : I → ℝ)
    (hv : ∀ i, 0 ≤ v₀ i ∧ v₀ i ≤ 1) (φ : LukPropForm I) :
    0 ≤ eval v₀ φ ∧ eval v₀ φ ≤ 1 := by
  induction φ with
  | var i =>
    exact hv i
  | tsub φ ψ ihφ ihψ =>
    exact tsubR.unitClosed ihφ.1 ihφ.2 ihψ.1
  | neg φ ih =>
    exact unit_closed_neg ih.1 ih.2

end LukPropForm

end ContinuousFOL
