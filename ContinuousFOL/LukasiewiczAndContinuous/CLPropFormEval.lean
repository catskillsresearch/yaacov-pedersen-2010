/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §2 Definition 2.4 evaluation
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.CLPropForm
public import ContinuousFOL.Introduction.UnitInterval

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace CLPropForm

def eval {I : Type*} (v₀ : I → ℝ) : CLPropForm I → ℝ
  | .var i    => v₀ i
  | .tsub φ ψ => eval v₀ φ ∸ eval v₀ ψ
  | .neg φ    => 1 - eval v₀ φ
  | .half φ   => eval v₀ φ / 2

lemma eval_mem_Icc {I : Type*} (v₀ : I → ℝ)
    (hv : ∀ i, 0 ≤ v₀ i ∧ v₀ i ≤ 1) (φ : CLPropForm I) :
    0 ≤ eval v₀ φ ∧ eval v₀ φ ≤ 1 := by
  induction φ with
  | var i =>
    exact hv i
  | tsub φ ψ ihφ ihψ =>
    exact tsubR.unitClosed ihφ.1 ihφ.2 ihψ.1
  | neg φ ih =>
    exact unit_closed_neg ih.1 ih.2
  | half φ ih =>
    exact unit_closed_half ih.1 ih.2

end CLPropForm

end ContinuousFOL
