/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.14; vision.md page 10
-/
module

public import ContinuousFOL.LanguageAndSemantics.FormulaEval
public import ContinuousFOL.LanguageAndSemantics.MetricPreStructure

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Logical equivalence `φ ≡ ψ` (Definition 5.14). -/
def FormulaEquiv.{u} {L : Signature} (φ ψ : Formula L) : Prop :=
  ∀ (M : PreStructure.{u} L) (σ : Var → M.Carrier), φ.eval M σ = ψ.eval M σ

infix:50 " ≡ᶠ " => FormulaEquiv

/-- Logical equivalence `φ ≡ ψ` when `𝓛` is a continuous signature with a metric
    (Definition 5.14): equality of values in every continuous `𝓛`-pre-structure,
    i.e. every `MetricPreStructure`. -/
def FormulaEquivMetric.{u} {LM : MetricSignature} (φ ψ : Formula LM.toSignature) : Prop :=
  ∀ (M : MetricPreStructure.{u} LM) (σ : Var → M.Carrier),
    φ.eval M.toPreStructure σ = ψ.eval M.toPreStructure σ

infix:50 " ≡ᵐ " => FormulaEquivMetric

/-- Ordinary `≡ᶠ` (quantifying over all pre-structures) implies metric `≡`. -/
lemma FormulaEquiv.toMetric.{u} {LM : MetricSignature}
    {φ ψ : Formula LM.toSignature} (h : FormulaEquiv.{u} φ ψ) :
    FormulaEquivMetric.{u} φ ψ :=
  fun M σ => h M.toPreStructure σ

end ContinuousFOL
