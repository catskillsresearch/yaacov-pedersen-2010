/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.12; vision.md page 10
-/
module

public import ContinuousFOL.LanguageAndSemantics.FormulaEval
public import ContinuousFOL.LanguageAndSemantics.MetricPreStructure
public import Mathlib.Data.Set.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Satisfaction `(𝔐, σ) ⊨_Q Γ` (Definition 5.12). -/
def ModelsPre {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (Γ : Set (Formula L)) : Prop :=
  ∀ φ ∈ Γ, φ.eval M σ = 0

def SatisfiablePre.{u} {L : Signature} (Γ : Set (Formula L)) : Prop :=
  ∃ (M : PreStructure.{u} L) (σ : Var → M.Carrier), ModelsPre M σ Γ

def SatisfiableMetricPre.{u} {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) : Prop :=
  ∃ (M : MetricPreStructure.{u} LM) (σ : Var → M.Carrier), ModelsPre M.toPreStructure σ Γ

end ContinuousFOL
