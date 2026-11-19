/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Definition 6.10; vision.md page 13
-/
module

public import ContinuousFOL.LanguageAndSemantics.ModelsPre
public import ContinuousFOL.LanguageAndSemantics.ContinuousStructure

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Complete satisfiability and entailment `Γ ⊨_{QC} φ` (Definition 6.10). -/
def CompletelySatisfiable {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) : Prop :=
  ∃ (M : ContinuousStructure LM) (σ : Var → M.Carrier), ModelsPre M.toPreStructure σ Γ

def EntailsComplete {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : Prop :=
  ∀ (M : ContinuousStructure LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ → φ.eval M.toPreStructure σ = 0

end ContinuousFOL
