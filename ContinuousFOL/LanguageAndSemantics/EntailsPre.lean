/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.13; vision.md page 10
-/
module

public import ContinuousFOL.LanguageAndSemantics.ModelsPre

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Logical entailment `Γ ⊨_Q φ` over pre-structures (Definition 5.13). -/
def EntailsPre.{u} {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) : Prop :=
  ∀ (M : PreStructure.{u} L) (σ : Var → M.Carrier), ModelsPre M σ Γ → φ.eval M σ = 0

def EntailsMetricPre.{u} {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : Prop :=
  ∀ (M : MetricPreStructure.{u} LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ → φ.eval M.toPreStructure σ = 0

end ContinuousFOL
