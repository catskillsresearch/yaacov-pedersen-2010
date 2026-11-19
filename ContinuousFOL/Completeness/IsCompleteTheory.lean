/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.9 complete theories
-/
module

public import ContinuousFOL.Completeness.IsTheory
public import ContinuousFOL.LanguageAndSemantics.ContinuousStructure
public import ContinuousFOL.LanguageAndSemantics.ModelsPre

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

def IsCompleteTheory {LM : MetricSignature} (T : Set (Formula LM.toSignature)) : Prop :=
  IsTheory T ∧ ∃ (M : ContinuousStructure LM) (σ : Var → M.Carrier),
    T = {φ | IsSentence φ ∧ φ.eval M.toPreStructure σ = 0}

end ContinuousFOL
