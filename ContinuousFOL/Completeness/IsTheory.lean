/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.9 theories
-/
module

public import ContinuousFOL.Completeness.IsSentence
public import ContinuousFOL.LanguageAndSemantics.MetricSignature

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

def IsTheory {LM : MetricSignature} (T : Set (Formula LM.toSignature)) : Prop :=
  ∀ φ ∈ T, IsSentence φ

end ContinuousFOL
