/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.9; vision.md page 25
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.FormulaFreeVars

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Definition 9.9: Sentences, Theories, and Complete Theories. -/
def IsSentence {L : Signature} (φ : Formula L) : Prop := φ.freeVars = ∅

end ContinuousFOL
