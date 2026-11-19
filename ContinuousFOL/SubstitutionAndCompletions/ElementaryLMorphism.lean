/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 Definition 6.5 elementary; vision.md page 12
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.LMorphism
public import ContinuousFOL.LanguageAndSemantics.FormulaEval

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- An elementary `𝓛`-morphism (Definition 6.5). -/
structure ElementaryLMorphism {L : Signature} (M N : PreStructure L)
    extends LMorphism M N where
  map_eval : ∀ (σ : Var → M.Carrier) (φ : Formula L),
    φ.eval M σ = φ.eval N (toFun ∘ σ)

end ContinuousFOL
