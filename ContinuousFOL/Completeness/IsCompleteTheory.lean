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

/-- Definition 9.9(ii): "We call a theory T *complete* if there is a continuous
    𝓛-structure 𝔐 (and an 𝔐-assignment σ) such that T = {φ : (𝔐, σ) ⊨_QC φ}."

    The paper writes that set as all formulae modeled by (𝔐, σ), but T is already
    a theory, hence a set of sentences (Definition 9.9(i)). The Lean therefore
    intersects with `IsSentence`. Without that restriction the right-hand side
    would contain open formulae that always evaluate to 0 (for example `d x x`),
    and could not be a theory. -/
def IsCompleteTheory.{u} {LM : MetricSignature} (T : Set (Formula LM.toSignature)) : Prop :=
  IsTheory T ∧ ∃ (M : ContinuousStructure.{u} LM) (σ : Var → M.Carrier),
    T = {φ | IsSentence φ ∧ φ.eval M.toPreStructure σ = 0}

end ContinuousFOL
