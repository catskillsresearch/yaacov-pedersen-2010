/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §4 Fact 4.5; vision.md page 7
-/
module

public import ContinuousFOL.Group1Axioms.CLPropForm.Provable
public import ContinuousFOL.LukasiewiczAndContinuous.CLPropFormModels
public import Mathlib.Data.Finset.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Fact 4.5: Finite Strong Completeness for Continuous Propositional Logic. -/
axiom cl_finite_strong_completeness {I : Type*} (Σ_set : Finset (CLPropForm I))
    (φ : CLPropForm I) :
    CLPropForm.Entails (Σ_set : Set (CLPropForm I)) φ ↔
      CLPropForm.Provable (Σ_set : Set (CLPropForm I)) φ

end ContinuousFOL
