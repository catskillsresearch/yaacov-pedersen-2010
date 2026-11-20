/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §4 Fact 4.1; vision.md page 6
-/
module

public import ContinuousFOL.Group1Axioms.LukPropForm.Provable
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormModels
public import ContinuousFOL.LukasiewiczAndContinuous.LukChang

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Fact 4.1: Weak Completeness for Łukasiewicz Logic [Cha59, RR58]. -/
theorem luk_weak_completeness {I : Type*} (φ : LukPropForm I) :
    LukPropForm.Entails ∅ φ ↔ LukPropForm.Provable ∅ φ :=
  LukPropForm.entails_empty_iff_provable φ

end ContinuousFOL
