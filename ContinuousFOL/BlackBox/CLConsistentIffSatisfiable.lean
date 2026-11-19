/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §4 Fact 4.3; vision.md page 6–7
-/
module

public import ContinuousFOL.Group1Axioms.CLPropForm.Provable
public import ContinuousFOL.LukasiewiczAndContinuous.CLPropFormModels

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Fact 4.3: Consistency ↔ Satisfiability for Continuous Propositional Logic [Ben]. -/
axiom cl_consistent_iff_satisfiable {I : Type*} (Σ_set : Set (CLPropForm I)) :
    CLPropForm.Consistent Σ_set ↔ CLPropForm.Satisfiable Σ_set

end ContinuousFOL
