/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §4 Fact 4.3; vision.md page 6–7. Added premise `[Nonempty I]`; see the docstring.
-/
module

public import ContinuousFOL.Group1Axioms.CLPropForm.Provable
public import ContinuousFOL.LukasiewiczAndContinuous.CLPropFormModels
public import ContinuousFOL.LukasiewiczAndContinuous.PropCompactness

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Fact 4.3: Consistency ↔ Satisfiability for Continuous Propositional Logic [Ben].

    Paper (§4, verbatim): "Fact 4.3. Let S be a continuous propositional logic and Σ ⊆ S. Then Σ is consistent if and only if it is satisﬁable."

    Definition 2.1 (verbatim): "Let S0 = {Pi : i ∈ I} be a set of distinct symbols."
    Definition 3.1 (verbatim): "We say that a set of formulae Σ is inconsistent if
    Σ ⊢ ϕ for every formula ϕ and consistent otherwise."

    **Added premise `[Nonempty I]` (at least one propositional variable).** The
    paper does not require `I` to be nonempty, but the literal statement is false
    when it is empty: then there are no formulas at all, so `Σ = ∅` is satisfiable
    (vacuously) yet inconsistent (`Σ ⊢ ϕ` holds for every one of the zero formulas).
    The counterexample is proved in `CLPropForm.consistent_iff_satisfiable_fails_empty`.
    With at least one variable the statement holds as written; the direction
    consistent ⇒ satisfiable is proved for every `I`
    (`CLPropForm.satisfiable_of_consistent`). -/
theorem cl_consistent_iff_satisfiable {I : Type*} [Nonempty I] (hypSet : Set (CLPropForm I)) :
    CLPropForm.Consistent hypSet ↔ CLPropForm.Satisfiable hypSet :=
  CLPropForm.consistent_iff_satisfiable hypSet

end ContinuousFOL
