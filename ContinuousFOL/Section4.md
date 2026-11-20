# Yaacov–Pedersen §4 Black-box theorems

Paper §4 (arXiv pp. 6–7) records five facts about the propositional logics and uses them as black boxes: weak completeness of Łukasiewicz logic (Fact 4.1), consistency versus satisfiability (Facts 4.2, 4.3), approximated strong completeness (Fact 4.4) and finite strong completeness (Fact 4.5) of continuous logic. The formalization does not assume them: all five are proved in Lean. The proof of Fact 4.1 follows Chang's algebraic route (MV-algebras, the Lindenbaum algebra, linearly ordered quotients and ordered abelian groups); Fact 4.5 reduces continuous logic to Łukasiewicz logic; Facts 4.2–4.4 follow by compactness.

**Added premise in Facts 4.2 and 4.3.** As stated in the paper these two facts are false when there are no propositional variables: then there are no formulae at all, so the empty set is satisfiable but (vacuously) inconsistent. The Lean statements therefore carry the extra hypothesis `[Nonempty I]` (at least one propositional variable), and the counterexample is itself proved (`LukPropForm.consistent_iff_satisfiable_fails_empty`, `CLPropForm.consistent_iff_satisfiable_fails_empty`). No other §4 statement needs a change. Neither Fact is used in the proof of any other result: no Lean module imports them (only the library root does), so the main theorems are unaffected.

@import "Section4.svg" {code_block=false, caption="Module dependencies within Yaacov–Pedersen §4"}

Subsections follow Lean import order; labels are mathematical English.

- [Soundness of continuous propositional logic](Section4/CLPropFormSoundness.md)
- [Transfer of linear inequalities from ordered groups to the reals](Section4/LinearTransfer.md)
- [Affine functions on real coordinate space](Section4/AffineFn.md)
- [Polyhedral cells in the unit cube and bounded ratios](Section4/PolyCell.md)
- [Piecewise-linear functions on the cube](Section4/HasPL.md)
- [Weak deduction theorem for Łukasiewicz logic](Section4/LukPropFormDeduction.md)
- [Semantic iteration for Łukasiewicz logic](Section4/LukPropFormSemanticIteration.md)
- [From the interval of an ordered group to the real unit interval](Section4/GroupEval.md)
- [MV-algebras](Section4/MVAlgebra.md)
- [Arithmetic and order in MV-algebras](Section4/MVBasic.md)
- [MV-chains and the carry identity](Section4/MVChain.md)
- [The standard MV-algebra on the unit interval](Section4/StandardMVAlgebra.md)
- [The ordered abelian group of an MV-chain](Section4/ChainGroup.md)
- [The Lindenbaum algebra of Łukasiewicz logic](Section4/LukLindenbaum.md)
- [Linear extensions and totally ordered Lindenbaum algebras](Section4/LukLinearTheory.md)
- [Soundness of Łukasiewicz propositional logic](Section4/LukPropFormSoundness.md)
- [Chang's completeness theorem (proof of Fact 4.1)](Section4/LukChang.md)
- [Finite strong completeness for Łukasiewicz logic](Section4/LukFiniteStrong.md)
- [Continuous logic reduced to Łukasiewicz logic (proof of Fact 4.5)](Section4/CLFromLuk.md)
- [Weak deduction theorem for continuous propositional logic](Section4/CLPropFormDeduction.md)
- [Compactness, consistency and approximated completeness (proofs of Facts 4.2–4.4)](Section4/PropCompactness.md)
- [Fact 4.4: approximated strong completeness](Section4/CLApproxStrongCompleteness.md)
- [Fact 4.3: consistency and satisfiability in continuous propositional logic](Section4/CLConsistentIffSatisfiable.md)
- [Fact 4.5: finite strong completeness of continuous propositional logic](Section4/CLFiniteStrongCompleteness.md)
- [Fact 4.2: consistency and satisfiability in Łukasiewicz logic](Section4/LukConsistentIffSatisfiable.md)
- [Fact 4.1: weak completeness of Łukasiewicz logic](Section4/LukWeakCompleteness.md)
- [Semantic iteration for continuous logic](Section4/CLPropFormSemanticIteration.md)
