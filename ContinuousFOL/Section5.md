# §5 Language and semantics of continuous first-order logic

Paper §5 (arXiv pp. 7–11) sets up continuous first-order logic: the logical symbols, continuous signatures with moduli of uniform continuity, signatures with a metric, pre-structures and structures, assignments, the value $\mathfrak M(\varphi,\sigma)\in[0,1]$ of a formula, models, satisfiability, entailment and logical equivalence. The Lean modules follow these definitions one by one; a few (the formula constants, iterated subtraction, rank, universe lifting) are bookkeeping that later sections need.

Universe levels: the paper lets the universe of a structure be any non-empty set. In Lean the carrier lives in an arbitrary universe `Type u`, and all semantic notions (satisfiable, entails, equivalent) are parameterized by that universe. `UliftPreStructure` shows that models in universe $0$ lift to every universe without changing any truth value, which is what lets the completeness theorem be stated for an arbitrary universe.

@import "Section5.svg" {code_block=false, caption="Module dependencies within §5"}

Subsections follow Lean import order; labels are mathematical English.

- [Continuous signatures](Section5/Signature.md)
- [Signatures with a metric](Section5/MetricSignature.md)
- [Pre-structures](Section5/PreStructure.md)
- [Replacing one argument of a tuple](Section5/ReplaceArg.md)
- [Pre-structures for a signature with a metric](Section5/MetricPreStructure.md)
- [Continuous structures](Section5/ContinuousStructure.md)
- [Variables](Section5/Var.md)
- [Terms](Section5/Term.md)
- [Formulae](Section5/Formula.md)
- [A fixed atomic formula](Section5/FormulaDefaultAtom.md)
- [The constants 1 and 0](Section5/FormulaOne.md)
- [Dyadic constants as formulae](Section5/FormulaDyadic.md)
- [Interpretation of terms](Section5/TermEval.md)
- [Updating an assignment](Section5/UpdateAssign.md)
- [The value of a formula](Section5/FormulaEval.md)
- [Models and satisfiability](Section5/ModelsPre.md)
- [Complete satisfiability and entailment](Section5/CompletelySatisfiable.md)
- [Semantic entailment](Section5/EntailsPre.md)
- [Derived connectives](Section5/FormulaConnectives.md)
- [Logical equivalence](Section5/FormulaEquiv.md)
- [Iterated subtraction for first-order formulae](Section5/FormulaIterSub.md)
- [Rank of a formula](Section5/FormulaRank.md)
- [Lifting structures to larger universes](Section5/UliftPreStructure.md)
