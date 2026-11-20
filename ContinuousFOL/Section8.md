# §8 The essentials

Paper §8 (arXiv pp. 15–20) develops the proof theory needed for completeness: the weak Deduction Theorem 8.1, the Generalization Theorem 8.2, provable equivalence of bound renamings (Lemma 8.3), generalization over a new constant (Lemma 8.4), and the continuous notion of a maximal consistent set (Lemmas 8.5–8.6, Definition 8.8, Theorem 8.10), with the instantiation Lemma 8.11 and the cut Lemma 8.12 that are used to build the Henkin model.

Every result is proved twice in Lean, once for $\vdash_Q$ without a metric and once for the metric calculus with (A10)–(A14); the metric versions either repeat the argument or reduce to the plain one by adding all metric axioms as premises.

@import "Section8.svg" {code_block=false, caption="Module dependencies within §8"}

Subsections follow Lean import order; labels are mathematical English.

- [Basic derived rules; inconsistency means proving 1](Section8/InconsistentIffProvableOne.md)
- [Monotonicity and finiteness of proofs](Section8/ProvableQMono.md)
- [The Deduction Theorem](Section8/DeductionTheorem.md)
- [The Generalization Theorem](Section8/GeneralizationTheorem.md)
- [Bound renaming is provably equivalent](Section8/ProvableBoundSubst.md)
- [Extending consistent sets](Section8/ConsistentAdjoin.md)
- [Maximal consistent sets](Section8/MaximalConsistent.md)
- [Generalizing over a new constant](Section8/GeneralizeFreshConst.md)
- [Maximal consistent sets with a metric](Section8/MaximalConsistentMetric.md)
