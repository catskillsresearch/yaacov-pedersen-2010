# Yaacov–Pedersen §6 Substitution and metric completions

Paper §6 (arXiv pp. 11–14) recalls free and bound substitution, states the Substitution Lemma 6.2 and the Bound Substitution Lemma 6.4, defines $\mathcal L$-morphisms, and shows that every pre-structure maps elementarily into its metric completion (Theorems 6.6–6.9), so that entailment and satisfiability may be computed over complete structures (Corollary 6.11). The paper proves 6.4 and 6.9 only in outline; here they are proved in full.

The paper passes from a pre-structure to the quotient by $d=0$ and then to the completion. In Lean both steps happen at once: Mathlib's completion of a pseudo-metric space is already a (Hausdorff) complete metric space, and the canonical map from the pre-structure is an isometry with dense image.

@import "Section6.svg" {code_block=false, caption="Module dependencies within Yaacov–Pedersen §6"}

Subsections follow Lean import order; labels are mathematical English.

- [Variables of a term](Section6/TermVars.md)
- [Free, bound and all variables; sup-closure](Section6/FormulaFreeVars.md)
- [Substitution in terms](Section6/TermSubst.md)
- [Free substitution](Section6/FormulaFreeSubst.md)
- [Bound substitution](Section6/FormulaBoundSubst.md)
- [The Substitution Lemma](Section6/SubstitutionLemma.md)
- [The Bound Substitution Lemma](Section6/BoundSubstitutionLemma.md)
- [L-morphisms; surjective morphisms are elementary](Section6/LMorphism.md)
- [Elementary L-morphisms](Section6/ElementaryLMorphism.md)
- [Uniform continuity of definable maps](Section6/EvalUniformlyContinuous.md)
- [Completion of finite products](Section6/PiCompletion.md)
- [The metric completion of a pre-structure](Section6/MetricPreStructureCompletion.md)
- [Existence of metric completions](Section6/ExistsMetricCompletion.md)
- [Entailment over complete structures](Section6/EntailsMetricIffComplete.md)
- [Occurrences of a constant; replacing it by a variable](Section6/FormulaHasFunc.md)
