# §9 A proof of completeness

Paper §9 (arXiv pp. 20–25) proves the main results: Henkin completions (Proposition 9.2), the Henkin model built from terms (Theorem 9.4), completeness (Theorem 9.5), approximated strong completeness (Corollary 9.6), Pavelka-style completeness (Corollary 9.8), decidability of complete theories with recursively enumerable axiomatizations (Corollary 9.11), and compactness (Corollary 9.12).

Points where the Lean differs in form from the paper:

- Henkin signature: instead of the tower $\mathcal L_0\subseteq\mathcal L_1\subseteq\cdots$, a single inductive type of codes contains the symbols of $\mathcal L$ and a constant $c_{(\varphi,x,p,q)}$ for every code of an $\mathcal L^c$-formula; the size of codes replaces the paper's level $m$ in the minimality argument.
- Universes: the Henkin model lives in universe $0$; the universe-lifting lemmas of §5 transfer every result to arbitrary universes.
- Inconsistent $\Gamma$ in Corollary 9.8: there are no models, and the equality $\varphi^\circ_\Gamma=\varphi^\circledcirc_\Gamma=0$ relies on the convention $\sup\emptyset=0$ for reals (Mathlib's `Real.sSup_empty`), together with $\inf$ of all dyadics being $0$. The paper does not discuss this case.
- Complete theories (Definition 9.9(ii)): the Lean intersects the set of formulae true in $(\mathfrak M,\sigma)$ with the set of sentences, since a theory is by definition a set of sentences.
- Decidability (Corollary 9.11): the paper assumes a countable recursive language. The Lean makes this explicit as a `RecursivePresentation`: an injective Gödel numbering with computable codes for $\dot-$, dyadic constants and sup-closure, and an r.e. set of logical axioms.

@import "Section9.svg" {code_block=false, caption="Module dependencies within §9"}

Subsections follow Lean import order; labels are mathematical English.

- [Henkin completeness](Section9/HenkinComplete.md)
- [Refuting a lower bound proves an upper bound](Section9/ProvableTsubOfInconsistentAdjoin.md)
- [Signature extensions and reducts](Section9/SignatureExtension.md)
- [Henkin completions](Section9/ExistsHenkinExtension.md)
- [The term pre-structure](Section9/TermPreStructure.md)
- [The truth lemma for the Henkin model](Section9/TermPreStructureEvalEqSup.md)
- [The Henkin model theorem](Section9/HenkinModelExistence.md)
- [The Henkin model theorem with a metric](Section9/HenkinModelExistenceMetric.md)
- [Completeness with a metric](Section9/CompletenessMetric.md)
- [Completeness without a metric](Section9/CompletenessPre.md)
- [Approximated strong completeness](Section9/ApproximatedStrongCompleteness.md)
- [Compactness with a metric](Section9/CompactnessMetric.md)
- [Compactness without a metric](Section9/CompactnessPre.md)
- [Degree of truth](Section9/DegreeOfTruth.md)
- [Sentences](Section9/IsSentence.md)
- [Theories](Section9/IsTheory.md)
- [Complete theories](Section9/IsCompleteTheory.md)
- [Recursive presentations of a language](Section9/RecursivePresentation.md)
- [Decidable theories](Section9/DecidableTheory.md)
- [Degree of provability](Section9/DegreeOfProvability.md)
- [Independence of the universe](Section9/UniverseTransport.md)
- [Pavelka-style completeness](Section9/PavelkaCompleteness.md)
- [Closure properties of r.e. and computable predicates](Section9/REPredBasic.md)
- [Provability from r.e. premises is r.e.](Section9/ProvableMetricQRE.md)
- [Complete r.e.-axiomatized theories are decidable](Section9/UniformlyComputableDegree.md)
