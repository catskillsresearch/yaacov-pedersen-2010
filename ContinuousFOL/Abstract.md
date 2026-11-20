# Abstract

Lean 4 / Mathlib formalization of Itaï Ben Yaacov and Arthur Paul Pedersen,
*A proof of completeness for continuous first-order logic*, Journal of Symbolic
Logic **75** (2010) 168–190.

The formalization proves, sorry-free and with no added axioms, the paper's
main results: soundness (Theorem 7.2); completeness, i.e. a set of formulae is
(completely) satisfiable if and only if it is consistent (Theorem 9.5);
approximated strong completeness
($\Sigma \models \varphi$ iff $\Sigma \vdash \varphi \mathbin{\dot{-}} 2^{-n}$
for all $n < \omega$, Corollary 9.6); Pavelka-style completeness
(Corollary 9.8); decidability of complete recursively axiomatized theories
(Corollary 9.11); and compactness (Corollary 9.12). Along the way it proves
the §4 propositional Facts 4.1–4.5 (including Chang's completeness theorem for
Łukasiewicz logic) and the §§6–8 lemmas they rest on, rather than assuming
them.

**Added premise (deviation from the paper).** Facts 4.2 and 4.3 (consistency ↔
satisfiability for Łukasiewicz and for continuous propositional logic) needed
one extra premise to go through: there is at least one propositional variable
(`[Nonempty I]` in Lean). As literally stated in the paper, with no variables
allowed (Definition 2.1 does not require `I` to be nonempty), both Facts are
false: with no variables there are no formulas, so the empty set is satisfiable
but, by Definition 3.1, inconsistent. This counterexample is proved in Lean
(`LukPropForm.consistent_iff_satisfiable_fails_empty`,
`CLPropForm.consistent_iff_satisfiable_fails_empty`). Neither Fact is used by
the main theorems, which are unaffected.

**Palomar Registration:** TBD.
