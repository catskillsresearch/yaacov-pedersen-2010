# Abstract

Lean 4 / Mathlib formalization of Itaï Ben Yaacov and Arthur Paul Pedersen,
*A proof of completeness for continuous first-order logic*, Journal of Symbolic
Logic **75** (2010) 168–190.

Primary result targeted for Comparator packaging: a set of formulae is
(completely) satisfiable if and only if it is consistent, with the paper's
approximated strong completeness
($\Sigma \models \varphi$ iff $\Sigma \vdash \varphi \mathbin{\dot{-}} 2^{-n}$
for all $n < \omega$).

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
