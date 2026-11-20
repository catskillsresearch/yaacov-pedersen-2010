# §4 Black-box theorems

Paper pin: vision.md pages 6–7.

## Lean modules

- [`BlackBox/CLApproxStrongCompleteness.lean`](BlackBox/CLApproxStrongCompleteness.lean)
- [`BlackBox/CLConsistentIffSatisfiable.lean`](BlackBox/CLConsistentIffSatisfiable.lean)
- [`BlackBox/CLFiniteStrongCompleteness.lean`](BlackBox/CLFiniteStrongCompleteness.lean)
- [`BlackBox/LukConsistentIffSatisfiable.lean`](BlackBox/LukConsistentIffSatisfiable.lean)
- [`BlackBox/LukWeakCompleteness.lean`](BlackBox/LukWeakCompleteness.lean)

## Added premise in Facts 4.2 and 4.3

Facts 4.2 and 4.3 carry the added premise `[Nonempty I]` (at least one
propositional variable). The literal statements are false when there are no
variables (`∅` is then satisfiable but inconsistent). The counterexample is
proved in `LukPropForm.consistent_iff_satisfiable_fails_empty` and
`CLPropForm.consistent_iff_satisfiable_fails_empty`. See the docstrings in the
two Lean files and the deviations table in `README.md`.
