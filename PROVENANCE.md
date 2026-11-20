# Provenance

This repository is a standalone Lean 4 / Mathlib formalization of Itaï Ben
Yaacov and Arthur Paul Pedersen, *A proof of completeness for continuous
first-order logic*, Journal of Symbolic Logic **75** (2010) 168–190
(arXiv:0903.4051). It is not a thin wrapper and not a reimplementation of an
independent formalization.

**Itaï Ben Yaacov and Arthur Paul Pedersen did not participate in, review, or
endorse this formalization.** There are no other human collaborators. The Lean
development was produced by Lars Warren Ericson with AI-agent assistance under
his direction and review. The source paper is cited as literature only and is
not licensed under this repository's Apache-2.0 terms (see `NOTICE`).

**This repository is intended for standalone Palomar registration**, for the
Ben Yaacov–Pedersen 2010 continuous-logic completeness development alone,
following the Challenge / Solution / `comparator.json` / `formalization.yaml`
pattern. Registration is pending; the registry id will be recorded here once
assigned.

## Framing

Primary story: **rigorous reconstruction / verification** of Ben Yaacov–Pedersen
2010 (§1–§9), including continuous propositional axioms (Group 1), the §4 propositional
Facts 4.1–4.5 (proved in Lean, not assumed), continuous first-order language and semantics, Group 2 axioms, and
the completeness / approximated strong-completeness theorems. Secondary story:
decidability consequences for recursively axiomatized theories (paper §9).

## Proof chart and Comparator

The paper-facing proof chart (`holes-graph.json` / `HOLES.md`) has 75 nodes,
all proved (`sorry`-free). The full list of proved results with Lean names,
files, axioms and verbatim paper quotes is in `formalization.yaml`
(`status.main_results`, `alignment.statements`). Packaging:

- Compared declarations live in namespace `ContinuousFOL`.
- `ContinuousFOLComparator/Challenge.lean` is a Mathlib-only statement file
  (deliberate `sorry` holes).
- `ContinuousFOLComparator/Solution.lean` imports the `ContinuousFOL/` library.

**Project rule: no Lean `axiom`.** Compared Solution proofs use only `propext`,
`Quot.sound`, and `Classical.choice`.

## Dependencies

Proofs use Mathlib (Lake pin in `lakefile.toml` / `lake-manifest.json`). No
project-defined `axiom`s. Intentional challenge stubs in
`ContinuousFOLComparator/Challenge.lean` are unchanged by library completion.

## AI assistance

Model cards for this project are listed in `scripts/ai_model_cards.py` and
mirrored under `automation.methods` in `formalization.yaml`. The registry
**includes Google Gemini 4 Carbon** alongside Cursor Grok 4.7, Cursor Composer
2.5, and Claude Fable 5.2.

## Deviations from the paper (errata)

| Paper statement | Lean | Added premise | Why |
|---|---|---|---|
| Fact 4.2 (§4): "Let S be a Lukasiewicz propositional logic, and Σ ⊆ S. Then Σ is consistent if and only if it is satisﬁable." | `ContinuousFOL.luk_consistent_iff_satisfiable` | `[Nonempty I]`: at least one propositional variable | False when there are no variables: there are then no formulas, so `∅` is satisfiable but inconsistent (Def. 3.1). Proved: `LukPropForm.consistent_iff_satisfiable_fails_empty`. |
| Fact 4.3 (§4): "Let S be a continuous propositional logic and Σ ⊆ S. Then Σ is consistent if and only if it is satisﬁable." | `ContinuousFOL.cl_consistent_iff_satisfiable` | `[Nonempty I]`: at least one propositional variable | Same counterexample. Proved: `CLPropForm.consistent_iff_satisfiable_fails_empty`. |

Consistent ⇒ satisfiable is proved for every `I` (`*.satisfiable_of_consistent`).
Neither Fact is used by the main theorems. No other paper statement was changed.
