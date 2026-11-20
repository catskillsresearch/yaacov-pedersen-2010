[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/yaacov-pedersen-2010/build.yml?label=Lean%204)](https://github.com/catskillsresearch/yaacov-pedersen-2010/actions/workflows/build.yml)

# Formalization of Completeness for Continuous First-Order Logic

Formalization of Itaï Ben Yaacov and Arthur Paul Pedersen,
*A proof of completeness for continuous first-order logic*,
J. Symbolic Logic **75** (2010) 168–190
([arXiv:0903.4051](https://arxiv.org/abs/0903.4051)).

Standalone package aimed at [Palomar](https://palomar-registry.org/about)
registration (Challenge / Solution / `comparator.json` / `formalization.yaml`).
Palomar Registration: TBD. See `PROVENANCE.md`.

## Build

```bash
lake exe cache get          # fetch Mathlib build cache (optional, recommended)
lake build                  # default targets: ContinuousFOL, ContinuousFOLChallenge, ContinuousFOLSolution
python3 scripts/build_holes.py   # regenerate the proof board (HOLES.md, holes-graph.json, holes.html)
```

Toolchain: Lean `v4.35.0` (see `lean-toolchain`), Mathlib pin in `lakefile.toml` / `lake-manifest.json`.

## Layout

| Path | Content |
|------|---------|
| `sources/yaacov_pedersen_2010.pdf` | Source paper |
| `sources/yaacov_pedersen_2010_vision.md` | Vision OCR (preferred over pdftotext) |
| `ContinuousFOL/<Topic>/*.lean` | Lean library, one folder per topic (e.g. `Essentials/`, `Completeness/`); the writeup maps modules to the paper's §§1–9 |
| `ContinuousFOL.lean` | Library root (imports every module) |
| `ContinuousFOL.md` | Paper-facing writeup root (table of contents) |
| `ContinuousFOLComparator/` | Palomar Challenge / Solution pair |
| `docs/` | Design notes (Corollary 9.11 presentation; development log for §4 Facts) |

See `docs/recursive-presentation-cor-9.11.md` for why `RecursivePresentation` includes a computable sup-closure on formula codes (Corollary 9.11 / “countable, recursive language”).
See `docs/section-4-facts-plan.md` for how Facts 4.1–4.5 were proved (Chang's completeness via MV-chains and ℓ-groups).

## Status

**Complete.** Every targeted result of the paper is proved in Lean 4 / Mathlib,
including the §4 propositional Facts (proved, not assumed). The `ContinuousFOL`
library is `sorry`-free and declares no `axiom`; all results depend only on
`propext`, `Classical.choice` and `Quot.sound`. The only `sorry`s in the
repository are the intended statement stubs in
`ContinuousFOLComparator/Challenge.lean`, proved in `Solution.lean`. The proof
board (`HOLES.md`) has 75 nodes, all done. One paper statement carries an added
premise (Facts 4.2/4.3, see the deviations table below). Full machine-readable
list of results, files, axioms and verbatim paper quotes: `formalization.yaml`
(`status.main_results`, `alignment.statements`, `fidelity.divergences`).

## Results

| Paper | Lean (namespace `ContinuousFOL`) | File |
|---|---|---|
| Remark 3.4 | `DyadicCode.val_range_eq_dyadics` | `Group1Axioms/DyadicCode/Val.lean` |
| Fact 4.1 | `luk_weak_completeness` | `BlackBox/LukWeakCompleteness.lean` |
| Fact 4.2 | `luk_consistent_iff_satisfiable` (with the added premise [Nonempty I] (at least one propositional variable); see fidelity.divergences) | `BlackBox/LukConsistentIffSatisfiable.lean` |
| Fact 4.3 | `cl_consistent_iff_satisfiable` (with the added premise [Nonempty I] (at least one propositional variable); see fidelity.divergences) | `BlackBox/CLConsistentIffSatisfiable.lean` |
| Fact 4.4 | `cl_approx_strong_completeness` | `BlackBox/CLApproxStrongCompleteness.lean` |
| Fact 4.5 | `cl_finite_strong_completeness` | `BlackBox/CLFiniteStrongCompleteness.lean` |
| Lemma 6.2 | `substitution_lemma` | `SubstitutionAndCompletions/SubstitutionLemma.lean` |
| Lemma 6.4 | `bound_substitution_lemma`<br>`bound_substitution_lemma_metric` | `SubstitutionAndCompletions/BoundSubstitutionLemma.lean` |
| Theorem 6.6 | `surjective_morphism_elementary` | `SubstitutionAndCompletions/LMorphism.lean` |
| Theorem 6.8 | `eval_uniformly_continuous` | `SubstitutionAndCompletions/EvalUniformlyContinuous.lean` |
| Theorem 6.9 | `exists_metric_completion` | `SubstitutionAndCompletions/ExistsMetricCompletion.lean` |
| Corollary 6.11 | `entails_metric_iff_complete` (clause (i))<br>`satisfiable_metric_iff_complete` (clause (ii)) | `SubstitutionAndCompletions/EntailsMetricIffComplete.lean` |
| Theorem 7.2 | `soundness_pre` (clause (i), signature without metric)<br>`satisfiable_consistent_pre` (clause (ii), signature without metric)<br>`soundness_metric` (clause (i), signature with a metric)<br>`satisfiable_consistent_metric` (clause (ii), signature with a metric)<br>`soundness_metric_full` (clauses (i) and (ii), signature with a metric, both readings (pre-structures and complete structures) in one statement) | `Group2Axioms/SoundnessMetric.lean`<br>`Group2Axioms/SoundnessPre.lean` |
| Theorem 8.1 | `deduction_theorem`<br>`deduction_theorem_metric` | `Essentials/DeductionTheorem.lean` |
| Lemma 8.2 | `generalization_theorem`<br>`generalization_theorem_metric` | `Essentials/GeneralizationTheorem.lean` |
| Lemma 8.3 | `provable_bound_subst`<br>`provable_bound_subst_metric` | `Essentials/ProvableBoundSubst.lean` |
| Lemma 8.4 | `generalize_fresh_const`<br>`generalize_fresh_const_metric` | `Essentials/GeneralizeFreshConst.lean` |
| Lemma 8.5 | `consistent_adjoin_approx` (clause (i))<br>`consistent_adjoin_comparable` (clause (ii))<br>`consistent_adjoin_approx_metric` (clause (i))<br>`consistent_adjoin_comparable_metric` (clause (ii)) | `Essentials/ConsistentAdjoin.lean` |
| Lemma 8.6 | `maximal_in_consistent_extensions_iff`<br>`maximal_in_consistent_extensions_iff_metric` | `Essentials/MaximalConsistent.lean`<br>`Essentials/MaximalConsistentMetric.lean` |
| Remark 8.9 | `MaximalConsistent.mem_iff_provable` (first sentence of Remark 8.9)<br>`MaximalConsistentMetric.mem_iff_provable` (first sentence of Remark 8.9) | `Essentials/MaximalConsistent.lean`<br>`Essentials/MaximalConsistentMetric.lean` |
| Theorem 8.10 | `exists_maximal_consistent`<br>`exists_maximal_consistent_metric` | `Essentials/MaximalConsistent.lean`<br>`Essentials/MaximalConsistentMetric.lean` |
| Lemma 8.11 | `maximal_consistent_sup_instantiate`<br>`maximal_consistent_sup_instantiate_metric` | `Essentials/MaximalConsistent.lean`<br>`Essentials/MaximalConsistentMetric.lean` |
| Lemma 8.12 | `maximal_consistent_sup_eq_inf`<br>`maximal_consistent_sup_eq_inf_metric` | `Essentials/MaximalConsistent.lean`<br>`Essentials/MaximalConsistentMetric.lean` |
| Proposition 9.2 | `exists_henkin_extension`<br>`exists_henkin_extension_metric` | `Completeness/ExistsHenkinExtension.lean` |
| Theorem 9.4 | `henkin_model_existence`<br>`henkin_model_existence_metric` | `Completeness/HenkinModelExistence.lean`<br>`Completeness/HenkinModelExistenceMetric.lean` |
| Theorem 9.5 | `completeness_pre` (first sentence (signature without metric))<br>`completeness_metric` (second sentence (signature with a metric)) | `Completeness/CompletenessMetric.lean`<br>`Completeness/CompletenessPre.lean` |
| Corollary 9.6 | `approximated_strong_completeness_pre` (first sentence)<br>`approximated_strong_completeness_metric` ("Moreover" sentence (signature with a metric)) | `Completeness/ApproximatedStrongCompleteness.lean` |
| Corollary 9.8 | `pavelka_completeness_pre`<br>`pavelka_completeness_metric` | `Completeness/PavelkaCompleteness.lean` |
| Corollary 9.11 | `complete_re_theory_decidable` (with RecursivePresentation (supClosureCode); see fidelity.divergences) | `Completeness/UniformlyComputableDegree.lean` |
| Corollary 9.12 | `compactness_pre` (satisfiable reading)<br>`compactness_metric` (completely satisfiable reading (signature with a metric)) | `Completeness/CompactnessMetric.lean`<br>`Completeness/CompactnessPre.lean` |

## Completed proof (paper writeup)

The `.md` tree is the source of the writeup; it is flattened to `arxiv.md`,
translated to `arxiv.tex`, and compiled (pdfLaTeX + BibTeX, `references.bib`)
to `ContinuousFOL.pdf`. Layout follows the lyasoff2016 repository.

| File | Role |
|------|------|
| [`ContinuousFOL.md`](ContinuousFOL.md) | Root: front matter (`bibliography: references.bib`) and table of contents |
| [`ContinuousFOL/Abstract.md`](ContinuousFOL/Abstract.md) | Abstract (incl. the added-premise note for Facts 4.2/4.3) |
| [`ContinuousFOL/Introduction.md`](ContinuousFOL/Introduction.md) | Section graph (`ContinuousFOL.svg`), faithfulness notes, sources / software / AI assistance |
| [`ContinuousFOL/SectionN.md`](ContinuousFOL/) | §1–§9 barrels: orientation, deviation notes, module graph `SectionN.svg`, links to leaves |
| [`ContinuousFOL/SectionN/Name.md`](ContinuousFOL/) | One leaf per `.lean`: paraphrased paper box (`*_math.txt`), English recap of the theorems and proofs (`*_aisummary.txt`, `*_ailean.txt`), full Lean `@import` |
| [`ContinuousFOL/module_writeup.json`](ContinuousFOL/module_writeup.json) | Source database for the leaf sidecars |
| [`references.bib`](references.bib) | Bibliography (paper, literature, Lean/Mathlib and pinned dependencies, AI model cards) |

```bash
python3 scripts/scaffold_continuousfol_writeup.py          # regenerate leaves, barrels and graphs from module_writeup.json
python3 scripts/scaffold_continuousfol_writeup.py --check  # verify every module has a leaf and nothing is stale
python3 scripts/section_deps_graph.py                      # ContinuousFOL.svg (section dependency graph)
bash scripts/build_arxiv_pdf.sh                            # md → arxiv.tex → ContinuousFOL.pdf (needs latexmk, bibtex)
```

The PDF has a title page (with the Palomar registration line, currently TBD),
a table of contents on its own page, pretty-printed Lean listings with Unicode
mapped to LaTeX, and a BibTeX bibliography.

## Palomar packaging

| File | Role |
|------|------|
| [`ContinuousFOLComparator/Challenge.lean`](ContinuousFOLComparator/Challenge.lean) | Mathlib-only statement of record (`sorry` holes) |
| [`ContinuousFOLComparator/Solution.lean`](ContinuousFOLComparator/Solution.lean) | Imports `ContinuousFOL/` |
| [`comparator.json`](comparator.json) | Compared theorems / definitions |
| [`formalization.yaml`](formalization.yaml) | v0.4 self-report |
| [`PROVENANCE.md`](PROVENANCE.md) | Authorship; source-author non-involvement |
| [`LICENSE`](LICENSE) / [`NOTICE`](NOTICE) | Apache-2.0 + third-party source notice |
| [`scripts/ai_model_cards.py`](scripts/ai_model_cards.py) | AI model-card registry (Grok Bot, Gemini 4 Carbon) |

```bash
bash scripts/palomar_preflight.sh   # Palomar packaging checks
lake build ContinuousFOLChallenge ContinuousFOLSolution
```

Itaï Ben Yaacov and Arthur Paul Pedersen did not participate in or endorse this
formalization. Author: Lars Warren Ericson (no other collaborators).

## AI model cards

Recorded in `scripts/ai_model_cards.py` and `formalization.yaml` → `automation`:

- Grok Bot
- Google Gemini 4 Carbon

## Proof-hole board

Dependency graph of paper-facing theorems. The graph JSON is **embedded** in
`holes.html` (file:// works), or serve locally:

```bash
python3 scripts/build_holes.py   # refreshes HOLES.md / holes-graph.json / embeds into holes.html
python3 -m http.server 8765 --bind 127.0.0.1
# open http://localhost:8765/holes.html
```

| File | Role |
|------|------|
| [`holes.html`](holes.html) | Interactive board (embedded graph) |
| [`holes-graph.json`](holes-graph.json) | Node/edge data (also embedded) |
| [`HOLES.md`](HOLES.md) | Markdown inventory |

## Deviations from the paper (errata)

| Paper statement | Lean | Added premise | Why |
|---|---|---|---|
| Fact 4.2 (§4): "Let S be a Lukasiewicz propositional logic, and Σ ⊆ S. Then Σ is consistent if and only if it is satisﬁable." | `ContinuousFOL.luk_consistent_iff_satisfiable` | `[Nonempty I]`: at least one propositional variable | False when there are no variables: there are then no formulas, so `∅` is satisfiable but inconsistent (Def. 3.1). Proved: `LukPropForm.consistent_iff_satisfiable_fails_empty`. |
| Fact 4.3 (§4): "Let S be a continuous propositional logic and Σ ⊆ S. Then Σ is consistent if and only if it is satisﬁable." | `ContinuousFOL.cl_consistent_iff_satisfiable` | `[Nonempty I]`: at least one propositional variable | Same counterexample. Proved: `CLPropForm.consistent_iff_satisfiable_fails_empty`. |

Consistent ⇒ satisfiable is proved for every `I` (`*.satisfiable_of_consistent`).
Neither Fact is used in the proof of any other result: no Lean module imports them (only the library root does), so the main theorems are unaffected. No other paper statement was changed;
reading choices for Definition 9.9, Corollaries 9.8 and 9.11 are listed in
`formalization.yaml` → `fidelity.divergences`.
