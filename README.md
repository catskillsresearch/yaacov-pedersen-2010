[![Lean 4](https://img.shields.io/github/actions/workflow/status/catskillsresearch/yaacov-pedersen-2010/build.yml?label=Lean%204)](https://github.com/catskillsresearch/yaacov-pedersen-2010/actions/workflows/build.yml)

# Formalization of Completeness for Continuous First-Order Logic

Formalization of Itaï Ben Yaacov and Arthur Paul Pedersen,
*A proof of completeness for continuous first-order logic*,
J. Symbolic Logic **75** (2010) 168–190
([arXiv:0903.4051](https://arxiv.org/abs/0903.4051)).

Standalone package aimed at [Palomar](https://palomar-registry.org/about)
registration (Challenge / Solution / `comparator.json` / `formalization.yaml`).
See `PROVENANCE.md`.

## Build

```bash
lake exe cache get   # optional, after lake update
lake build ContinuousFOL
```

Toolchain: Lean `v4.35.0` (see `lean-toolchain`), Mathlib pin in `lakefile.toml`.

## Layout

| Path | Content |
|------|---------|
| `sources/yaacov_pedersen_2010.pdf` | Source paper |
| `sources/yaacov_pedersen_2010_vision.md` | Vision OCR (preferred over pdftotext) |
| `ContinuousFOL/*.lean` | Section modules with paper-position comments |
| `ContinuousFOL.md` | Paper-facing writeup root (TOC only) |
| `ContinuousFOLComparator/` | Palomar Challenge / Solution pair |

See `docs/recursive-presentation-cor-9.11.md` for why `RecursivePresentation` includes a computable sup-closure on formula codes (Corollary 9.11 / “countable, recursive language”).
See `docs/section-4-facts-plan.md` for the plan and size estimate for Facts 4.1 and 4.5 (`luk_weak_completeness`, `cl_finite_strong_completeness`).

## Status

Scaffold / framework stage. Proof-chart holes are not yet inventoried
(`python3 scripts/build_holes.py`). Target: sorry-free Comparator family and
Palomar registration.

## Completed proof (paper writeup)

| File | Role |
|------|------|
| [`ContinuousFOL.md`](ContinuousFOL.md) | Paper-facing TOC |
| [`ContinuousFOL/SectionN.md`](ContinuousFOL/) | Section barrels + subsection dependency SVGs |
| [`ContinuousFOL/SectionN/Name.md`](ContinuousFOL/) | One leaf per `.lean` (`*_aisummary.txt`, `*_math.txt`, `*_ailean.txt`, Lean `@import`) |

```bash
python3 scripts/compile_md_tree.py --tex-only   # → arxiv.md + arxiv.tex
bash scripts/build_arxiv_pdf.sh                 # → ContinuousFOL.pdf (needs latexmk)
```

## Palomar packaging

| File | Role |
|------|------|
| [`ContinuousFOLComparator/Challenge.lean`](ContinuousFOLComparator/Challenge.lean) | Mathlib-only statement of record (`sorry` holes) |
| [`ContinuousFOLComparator/Solution.lean`](ContinuousFOLComparator/Solution.lean) | Imports `ContinuousFOL/` |
| [`comparator.json`](comparator.json) | Compared theorems / definitions |
| [`formalization.yaml`](formalization.yaml) | v0.4 self-report |
| [`PROVENANCE.md`](PROVENANCE.md) | Authorship; source-author non-involvement |
| [`LICENSE`](LICENSE) / [`NOTICE`](NOTICE) | Apache-2.0 + third-party source notice |
| [`scripts/ai_model_cards.py`](scripts/ai_model_cards.py) | AI model-card registry (**includes Gemini 4 Carbon**) |

```bash
bash scripts/palomar_preflight.sh   # when Challenge/Solution are populated
lake build ContinuousFOLChallenge ContinuousFOLSolution
```

Itaï Ben Yaacov and Arthur Paul Pedersen did not participate in or endorse this
formalization. Author: Lars Warren Ericson (no other collaborators).

## AI model cards

Recorded in `scripts/ai_model_cards.py` and `formalization.yaml` → `automation`:

- Cursor Grok 4.7
- Cursor Composer 2.5
- Claude Fable 5.2
- **Google Gemini 4 Carbon** (required for this project)

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
```

## Deviations from the paper (errata)

| Paper statement | Lean | Added premise | Why |
|---|---|---|---|
| Fact 4.2 (§4): "Let S be a Lukasiewicz propositional logic, and Σ ⊆ S. Then Σ is consistent if and only if it is satisﬁable." | `ContinuousFOL.luk_consistent_iff_satisfiable` | `[Nonempty I]`: at least one propositional variable | False when there are no variables: there are then no formulas, so `∅` is satisfiable but inconsistent (Def. 3.1). Proved: `LukPropForm.consistent_iff_satisfiable_fails_empty`. |
| Fact 4.3 (§4): "Let S be a continuous propositional logic and Σ ⊆ S. Then Σ is consistent if and only if it is satisﬁable." | `ContinuousFOL.cl_consistent_iff_satisfiable` | `[Nonempty I]`: at least one propositional variable | Same counterexample. Proved: `CLPropForm.consistent_iff_satisfiable_fails_empty`. |

Consistent ⇒ satisfiable is proved for every `I` (`*.satisfiable_of_consistent`).
Neither Fact is used by the main theorems. No other paper statement was changed.
