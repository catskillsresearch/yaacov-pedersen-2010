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

```bash
python3 scripts/build_holes.py   # refreshes HOLES.md / holes-graph.json / holes.html
```
