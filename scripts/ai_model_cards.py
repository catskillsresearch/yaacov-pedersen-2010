"""Model-card registry for AI-assisted development acknowledgements.

Injected into narrative / TeX builds at:
  <!-- AI_MODEL_TOOL_BULLETS --> … <!-- /AI_MODEL_TOOL_BULLETS -->

Keep this list aligned with `formalization.yaml` → `automation.methods`.
"""

from __future__ import annotations

import re
from dataclasses import dataclass


@dataclass(frozen=True)
class ModelCard:
    label: str
    cite_key: str
    tool_note: str
    bib_entry_type: str
    bib_fields: dict[str, str]


MODEL_CARDS: tuple[ModelCard, ...] = (
    ModelCard(
        label="Cursor Grok 4.7",
        cite_key="Grk47",
        tool_note=(
            "primary agent model for Lean 4 / Mathlib formalization, lake build "
            "repair, vision-OCR alignment, ContinuousFOL writeup, and Palomar "
            "packaging."
        ),
        bib_entry_type="misc",
        bib_fields={
            "author": "xAI and {Anysphere, Inc.}",
            "title": "Grok 4.7",
            "howpublished":
                "Model documentation, \\url{https://docs.x.ai/docs/models}; "
                "Cursor model catalog, \\url{https://cursor.com/docs/models}",
            "year": "2026",
            "note": "accessed 2026",
        },
    ),
    ModelCard(
        label="Cursor Composer 2.5",
        cite_key="Cmp25",
        tool_note=(
            "routine scaffolding and medium-complexity proof obligations where "
            "the strategy is already fixed (`composer-2.5`)."
        ),
        bib_entry_type="misc",
        bib_fields={
            "author": "{Anysphere, Inc.}",
            "title": "Composer 2.5",
            "howpublished":
                "Model announcement and documentation, "
                "\\url{https://cursor.com/blog/composer-2-5}; "
                "model card as integrated in Cursor, "
                "\\url{https://cursor.com/docs/models}",
            "year": "2026",
            "note": "accessed 2026",
        },
    ),
    ModelCard(
        label="Claude Fable 5.2",
        cite_key="Fab52",
        tool_note=(
            "substantive Lean repairs and larger proof obligations "
            "(`claude-fable-5-2`)."
        ),
        bib_entry_type="misc",
        bib_fields={
            "author": "{Anthropic} and {Anysphere, Inc.}",
            "title": "Claude Fable 5.2",
            "howpublished":
                "Model as integrated in Cursor, "
                "\\url{https://cursor.com/docs/models}",
            "year": "2026",
            "note": "accessed 2026",
        },
    ),
    ModelCard(
        label="Google Gemini 4 Carbon",
        cite_key="Gem4C",
        tool_note=(
            "agent and support passes for ContinuousFOL formalization "
            "(`gemini-4-carbon` / Gemini 4 Carbon in Cursor)."
        ),
        bib_entry_type="misc",
        bib_fields={
            "author": "{Google DeepMind} and {Anysphere, Inc.}",
            "title": "Gemini 4 Carbon",
            "howpublished":
                "Technical documentation and model cards, "
                "\\url{https://ai.google.dev/gemini-api/docs/models}; "
                "Cursor model catalog, \\url{https://cursor.com/docs/models}",
            "year": "2026",
            "note": "accessed 2026; required model card for this project",
        },
    ),
)

TOOL_BULLETS_BEGIN = "<!-- AI_MODEL_TOOL_BULLETS -->"
TOOL_BULLETS_END = "<!-- /AI_MODEL_TOOL_BULLETS -->"
REFERENCES_BEGIN = "<!-- AI_MODEL_REFERENCES -->"
REFERENCES_END = "<!-- /AI_MODEL_REFERENCES -->"

ACKNOWLEDGMENTS_MARKDOWN = r"""## Acknowledgments

### AI-assisted development

The human author retains sole responsibility for the mathematical content, the choice of
formalization route, and every formal claim in this work. Following standard publisher practice
(e.g., COPE guidance on authorship and AI tools [@COPE24]), **no large language model is listed
as a co-author** — authorship implies an accountability that automated systems cannot bear.

We gratefully acknowledge assistance from the following tools
(auto-generated from `scripts/ai_model_cards.py` when building `arxiv.tex`):

<!-- AI_MODEL_TOOL_BULLETS -->
<!-- /AI_MODEL_TOOL_BULLETS -->

All definitions and final prose were reviewed by the human author, who takes
full responsibility for them.

### Artifact availability and reproducibility

The development is at
[`github.com/catskillsresearch/yaacov-pedersen-2010`](https://github.com/catskillsresearch/yaacov-pedersen-2010).
GitHub Actions CI runs `lake build` on `main`.

Locally:

```bash
lake exe cache get
lake build ContinuousFOL
```

"""


def render_tool_bullets() -> str:
    return "\n".join(
        f"- **{card.label}** [@{card.cite_key}] — {card.tool_note}"
        for card in MODEL_CARDS
    )


def render_model_bibtex() -> str:
    blocks: list[str] = []
    for card in MODEL_CARDS:
        lines = [f"@{card.bib_entry_type}{{{card.cite_key},"]
        for key, value in card.bib_fields.items():
            lines.append(f"  {key} = {{{value}}},")
        lines.append("}")
        blocks.append("\n".join(lines))
    return "\n\n".join(blocks)


def inject_acknowledgments(text: str) -> str:
    if re.search(r"^##\s+Acknowledgments\s*$", text, re.MULTILINE):
        return text
    m = re.search(r"^##\s+References\s*$", text, re.MULTILINE)
    if not m:
        raise RuntimeError(
            "missing ## References in narrative; needed to place Acknowledgments before it"
        )
    return text[: m.start()] + ACKNOWLEDGMENTS_MARKDOWN + "\n" + text[m.start() :]


def inject_model_cards(text: str) -> str:
    text = inject_acknowledgments(text)
    if TOOL_BULLETS_BEGIN not in text:
        raise RuntimeError(
            f"missing {TOOL_BULLETS_BEGIN} after Acknowledgments injection"
        )
    text = _replace_between(text, TOOL_BULLETS_BEGIN, TOOL_BULLETS_END, render_tool_bullets())
    if REFERENCES_BEGIN in text and REFERENCES_END in text:
        text = _replace_between(text, REFERENCES_BEGIN, REFERENCES_END, "")
    return text


def _replace_between(text: str, begin: str, end: str, body: str) -> str:
    start = text.index(begin)
    stop = text.index(end, start)
    stop_end = stop + len(end)
    inner_start = start + len(begin)
    if inner_start < stop and text[inner_start : inner_start + 1] == "\n":
        inner_start += 1
    if inner_start < stop and text[stop - 1 : stop] == "\n":
        stop -= 1
    if body:
        return text[:start] + begin + "\n" + body + "\n" + end + text[stop_end:]
    return text[:start] + begin + "\n" + end + text[stop_end:]


if __name__ == "__main__":
    print(render_tool_bullets())
    print()
    print(render_model_bibtex())
