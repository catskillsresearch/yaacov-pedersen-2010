#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Locate verbatim paper quotations for Lean `Paper:` ascriptions.

Source of truth: ``sources/yaacov_pedersen_2010_vision.md`` (vision transcription of the
arXiv preprint arXiv:0903.4051v1, 26 pages, ``<!-- page N -->`` markers; page
labels below are arXiv page numbers, not JSL journal pages).  Quotes are
*cut* from that file, never written by hand:

1. an equation number ``(4.4)`` / ``(5.9b)`` → the display carrying ``\\tag{…}``
   plus the prose paragraph that introduces it;
2. otherwise a named result (Theorem / Lemma / Proposition / Remark / Corollary /
   Table ``N.M``) → the paragraph that starts with its bold label, plus any
   directly following italic/display continuation of the statement;
3. otherwise an entry in ``scripts/paper_quote_anchors.json`` giving verbatim
   ``start`` / ``end`` substrings of the transcription (checked to exist);
4. otherwise the ascription is reported as *unresolved* (no quote is produced).

Used by ``scripts/scaffold_continuousfol_writeup.py`` to write ``*_math.txt``.
Run directly to print the resolution report for every module.
"""

from __future__ import annotations

import json
import re
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
VISION = ROOT / "sources" / "yaacov_pedersen_2010_vision.md"
ANCHORS = ROOT / "scripts" / "paper_quote_anchors.json"
# The source PDF is the arXiv preprint; OCR page index = arXiv page number.
PAGE_OFFSET = 0

_JUNK_RE = re.compile(r"<｜[^｜]*｜>")
_RUNNING_HEADERS = {
    "A proof of completeness for continuous first-order logic",
    "A PROOF OF COMPLETENESS FOR CONTINUOUS FIRST-ORDER LOGIC",
    "ITAÏ BEN YAACOV AND ARTHUR PAUL PEDERSEN",
    "ITAI BEN YAACOV AND ARTHUR PAUL PEDERSEN",
}
_EQ_RE = re.compile(r"\((\d\.\d+[ab]?)\)")
_NAMED_RE = re.compile(
    r"\b(Theorem|Thm\.?|Lemma|Proposition|Prop\.|Remark|Corollary|Table)\s*(\d+(?:\.\d+)?)",
)
_NAME_CANON = {
    "Thm": "Theorem",
    "Thm.": "Theorem",
    "Prop.": "Proposition",
}


@dataclass
class Unit:
    text: str
    page: int  # vision page
    display: bool


def _load_units() -> list[Unit]:
    units: list[Unit] = []
    page = 0
    buf: list[str] = []
    buf_page = 0
    in_display = False

    def flush() -> None:
        nonlocal buf
        body = "\n".join(buf).strip()
        if body:
            disp = body.startswith("$$")
            units.append(Unit(body, buf_page, disp))
        buf = []

    for raw in VISION.read_text(encoding="utf-8").splitlines():
        line = _JUNK_RE.sub("", raw).rstrip()
        m = re.match(r"<!--\s*page\s+(\d+)\s*-->", line.strip())
        if m:
            if not in_display:
                flush()
            page = int(m.group(1))
            continue
        if line.strip() in _RUNNING_HEADERS or line.strip() == "---" or re.match(
            r"^\*\*A proof of completeness for continuous first-order logic\*\*", line.strip()
        ):
            continue
        if line.strip() == "$$":
            if not in_display:
                flush()
                buf_page = page
                buf.append(line)
                in_display = True
            else:
                buf.append(line)
                in_display = False
                flush()
            continue
        if in_display:
            buf.append(line)
            continue
        if not line.strip():
            flush()
            continue
        if not buf:
            buf_page = page
        buf.append(line)
    flush()
    return units


_UNITS: list[Unit] | None = None


def units() -> list[Unit]:
    global _UNITS
    if _UNITS is None:
        _UNITS = _load_units()
    return _UNITS


def _fix_tags(text: str) -> str:
    # `\tag` is illegal inside `aligned`; keep the number visibly instead.
    return re.sub(r"\\tag\{([^}]*)\}", r"\\qquad\\text{(\1)}", text)


def _is_prose(u: Unit) -> bool:
    return not u.display and not u.text.startswith("#") and not u.text.startswith("|")


def _by_equation(tags: list[str]) -> tuple[list[int], str] | None:
    us = units()
    idxs: list[int] = []
    for tag in tags:
        for i, u in enumerate(us):
            if u.display and f"\\tag{{{tag}}}" in u.text:
                if i not in idxs:
                    if not idxs and i > 0 and _is_prose(us[i - 1]):
                        idxs.append(i - 1)
                    idxs.append(i)
                break
    if not idxs:
        return None
    return idxs, ", ".join(f"({t})" for t in tags)


def _by_name(kind: str, num: str) -> tuple[list[int], str] | None:
    kind = _NAME_CANON.get(kind, kind)
    us = units()
    pat = re.compile(rf"^(\*\*|\*){kind}\s+{re.escape(num)}\.?(\*\*|\*)")
    for i, u in enumerate(us):
        if pat.match(u.text):
            idxs = [i]
            j = i + 1
            while j < len(us) and len(idxs) < 8:
                t = us[j].text
                if us[j].display or (t.startswith("*") and not t.startswith("**")) or (
                    kind == "Table" and t.startswith("|")
                ):
                    if t.startswith("*Proof"):
                        break
                    idxs.append(j)
                    j += 1
                    continue
                break
            return idxs, f"{kind} {num}"
    return None


def _load_anchors() -> dict[str, dict[str, str]]:
    if ANCHORS.is_file():
        return json.loads(ANCHORS.read_text(encoding="utf-8"))
    return {}


def _by_anchor(spec: dict[str, str]) -> tuple[list[int], str] | None:
    us = units()
    start, end = spec["start"], spec.get("end", spec["start"])
    i0 = next((i for i, u in enumerate(us) if start in u.text), None)
    if i0 is None:
        raise SystemExit(f"paper_quote_anchors.json: start anchor not found: {start!r}")
    i1 = next((i for i in range(i0, len(us)) if end in us[i].text), None)
    if i1 is None:
        raise SystemExit(f"paper_quote_anchors.json: end anchor not found: {end!r}")
    return list(range(i0, i1 + 1)), spec.get("label", "")


@dataclass
class Quote:
    title: str
    body: str


def resolve(module: str, ascription: str) -> tuple[Quote | None, str]:
    """Return (quote, how) for one ascription; quote is None when unresolved."""
    anchors = _load_anchors()
    hit = None
    how = ""
    for key, spec in anchors.items():
        mod, _, prefix = key.partition("|")
        if mod == module and ascription.startswith(prefix):
            hit = _by_anchor(spec)
            how = "anchor"
            break
    if hit is None:
        # Equation numbers win over result names ("Theorem 4.1 identity (4.4)").
        loc = re.split(r"(?<=[^.])[:](?=\s)", ascription, maxsplit=1)[0]
        tags = []
        for m in _EQ_RE.finditer(loc):
            if m.group(1) not in tags:
                tags.append(m.group(1))
        # Expand en-dash ranges such as (5.7)–(5.8): both ends are listed already.
        if tags:
            hit = _by_equation(tags)
            how = "equation"
        if hit is None:
            nm = _NAMED_RE.search(loc)
            if nm:
                hit = _by_name(nm.group(1), nm.group(2))
                how = "named"
    if hit is None:
        return None, "unresolved"
    idxs, label = hit
    us = units()
    pages = sorted({PAGE_OFFSET + us[i].page for i in idxs})
    ptxt = f"p. {pages[0]}" if len(pages) == 1 else f"pp. {pages[0]}–{pages[-1]}"
    title = f"Ben Yaacov–Pedersen (2010), arXiv {ptxt}" + (f", {label}" if label else "")
    body = "\n\n".join(_fix_tags(us[i].text) for i in idxs)
    return Quote(title, body), how


GREEN_DIV = (
    '<div class="sourcequote" style="border:1px solid #2f7d57; background:#eef7f1; '
    'border-radius:4px; padding:0.1em 0.9em; margin:0.7em 0;">'
)


def format_quotes(quotes: list[Quote]) -> str:
    """Markdown for `*_math.txt`: one green box per quote, title = source location.

    The HTML wrapper gives the green box in Markdown previews; the TeX pipeline
    (``build_arxiv_tex.py``) drops the wrapper and renders a ``sourcequote``
    tcolorbox titled by the bold first line.
    """
    parts: list[str] = []
    seen: set[str] = set()
    kept: list[Quote] = []
    for q in quotes:
        # Skip a quote already contained in a longer one for the same module.
        if any(q.body in k.body for k in kept) or (q.title + q.body) in seen:
            continue
        kept = [k for k in kept if k.body not in q.body]
        kept.append(q)
        seen.add(q.title + q.body)
    for q in kept:
        parts.append(f"{GREEN_DIV}\n\n**{q.title}**\n\n{q.body}\n\n</div>\n")
    return "\n".join(parts)


def main() -> int:
    import sys

    sys.path.insert(0, str(ROOT / "scripts"))
    from scaffold_continuousfol_writeup import extract_paper_blocks  # type: ignore

    n = ok = 0
    for p in sorted((ROOT / "ContinuousFOL").rglob("*.lean")):
        for asc, _ in extract_paper_blocks(p.read_text(encoding="utf-8")):
            n += 1
            q, how = resolve(p.stem, asc)
            if q:
                ok += 1
                print(f"OK   {p.stem}: {asc[:70]}  →  {q.title} [{how}]")
            else:
                print(f"MISS {p.stem}: {asc[:110]}")
    print(f"resolved {ok}/{n}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
