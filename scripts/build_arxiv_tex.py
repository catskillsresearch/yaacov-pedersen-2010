#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
r"""Convert arxiv_with_code.md to arxiv.tex (arXiv-ready).

Pipeline:
  1. Drop the GitHub-only navigation preamble (auto-gen note, document map, file index).
  2. Lift the `## Abstract` section into a LaTeX \begin{abstract}.
  3. Demote the Appendix-A structural headings so LaTeX numbers everything once, then
     insert \\appendix before the combined Lean-source appendix.
  4. Strip manual section numbers (any depth, e.g. `1.`, `1.3`, `5.1`) so LaTeX does
     the numbering and we never get duplicates like "5.1 5.1".
  5. Replace fenced code with \\lstinputlisting blocks (ASCII-sanitized for arXiv pdfLaTeX).
  5b. Render ```mermaid blocks to PNG via mermaid-cli (mmdc) for arXiv pdfLaTeX.
  6. pandoc → LaTeX, then splice the listing/math/figure placeholders back in.
    Model acknowledgements and BibTeX keys live in the note tree / references.bib.
"""

from __future__ import annotations

import os
import re
import shutil
import subprocess
import sys
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCRIPTS = Path(__file__).resolve().parent
sys.path.insert(0, str(SCRIPTS))
from lean_listing_sanitize import chunk_line_ranges, sanitize_lean_for_arxiv

SRC = ROOT / "arxiv_with_code.md"
OUT = ROOT / "arxiv.tex"
PREAMBLE = SCRIPTS / "tex_preamble_arxiv.tex"
LISTINGS_DIR = ROOT / "lean-listings"
FIGURES_DIR = ROOT / "figures"
PUPPETEER_CONFIG = SCRIPTS / "puppeteer-config.json"
LISTING_CHUNK_LINES = 400

AUTHOR = "Lars Warren Ericson"
COMPANY = "Catskills Research Company"
GITHUB_URL = r"https://github.com/catskillsresearch/yaacov-pedersen-2010"
# Palomar registry entry: TBD (this project is not registered yet). Set to the
# entry URL once registered; until then the title page shows "TBD".
PALOMAR_URL = ""
ORCID = "0000-0001-8299-9361"
EMAIL = "lars.ericson@catskillsresearch.com"


def find_chrome() -> str | None:
    env = os.environ.get("PUPPETEER_EXECUTABLE_PATH")
    if env and Path(env).exists():
        return env
    for name in ("google-chrome", "google-chrome-stable", "chromium", "chromium-browser"):
        path = shutil.which(name)
        if path:
            return path
    return None


def render_mermaid(code: str, idx: int) -> str:
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    mmd_path = FIGURES_DIR / f"figure-{idx:03d}.mmd"
    png_path = FIGURES_DIR / f"figure-{idx:03d}.png"
    mmd_path.write_text(code.strip() + "\n", encoding="utf-8")

    mmdc = shutil.which("mmdc")
    if not mmdc:
        raise RuntimeError(
            "mermaid-cli (mmdc) not found; install with "
            "`npm install -g @mermaid-js/mermaid-cli`"
        )
    env = os.environ.copy()
    chrome = find_chrome()
    if chrome:
        env["PUPPETEER_EXECUTABLE_PATH"] = chrome
    cmd = [mmdc, "-i", str(mmd_path), "-o", str(png_path), "-b", "white"]
    if PUPPETEER_CONFIG.is_file():
        cmd += ["-p", str(PUPPETEER_CONFIG)]
    proc = subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)
    if proc.returncode != 0 or not png_path.is_file():
        sys.stderr.write(proc.stdout + "\n" + proc.stderr + "\n")
        raise RuntimeError(f"mmdc failed to render figure {idx}")
    return png_path.relative_to(ROOT).as_posix()


def extract_title() -> str:
    # One source of truth for the PDF title, shared with the Markdown root.
    root = ROOT / "ContinuousFOL.md"
    for line in root.read_text(encoding="utf-8").splitlines():
        if line.startswith("# "):
            return line[2:].strip()
    return "Formalization of Completeness for Continuous First-Order Logic"


TITLE = extract_title()

GITHUB_INLINE_MATH = re.compile(r"\$`([^`\n]+?)`\$")
HTML_COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
FENCE_RE = re.compile(r"^```([^\n]*)\n(.*?)^```\s*$", re.MULTILINE | re.DOTALL)
MANUAL_SECTION_NUM = re.compile(r"^(#{1,6})[ \t]+\d+(?:\.\d+)*\.?[ \t]+", re.MULTILINE)
NARRATIVE_MARKER = "# Narrative (from arxiv.md)"
LEAN_MODULE_RE = re.compile(
    r"^###\s+(ContinuousFOL(?:\.lean|/[^\s{]+))\s*$",
    re.MULTILINE,
)
FIGURE_CAPTION_RE = re.compile(
    r"<!--\s*figure-caption:\s*(.*?)\s*-->\s*\n```mermaid",
    re.IGNORECASE | re.DOTALL,
)


def github_math_to_tex(text: str) -> str:
    return GITHUB_INLINE_MATH.sub(r"$\1$", text)


# Notes use pandoc citation syntax (`[@key]`, `[@a; @b]`, `[@key, pp. 1-2]`).
_PANDOC_CITE_RE = re.compile(
    r"\["
    r"("
    r"@[A-Za-z][\w\-]*(?:\s*,\s*[^;\]]+)?"
    r"(?:\s*;\s*@[A-Za-z][\w\-]*(?:\s*,\s*[^;\]]+)?)*"
    r")"
    r"\]"
)


def pandoc_cites_to_latex_cite(text: str) -> str:
    """Rewrite pandoc ``[@…]`` citations to ``\\cite{…}`` for BibTeX."""

    def repl(m: re.Match[str]) -> str:
        body = m.group(1).strip()
        parts = [p.strip() for p in body.split(";") if p.strip()]
        keys: list[str] = []
        opt: str | None = None
        for i, part in enumerate(parts):
            if not part.startswith("@"):
                return m.group(0)
            rest = part[1:].strip()
            if i == 0 and "," in rest:
                key, _, locator = rest.partition(",")
                keys.append(key.strip())
                locator = locator.strip()
                if locator:
                    loc = locator
                    loc = re.sub(r"\bpp\.\s*", "pp.~", loc)
                    loc = re.sub(r"(?<!\w)\bp\.\s*", "p.~", loc)
                    loc = loc.replace("§ ", "$\\S$~").replace("§", "$\\S$")
                    loc = re.sub(r"(\d)-(\d)", r"\1--\2", loc)
                    loc = loc.replace("~~", "~")
                    opt = loc
            else:
                keys.append(rest.split(",", 1)[0].strip())
        if not keys:
            return m.group(0)
        key_str = ",".join(keys)
        if opt:
            return f"\\cite[{opt}]{{{key_str}}}"
        return f"\\cite{{{key_str}}}"

    return _PANDOC_CITE_RE.sub(repl, text)


def strip_html_comments(text: str) -> str:
    return HTML_COMMENT.sub("", text)


def strip_manual_section_numbers(text: str) -> str:
    return MANUAL_SECTION_NUM.sub(r"\1 ", text)


def drop_github_nav(text: str) -> str:
    idx = text.find(NARRATIVE_MARKER)
    if idx == -1:
        return text
    return text[idx + len(NARRATIVE_MARKER) :].lstrip("\n")


def normalize_appendix_headings(text: str) -> str:
    text = re.sub(
        r"^#\s+Appendix A: (?:Complete Lean source|Lean module index)\s*$",
        "## Complete Lean source",
        text,
        flags=re.MULTILINE,
    )
    text = re.sub(
        r"^##\s+`(ContinuousFOL(?:\.lean|/[^`]+))`\s*$",
        r"### \1",
        text,
        flags=re.MULTILINE,
    )
    return text


def extract_abstract(text: str) -> tuple[str, str]:
    m = re.search(r"^##\s+Abstract\s*\n(.*?)(?=^##\s)", text, re.DOTALL | re.MULTILINE)
    if not m:
        return "", text
    abstract_md = m.group(1).strip()
    body = text[: m.start()] + text[m.end() :]
    return abstract_md, body


def strip_lean_copyright(code: str) -> str:
    """Drop the leading ``/- Copyright … -/`` block from Lean listings."""
    text = code.lstrip("\n")
    if not text.startswith("/-"):
        return code
    end = text.find("-/")
    if end == -1:
        return code
    header = text[: end + 2]
    if "Copyright" not in header:
        return code
    return text[end + 2 :].lstrip("\n")


def write_listing(code: str, listing_name: str) -> tuple[str, int]:
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)
    source = sanitize_lean_for_arxiv(
        strip_lean_copyright(code).rstrip("\n"), source_name=listing_name
    )
    listing_path = LISTINGS_DIR / listing_name
    listing_path.write_text(source + "\n", encoding="utf-8")
    rel_path = listing_path.relative_to(ROOT).as_posix()
    return rel_path, (len(source.splitlines()) if source else 0)


def embed_lstlean(preamble: str) -> str:
    """Inline ``\\input{lstlean}`` so the assembled ``arxiv.tex`` is self-contained."""
    marker = "\\input{lstlean}"
    if marker not in preamble:
        return preamble
    lstlean_path = SCRIPTS / "lstlean.tex"
    if not lstlean_path.is_file():
        raise FileNotFoundError(f"missing {lstlean_path} (required by tex preamble)")
    return preamble.replace(marker, lstlean_path.read_text(encoding="utf-8"))


# Bold first line of a ```source``` / `*_math.txt` block, e.g.
# **Ben Yaacov–Pedersen (2010), arXiv p. 3, Definition 2.1 (paraphrase)**
_SOURCE_HEADER_RE = re.compile(
    r"^\*\*((?:Ben Yaacov|Lyasoff|Nowakowska)\b.*?)\*\*\s*$",
)

_DEFAULT_SOURCE_TITLE = r"Ben Yaacov--Pedersen, \emph{J. Symbolic Logic} (2010)"


def _is_source_header(stripped: str) -> bool:
    return bool(_SOURCE_HEADER_RE.match(stripped))


def source_header_to_title(header: str) -> str:
    """Turn a bold ascription header into a ``sourcequote`` box title."""
    m = _SOURCE_HEADER_RE.match(header.strip())
    if not m:
        return _DEFAULT_SOURCE_TITLE
    title = m.group(1).strip()
    title = title.replace("–", "--").replace("—", "---")
    title = re.sub(r"\bpp\.\s*", "pp.~", title)
    title = re.sub(r"\bp\.\s*", "p.~", title)
    # Light TeX escaping for specials in titles.
    esc = {
        "\\": "\\textbackslash{}", "&": "\\&", "%": "\\%", "#": "\\#",
        "_": "\\_", "{": "\\{", "}": "\\}", "^": "\\^{}", "$": "\\$",
        "~": "\\textasciitilde{}",
    }
    # Escape character-by-character, keeping the "p.~" ties inserted above.
    out: list[str] = []
    i = 0
    while i < len(title):
        if title.startswith(".~", i):
            out.append(".~")
            i += 2
            continue
        out.append(esc.get(title[i], title[i]))
        i += 1
    return "".join(out)


_LONGTABLE_RE = re.compile(
    r"(?:\{\\def\\LTcaptype\{none\}[^\n]*\n)?"
    r"\\begin\{longtable\}\[[^\]]*\]\{(?P<spec>[^\n]*)\}\n(?P<body>.*?)\\end\{longtable\}\n?\}?",
    re.DOTALL,
)


def _longtable_to_tabular(latex: str) -> str:
    """longtable cannot live inside a tcolorbox; rewrite pandoc's longtables as
    centred tabulars (head kept once, the last-foot rule moved to the end)."""

    def repl(m: re.Match[str]) -> str:
        body = m.group("body")
        foot = ""
        if "\\endlastfoot" in body:
            pre, post = body.split("\\endlastfoot", 1)
            # pre = head ... \endhead foot-rows
            if "\\endhead" in pre:
                head, foot = pre.split("\\endhead", 1)
            else:
                head, foot = pre, ""
            if "\\endfirsthead" in head:
                head = head.split("\\endfirsthead", 1)[0]
            body = head + post
        else:
            body = re.sub(r"\\end(?:first)?head|\\end(?:last)?foot", "", body)
        return (
            "\\begin{center}\n\\begin{tabular}{" + m.group("spec") + "}\n"
            + body.strip("\n") + "\n" + foot.strip("\n") + "\n"
            + "\\end{tabular}\n\\end{center}"
        )

    return _LONGTABLE_RE.sub(repl, latex)


def _one_sourcequote(title: str, body: str) -> str:
    if not body.endswith("\n"):
        body += "\n"
    inner = pandoc_to_latex(body, shift=False)
    inner = cleanup_pandoc_latex(inner).strip()
    inner = _longtable_to_tabular(inner)
    return f"\\begin{{sourcequote}}{{{title}}}\n{inner}\n\\end{{sourcequote}}\n"


def source_block_latex(markdown: str) -> str:
    """Render paper ascriptions as green ``sourcequote`` boxes (one per bold header)."""
    # Drop the markdown-preview <div class="sourcequote" ...> wrappers emitted by
    # scripts/paper_quotes.py; the tcolorbox is the LaTeX equivalent.
    text = "\n".join(
        ln for ln in markdown.splitlines()
        if not re.match(r"^\s*</?div\b[^>]*>\s*$", ln)
    ).strip() + "\n"
    lines = text.splitlines()
    chunks: list[tuple[str | None, list[str]]] = []
    current_header: str | None = None
    current_body: list[str] = []
    for line in lines:
        stripped = line.strip()
        if _is_source_header(stripped):
            if current_header is not None or any(s.strip() for s in current_body):
                chunks.append((current_header, current_body))
            current_header = stripped
            current_body = []
        else:
            current_body.append(line)
    if current_header is not None or any(s.strip() for s in current_body):
        chunks.append((current_header, current_body))

    if not chunks:
        return _one_sourcequote(_DEFAULT_SOURCE_TITLE, text)

    parts: list[str] = []
    for header, body_lines in chunks:
        title = (
            source_header_to_title(header) if header else _DEFAULT_SOURCE_TITLE
        )
        body = "\n".join(body_lines).strip("\n") + "\n"
        parts.append(_one_sourcequote(title, body))
    return "\n".join(parts)

def lean_block_latex(code: str, listing_name: str) -> str:
    rel_path, line_count = write_listing(code, listing_name)
    ranges = chunk_line_ranges(line_count, LISTING_CHUNK_LINES)

    parts: list[str] = []
    for first, last in ranges:
        if first == 1 and last == line_count:
            parts.append(f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n")
        else:
            # Continuation header for long modules split into chunks (scott1964 style).
            parts.append(
                f"\\noindent\\textcolor{{green!40!black}}{{\\textbf{{Lean 4 source "
                f"(lines {first}--{last})}}}}\\par\\vspace{{0.25\\baselineskip}}\n"
                f"\\lstinputlisting[style=leanbox,firstline={first},lastline={last}]"
                f"{{{rel_path}}}\n"
            )
    return "".join(parts)


def parse_figure_captions(text: str) -> list[str]:
    return [m.group(1).strip() for m in FIGURE_CAPTION_RE.finditer(text)]


def escape_latex_caption(text: str) -> str:
    out: list[str] = []
    for ch in text:
        if ch in "&%$#_{}":
            out.append(f"\\{ch}" if ch != "}" else "\\}")
        elif ch == "~":
            out.append(r"\textasciitilde{}")
        elif ch == "^":
            out.append(r"\textasciicircum{}")
        elif ch == "\\":
            out.append(r"\textbackslash{}")
        else:
            out.append(ch)
    return "".join(out)


def extract_lean_titles(text: str) -> dict[str, str]:
    titles: dict[str, str] = {}
    lean_starts = [m.start() for m in re.finditer(r"^```lean\s*$", text, re.MULTILINE)]
    for idx, pos in enumerate(lean_starts):
        prefix = text[:pos].rstrip("\n")
        module = None
        for line in reversed(prefix.splitlines()[-4:]):
            m = re.match(
                r"^###\s+(ContinuousFOL(?:\.lean|/[^\s{]+))",
                line.strip(),
            )
            if m:
                module = m.group(1)
                break
        titles[f"LEANINCLUDE{idx:03d}"] = module or f"module-{idx + 1}"
    return titles


def replace_fences(text: str, figure_captions: list[str]) -> tuple[str, dict[str, str]]:
    lean_titles = extract_lean_titles(text)
    placeholders: dict[str, str] = {}
    lean_idx = 0
    other_idx = 0
    figure_idx = 0

    def repl(match: re.Match[str]) -> str:
        nonlocal lean_idx, other_idx, figure_idx
        lang = match.group(1).strip().lower()
        body = match.group(2)
        if lang == "source":
            key = f"SOURCEINCLUDE{other_idx:03d}"
            other_idx += 1
            placeholders[key] = source_block_latex(body)
            return f"\n\n{key}\n\n"
        if lang == "lean":
            key = f"LEANINCLUDE{lean_idx:03d}"
            module = lean_titles.get(key, f"module-{lean_idx}")
            lean_idx += 1
            safe_name = module.replace("/", "-")
            if not safe_name.endswith(".lean"):
                safe_name += ".lean"
            placeholders[key] = lean_block_latex(body, safe_name)
            return f"\n\n{key}\n\n"
        if lang == "math":
            key = f"MATHINCLUDE{other_idx:03d}"
            other_idx += 1
            placeholders[key] = f"\\[\n{body.strip()}\n\\]\n"
            return f"\n\n{key}\n\n"
        if lang == "latex":
            key = f"LATEXINCLUDE{other_idx:03d}"
            other_idx += 1
            placeholders[key] = body.strip() + "\n"
            return f"\n\n{key}\n\n"
        if lang == "mermaid":
            key = f"FIGINCLUDE{other_idx:03d}"
            rel_path = render_mermaid(body, figure_idx)
            if figure_idx < len(figure_captions):
                caption = figure_captions[figure_idx]
            else:
                caption = f"Dependency diagram {figure_idx + 1}."
            label = f"fig:scott2026-{figure_idx + 1:02d}"
            figure_idx += 1
            other_idx += 1
            cap = escape_latex_caption(caption)
            placeholders[key] = (
                "\\begin{figure}[htbp]\n\\centering\n"
                f"\\includegraphics[max width=\\linewidth,"
                f"max totalheight=0.85\\textheight,keepaspectratio]{{{rel_path}}}\n"
                f"\\caption{{{cap}}}\n"
                f"\\label{{{label}}}\n"
                "\\end{figure}\n"
            )
            return f"\n\n{key}\n\n"
        key = f"CODEINCLUDE{other_idx:03d}"
        rel_path, _ = write_listing(body, f"snippet-{other_idx:03d}.txt")
        other_idx += 1
        placeholders[key] = f"\\lstinputlisting[style=leanbox]{{{rel_path}}}\n"
        return f"\n\n{key}\n\n"

    converted = FENCE_RE.sub(repl, text)
    return converted, placeholders


def pandoc_to_latex(markdown: str, shift: bool = True) -> str:
    cmd = [
        "pandoc",
        "-f",
        "markdown+tex_math_dollars+raw_tex+smart",
        "-t",
        "latex",
        "--wrap=none",
    ]
    if shift:
        cmd += ["--shift-heading-level-by=-1"]
    proc = subprocess.run(cmd, input=markdown, text=True, capture_output=True, check=False)
    if proc.returncode != 0:
        print(proc.stderr, file=sys.stderr)
        raise RuntimeError("pandoc failed")
    return proc.stdout


def inject_placeholders(latex: str, placeholders: dict[str, str]) -> str:
    out = latex
    for key, value in placeholders.items():
        patterns = [
            key,
            f"\\emph{{{key}}}",
            f"\\text{{{key}}}",
            f"\\passthrough{{\\lstinline!{key}!}}",
        ]
        for pat in patterns:
            if pat in out:
                out = out.replace(pat, value)
                break
        else:
            out = out.replace(key, value)
    return out


def break_long_alnum(text: str, width: int = 10) -> str:
    """Insert allowbreaks inside long unbroken words (e.g. Negligibility).

    CamelCase tokens are left alone; they get structural breaks later.
    """

    def chunk(match: re.Match[str]) -> str:
        token = match.group(0)
        if len(token) <= width:
            return token
        # Leave CamelCase / acronyms for the structural pass.
        if re.search(r"[a-z][A-Z]", token) or re.search(r"[A-Z]{2,}[a-z]", token):
            return token
        parts = [token[i : i + width] for i in range(0, len(token), width)]
        return "\\allowbreak{}".join(parts)

    return re.sub(r"[A-Za-z0-9]{%d,}" % (width + 1), chunk, text)


def break_path_text(inner: str, *, chunk_long: bool = False) -> str:
    """Allow line breaks in repository-relative Lean paths."""
    # Chunk long tokens first so later ``\allowbreak`` commands are not
    # themselves matched as alphanumeric runs.
    if chunk_long:
        inner = break_long_alnum(inner)
    inner = inner.replace("/", "/\\allowbreak{}")
    inner = inner.replace(r"\_", r"\_\allowbreak{}")
    inner = re.sub(r"(?<=[a-z])(?=[A-Z])", r"\\allowbreak{}", inner)
    inner = re.sub(r"(?<=[A-Z])(?=[A-Z][a-z])", r"\\allowbreak{}", inner)
    inner = inner.replace(".lean", ".\\allowbreak{}lean")
    inner = re.sub(r"\.(?=[A-Za-z])", r".\\allowbreak{}", inner)
    return inner


def break_texttt_paths(latex: str) -> str:
    """Allow line breaks after `/` and `_` in \\texttt paths and identifiers."""

    def fix(match: re.Match[str]) -> str:
        return "\\texttt{" + break_path_text(match.group(1)) + "}"

    return re.sub(r"\\texttt\{([^{}]*)\}", fix, latex)


def break_lean_path_headings(latex: str) -> str:
    """Breakable appendix subsection titles that are Lean paths.

    Avoid ``\\par`` / ``\\raggedright`` here: pandoc wraps headings in
    ``\\hypertarget{...}{...}``, which cannot contain ``\\par``.
    """

    def fix(match: re.Match[str]) -> str:
        raw = match.group(2)
        broken = break_path_text(raw, chunk_long=True)
        plain = raw.replace(r"\_", "_").replace(r"\allowbreak{}", "")
        return (
            f"{match.group(1)}"
            f"\\texorpdfstring{{{broken}}}{{{plain}}}"
            f"{match.group(3)}"
        )

    return re.sub(
        r"(\\(?:sub)*section\{)(ContinuousFOL(?:\.lean|/[^{}]+))(\})",
        fix,
        latex,
    )


def cleanup_pandoc_latex(latex: str) -> str:
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n?", "", latex)
    # Keep overview / note diagrams under their section titles (no float drift).
    latex = re.sub(r"\\begin\{figure\}(?!\[)", r"\\begin{figure}[H]", latex)
    latex = re.sub(r"\\begin\{figure\}\[[^\]]*\]", r"\\begin{figure}[H]", latex)
    # Note-tree figures (vector PDF from Graphviz, or high-DPI PNG fallback):
    # keep natural size so labels stay near body text; only cap wide diagrams.
    latex = re.sub(
        r"\\includegraphics\{(figures/[^}]+\.(?:pdf|png|jpe?g))\}",
        r"\\includegraphics[max width=0.92\\linewidth,keepaspectratio]{\1}",
        latex,
        flags=re.IGNORECASE,
    )
    # Drop duplicate Lean path paragraph headings (the blue \\href is enough).
    latex = re.sub(
        r"\\hypertarget\{[^\n]*\}\{%\n\\(?:sub)*paragraph\{ContinuousFOL[^\n]*\}\\label\{[^\n]*\}\}\n*",
        "",
        latex,
    )
    # Blue Lean path link: noindent, flush against the following listing.
    def _lean_href(m: re.Match[str]) -> str:
        # Blank line before the path (\\parskip is 0, so \\medskip is required),
        # flush left, then listing with no gap under the link.
        return (
            f"\\medskip\\noindent\\textbf{{\\href{{{m.group(1)}}}{{{m.group(2)}}}}}"
            f"\\\\*\\nopagebreak\n"
            f"\\lstinputlisting[style=leanbox,aboveskip=0pt,belowskip=0.5\\baselineskip]"
        )

    latex = re.sub(
        r"\\textbf\{\\href\{([^}]*)\}\{(ContinuousFOL[^}]*)\}\}\s*"
        r"\\lstinputlisting\[style=leanbox\]",
        _lean_href,
        latex,
    )
    latex = break_texttt_paths(latex)
    latex = break_lean_path_headings(latex)
    for cmd in ("section", "subsection", "subsubsection", "paragraph"):
        latex = re.sub(
            rf"(\\{cmd}\{{)\d+(?:\.\d+)*\.?\s+",
            r"\1",
            latex,
        )
    latex = re.sub(
        r"\\section\{Appendix A\. Lean source index\}",
        "",
        latex,
    )
    latex = re.sub(
        r"\\section\{Appendix A: (?:Complete Lean source|Lean module index)\}",
        r"\\section{Complete Lean source}",
        latex,
    )
    latex = re.sub(
        r"\\section\{Appendix A\. (?:Complete Lean source|Lean module index)\}",
        r"\\section{Complete Lean source}",
        latex,
    )
    latex = re.sub(
        r"\\section\{Lean module index\}",
        r"\\section{Complete Lean source}",
        latex,
    )
    latex = re.sub(r"\n{3,}", "\n\n", latex)
    return latex


def insert_appendix_command(latex: str) -> str:
    marker = r"\section{Complete Lean source}"
    if marker not in latex:
        # Inline Lean formalization has no separate appendix dump.
        return latex
    # \sloppy lets long path subsection titles and listing lines wrap
    # instead of producing Overfull \hbox failures in the build gate.
    return latex.replace(
        marker,
        r"\appendix" + "\n" + r"\sloppy" + "\n" + marker,
        1,
    )


def cleanup_abstract_latex(latex: str) -> str:
    """Keep the abstract pdfLaTeX/arXiv-safe: ASCII plus standard LaTeX escapes."""
    latex = latex.replace("\\pandocbounded{", "{")
    latex = re.sub(r"\\tightlist\n?", "", latex)
    latex = latex.replace("\\textbf{{[}", "\\textbf{[")
    latex = latex.replace("\\texttt{{[}", "\\texttt{[")
    latex = latex.replace("{]}}", "]}")
    latex = re.sub(r"\\begin\{center\}\\rule\{.*?\}\\end\{center\}\s*", "", latex, flags=re.DOTALL)
    return latex


def build_title_page(abstract_latex: str) -> str:
    palomar_latex = f"\\url{{{PALOMAR_URL}}}" if PALOMAR_URL else "TBD"
    return textwrap.dedent(
        f"""
        \\title{{\\textbf{{{TITLE}}}}}

        \\author[1]{{\\textbf{{{AUTHOR}}}}}
        \\affil[1]{{{COMPANY}}}
        \\affil[1]{{\\url{{{GITHUB_URL}}}}}
        \\affil[1]{{\\texttt{{{EMAIL}}}}}

        \\date{{\\today}}

        \\begin{{document}}

        \\maketitle

        \\begin{{center}}
          \\small
          \\textbf{{ORCID:}} {ORCID} \\\\
          \\textbf{{Palomar Registration:}} {palomar_latex}
        \\end{{center}}

        \\begin{{abstract}}
        {abstract_latex.strip()}
        \\end{{abstract}}

        \\clearpage
        \\tableofcontents
        \\clearpage
        """
    ).strip()


def main() -> int:
    if not SRC.is_file():
        print(f"error: missing {SRC}; run scripts/generate_arxiv_with_code.sh first", file=sys.stderr)
        return 1
    if not PREAMBLE.is_file():
        print(f"error: missing {PREAMBLE}", file=sys.stderr)
        return 1

    if LISTINGS_DIR.exists():
        for path in LISTINGS_DIR.iterdir():
            if path.is_file():
                path.unlink()
    LISTINGS_DIR.mkdir(parents=True, exist_ok=True)
    FIGURES_DIR.mkdir(parents=True, exist_ok=True)
    # Keep SVG→PNG assets from compile_md_tree; only clear mermaid renders.
    for path in FIGURES_DIR.iterdir():
        if path.is_file() and (
            path.name.startswith("figure-") or path.suffix.lower() == ".mmd"
        ):
            path.unlink()

    raw = SRC.read_text(encoding="utf-8")
    body = drop_github_nav(raw)
    figure_captions = parse_figure_captions(body)
    body = strip_html_comments(body)
    body = normalize_appendix_headings(body)
    abstract_md, body = extract_abstract(body)
    body = strip_manual_section_numbers(body)
    body = github_math_to_tex(body)
    body, placeholders = replace_fences(body, figure_captions)
    body = pandoc_cites_to_latex_cite(body)
    if abstract_md:
        abstract_md = pandoc_cites_to_latex_cite(abstract_md)

    latex_body = pandoc_to_latex(body, shift=True)
    latex_body = inject_placeholders(latex_body, placeholders)
    latex_body = cleanup_pandoc_latex(latex_body)
    latex_body = insert_appendix_command(latex_body)
    # compile_md_tree emits the References heading; append a real BibTeX
    # bibliography there (natbib's bibsection is empty to avoid a second title).
    if "\\section{References}" not in latex_body:
        latex_body += "\n\\section{References}\n"
    latex_body += "\n\\nocite{*}\n\\bibliographystyle{plainnat}\n\\bibliography{references}\n"


    abstract_latex = pandoc_to_latex(github_math_to_tex(abstract_md), shift=False) if abstract_md else ""
    abstract_latex = cleanup_abstract_latex(abstract_latex)

    preamble = embed_lstlean(PREAMBLE.read_text(encoding="utf-8"))
    # Article chapters are top-level sections. Flush floats before every one,
    # including References, and put the anchor on the section's new page.
    latex_body = re.sub(
        r"(\\hypertarget\{[^\n]*\}\{%\n)(\\section\{)",
        r"\\clearpage\n\1\2", latex_body,
    )
    latex_body = re.sub(r"(?<!%\n)(?<!\\clearpage\n)(\\section\{)", r"\\clearpage\n\1", latex_body)
    preamble += "\n\\hypersetup{pdftitle={" + TITLE + "},pdfauthor={" + AUTHOR + "}}\n"
    title_page = build_title_page(abstract_latex)
    document = preamble + "\n\n" + title_page + "\n\n" + latex_body + "\n\n\\end{document}\n"
    # Combining macron (e.g. "z̄" in generated prose): pdfLaTeX cannot place a
    # combining glyph, so rewrite letter + U+0304 as a math bar.
    document = re.sub(r"([A-Za-z])\u0304", r"\\ensuremath{\\bar{\1}}", document)
    OUT.write_text(document, encoding="utf-8")
    n_listings = sum(1 for p in LISTINGS_DIR.iterdir() if p.is_file())
    n_figures = sum(1 for p in FIGURES_DIR.glob("*.png"))
    print(
        f"wrote {OUT.relative_to(ROOT)} ({OUT.stat().st_size:,} bytes, "
        f"{n_listings} listings, {n_figures} mermaid figures)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
