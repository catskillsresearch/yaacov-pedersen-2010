#!/usr/bin/env python3
# Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
"""Build holes-graph.json and HOLES.md for the ContinuousFOL proof-hole board.

Scans ContinuousFOL/**/*.lean for paper-facing theorems/lemmas, marks those whose
proof body contains a bare `sorry` (or residual `axiom`) as open, and wires hard
dependency edges from the Lean/paper order.
"""
from __future__ import annotations

import json
import re
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "ContinuousFOL"
OUT_JSON = ROOT / "holes-graph.json"
OUT_HTML = ROOT / "holes.html"
HTML_EMBED_MARKER = "/*HOLES_GRAPH_JSON*/"
OUT_MD = ROOT / "HOLES.md"
OUT_EDGES = ROOT / "holes-edges.txt"

# Bare tactic `sorry`, not the substring of "sorry-free".
SORRY_RE = re.compile(r"(?<![\w-])sorry(?![\w-])")
# Residual `axiom` counts as unfinished (intentional §4 black boxes stay open).
AXIOM_RE = re.compile(r"^axiom\s+([A-Za-z0-9_'.]+)")
DECL_RE = re.compile(r"^(theorem|lemma)\s+([A-Za-z0-9_'.]+)")
NS_OPEN_RE = re.compile(r"^namespace\s+([A-Za-z0-9_'.]+)")
NS_END_RE = re.compile(r"^end(?:\s+([A-Za-z0-9_'.]+))?\s*$")

# Paper-facing nodes shown on the board (id → metadata).
# status is overwritten from the Lean scan when the declaration is found.
NODES: dict[str, dict] = {
    # §1
    "unit_closed_neg": {
        "label": "§1 ¬ closed",
        "section": 1,
        "file": "ContinuousFOL/Introduction/UnitInterval.lean",
        "detail": "[0,1] closed under 1−x.",
    },
    "unit_closed_half": {
        "label": "§1 ½ closed",
        "section": 1,
        "file": "ContinuousFOL/Introduction/UnitInterval.lean",
        "detail": "[0,1] closed under x/2.",
    },
    # §3
    "DyadicCode.val_mem_Icc": {
        "label": "val ∈ [0,1]",
        "section": 3,
        "file": "ContinuousFOL/Group1Axioms/DyadicCode/Val.lean",
        "detail": "DyadicCode.val lands in [0,1].",
    },
    "DyadicCode.dense_in_Icc": {
        "label": "Rem 3.4 denseness",
        "section": 3,
        "file": "ContinuousFOL/Group1Axioms/DyadicCode/Val.lean",
        "detail": "Dyadics dense in (x,y) ∩ [0,1].",
    },
    # §4 black boxes (axioms / approx completeness)
    "cl_consistent_iff_satisfiable": {
        "label": "Fact 4.1 CL",
        "section": 4,
        "file": "ContinuousFOL/BlackBox/CLConsistentIffSatisfiable.lean",
        "detail": "CL: consistent ↔ satisfiable (black-box axiom).",
    },
    "cl_finite_strong_completeness": {
        "label": "Fact 4.2 finite",
        "section": 4,
        "file": "ContinuousFOL/BlackBox/CLFiniteStrongCompleteness.lean",
        "detail": "CL finite strong completeness (black-box axiom).",
    },
    "cl_approx_strong_completeness": {
        "label": "Fact 4.3 approx",
        "section": 4,
        "file": "ContinuousFOL/BlackBox/CLApproxStrongCompleteness.lean",
        "detail": "CL approximated strong completeness.",
    },
    "luk_consistent_iff_satisfiable": {
        "label": "Fact 4.4 Łuk",
        "section": 4,
        "file": "ContinuousFOL/BlackBox/LukConsistentIffSatisfiable.lean",
        "detail": "Łukasiewicz: consistent ↔ satisfiable (black-box axiom).",
    },
    "luk_weak_completeness": {
        "label": "Fact 4.5 weak",
        "section": 4,
        "file": "ContinuousFOL/BlackBox/LukWeakCompleteness.lean",
        "detail": "Łukasiewicz weak completeness (black-box axiom).",
    },
    # §5
    "Formula.eval_in_Icc": {
        "label": "eval ∈ [0,1]",
        "section": 5,
        "file": "ContinuousFOL/LanguageAndSemantics/FormulaEval.lean",
        "detail": "Formula evaluation stays in [0,1].",
    },
    # §6
    "substitution_lemma": {
        "label": "Subst lemma",
        "section": 6,
        "file": "ContinuousFOL/SubstitutionAndCompletions/SubstitutionLemma.lean",
        "detail": "Free substitution preserves evaluation.",
    },
    "bound_substitution_lemma": {
        "label": "Bound subst",
        "section": 6,
        "file": "ContinuousFOL/SubstitutionAndCompletions/BoundSubstitutionLemma.lean",
        "detail": "Bound variable renaming lemma.",
    },
    "surjective_morphism_elementary": {
        "label": "Thm 6.6 elem.",
        "section": 6,
        "file": "ContinuousFOL/SubstitutionAndCompletions/LMorphism.lean",
        "detail": "Surjective 𝓛-morphisms are elementary.",
    },
    "exists_metric_completion": {
        "label": "Metric completion",
        "section": 6,
        "file": "ContinuousFOL/SubstitutionAndCompletions/ExistsMetricCompletion.lean",
        "detail": "Every MetricPreStructure embeds in a ContinuousStructure.",
    },
    "eval_uniformly_continuous": {
        "label": "eval unif. cont.",
        "section": 6,
        "file": "ContinuousFOL/SubstitutionAndCompletions/EvalUniformlyContinuous.lean",
        "detail": "Formula eval is uniformly continuous on metric structures.",
    },
    "entails_metric_iff_complete": {
        "label": "Entails ↔ complete",
        "section": 6,
        "file": "ContinuousFOL/SubstitutionAndCompletions/EntailsMetricIffComplete.lean",
        "detail": "Metric entails iff complete-structure entails.",
    },
    "satisfiable_metric_iff_complete": {
        "label": "Sat ↔ complete",
        "section": 6,
        "file": "ContinuousFOL/SubstitutionAndCompletions/EntailsMetricIffComplete.lean",
        "detail": "Metric satisfiable iff completely satisfiable.",
    },
    # §7
    "soundness_pre": {
        "label": "Thm 7.2 sound",
        "section": 7,
        "file": "ContinuousFOL/Group2Axioms/SoundnessPre.lean",
        "detail": "ProvableQ ⇒ EntailsPre.",
    },
    "satisfiable_consistent_pre": {
        "label": "Sat ⇒ Cons (pre)",
        "section": 7,
        "file": "ContinuousFOL/Group2Axioms/SoundnessPre.lean",
        "detail": "SatisfiablePre ⇒ ConsistentQ.",
    },
    "soundness_metric": {
        "label": "Thm 7.2 metric",
        "section": 7,
        "file": "ContinuousFOL/Group2Axioms/SoundnessMetric.lean",
        "detail": "ProvableMetricQ ⇒ EntailsComplete.",
    },
    "satisfiable_consistent_metric": {
        "label": "Sat ⇒ Cons (met)",
        "section": 7,
        "file": "ContinuousFOL/Group2Axioms/SoundnessMetric.lean",
        "detail": "CompletelySatisfiable ⇒ ConsistentMetricQ.",
    },
    # §8
    "deduction_theorem": {
        "label": "Deduction",
        "section": 8,
        "file": "ContinuousFOL/Essentials/DeductionTheorem.lean",
        "detail": "Deduction theorem (pre).",
    },
    "deduction_theorem_metric": {
        "label": "Deduction met",
        "section": 8,
        "file": "ContinuousFOL/Essentials/DeductionTheorem.lean",
        "detail": "Deduction theorem (metric).",
    },
    "generalization_theorem": {
        "label": "Generalization",
        "section": 8,
        "file": "ContinuousFOL/Essentials/GeneralizationTheorem.lean",
        "detail": "Generalization theorem.",
    },
    "generalize_fresh_const": {
        "label": "Fresh const gen",
        "section": 8,
        "file": "ContinuousFOL/Essentials/GeneralizeFreshConst.lean",
        "detail": "Generalize over a fresh constant.",
    },
    "ProvableQ.tsub_one": {
        "label": "⊢ φ ∸ 1",
        "section": 8,
        "file": "ContinuousFOL/Essentials/InconsistentIffProvableOne.lean",
        "detail": "Łukasiewicz tautology φ ∸ 1 from A1–A4 + MP.",
    },
    "inconsistent_iff_provable_one": {
        "label": "Incons ↔ ⊢1",
        "section": 8,
        "file": "ContinuousFOL/Essentials/InconsistentIffProvableOne.lean",
        "detail": "¬ConsistentQ ↔ ProvableQ Γ 1.",
    },
    "provable_bound_subst": {
        "label": "⊢ bound subst",
        "section": 8,
        "file": "ContinuousFOL/Essentials/ProvableBoundSubst.lean",
        "detail": "Bound substitution is provable.",
    },
    "consistent_adjoin_approx": {
        "label": "Adjoin approx",
        "section": 8,
        "file": "ContinuousFOL/Essentials/ConsistentAdjoin.lean",
        "detail": "Consistent adjunction of approximate inequalities.",
    },
    "consistent_adjoin_comparable": {
        "label": "Adjoin comparable",
        "section": 8,
        "file": "ContinuousFOL/Essentials/ConsistentAdjoin.lean",
        "detail": "Consistent adjunction of comparability.",
    },
    "mem_iff_provable": {
        "label": "∈ ↔ ⊢ (max)",
        "section": 8,
        "file": "ContinuousFOL/Essentials/MaximalConsistent.lean",
        "detail": "In a maximal consistent set, membership ↔ provability.",
    },
    "maximal_consistent_sup_instantiate": {
        "label": "sup instantiate",
        "section": 8,
        "file": "ContinuousFOL/Essentials/MaximalConsistent.lean",
        "detail": "Lemma 8.11: sup_x φ ∸ p ∈ Δ ⇒ ∃ φ' ≡ φ, φ'[t/x] ∸ p ∈ Δ.",
    },
    "maximal_consistent_sup_instantiate_aux": {
        "label": "8.11 helper",
        "section": 8,
        "file": "ContinuousFOL/Essentials/MaximalConsistent.lean",
        "detail": "Helper: Lemma 8.11 plus rank and substitution correctness of φ'.",
    },
    "maximal_consistent_sup_eq_inf": {
        "label": "sup = Inf",
        "section": 8,
        "file": "ContinuousFOL/Essentials/MaximalConsistent.lean",
        "detail": "Degree of truth via Inf of dyadic approximations.",
    },
    "maximal_in_consistent_extensions_iff": {
        "label": "Max ↔ no ext",
        "section": 8,
        "file": "ContinuousFOL/Essentials/MaximalConsistent.lean",
        "detail": "Maximal among consistent extensions characterization.",
    },
    "exists_maximal_consistent": {
        "label": "Thm 8.10 Lindenbaum",
        "section": 8,
        "file": "ContinuousFOL/Essentials/MaximalConsistent.lean",
        "detail": "Lindenbaum: every consistent set has a maximal extension.",
    },
    "exists_maximal_consistent_metric": {
        "label": "Thm 8.10 metric",
        "section": 8,
        "file": "ContinuousFOL/Essentials/MaximalConsistentMetric.lean",
        "detail": "Metric Lindenbaum lemma.",
    },
    # §9
    "eval_reduct": {
        "label": "eval reduct",
        "section": 9,
        "file": "ContinuousFOL/Completeness/SignatureExtension.lean",
        "detail": "Evaluation after signature reduct.",
    },
    "exists_henkin_extension": {
        "label": "Henkin extension",
        "section": 9,
        "file": "ContinuousFOL/Completeness/ExistsHenkinExtension.lean",
        "detail": "Consistent theories admit Henkin extensions.",
    },
    "exists_henkin_extension_metric": {
        "label": "Henkin ext met",
        "section": 9,
        "file": "ContinuousFOL/Completeness/ExistsHenkinExtension.lean",
        "detail": "Metric Henkin extension.",
    },
    "termPreStructure_eval_eq_sup": {
        "label": "term eval = Inf",
        "section": 9,
        "file": "ContinuousFOL/Completeness/TermPreStructureEvalEqSup.lean",
        "detail": "Term model evaluation matches Inf of dyadics in Δ.",
    },
    "henkin_model_existence": {
        "label": "Thm 9.4 Henkin",
        "section": 9,
        "file": "ContinuousFOL/Completeness/HenkinModelExistence.lean",
        "detail": "Consistent ⇒ term-model of a maximal Henkin extension.",
    },
    "henkin_model_existence_metric": {
        "label": "Thm 9.4 metric",
        "section": 9,
        "file": "ContinuousFOL/Completeness/HenkinModelExistenceMetric.lean",
        "detail": "Consistent ⇒ metric term-model of a maximal consistent Henkin complete Δ ⊇ Γ.",
    },
    "metric_prestructure_model_of_consistent": {
        "label": "9.5 met helper",
        "section": 9,
        "file": "ContinuousFOL/Completeness/HenkinModelExistenceMetric.lean",
        "detail": "Helper: metric-consistent Γ has a metric pre-structure model.",
    },
    "completeness_pre": {
        "label": "Thm 9.5 complete",
        "section": 9,
        "file": "ContinuousFOL/Completeness/CompletenessPre.lean",
        "detail": "ConsistentQ → SatisfiablePre (iff helper: completeness_pre_iff).",
    },
    "completeness_metric": {
        "label": "Thm 9.5 metric",
        "section": 9,
        "file": "ContinuousFOL/Completeness/CompletenessMetric.lean",
        "detail": "ConsistentMetricQ → CompletelySatisfiable (iff helper: completeness_metric_iff).",
    },
    "provable_tsub_of_inconsistent_adjoin": {
        "label": "⊢ φ∸p from ⊥",
        "section": 9,
        "file": "ContinuousFOL/Completeness/ProvableTsubOfInconsistentAdjoin.lean",
        "detail": "Inconsistent adjunction of p∸φ yields ProvableQ Γ (φ∸p).",
    },
    "provable_tsub_of_inconsistent_adjoin_metric": {
        "label": "⊢ φ∸p met",
        "section": 9,
        "file": "ContinuousFOL/Completeness/ProvableTsubOfInconsistentAdjoin.lean",
        "detail": "Metric variant of inconsistent-adjunction rule.",
    },
    "approximated_strong_completeness_pre": {
        "label": "Cor 9.6 approx",
        "section": 9,
        "file": "ContinuousFOL/Completeness/ApproximatedStrongCompleteness.lean",
        "detail": "EntailsPre ↔ ∀n ProvableQ (φ∸2⁻ⁿ).",
    },
    "approximated_strong_completeness_metric": {
        "label": "Cor 9.6 metric",
        "section": 9,
        "file": "ContinuousFOL/Completeness/ApproximatedStrongCompleteness.lean",
        "detail": "EntailsComplete ↔ ∀n ProvableMetricQ (φ∸2⁻ⁿ).",
    },
    "pavelka_completeness_pre": {
        "label": "Cor 9.8 Pavelka",
        "section": 9,
        "file": "ContinuousFOL/Completeness/PavelkaCompleteness.lean",
        "detail": "degreeOfTruthPre = degreeOfProvabilityPre.",
    },
    "pavelka_completeness_metric": {
        "label": "Cor 9.8 metric",
        "section": 9,
        "file": "ContinuousFOL/Completeness/PavelkaCompleteness.lean",
        "detail": "degreeOfTruthComplete = degreeOfProvabilityMetric.",
    },
    "compactness_pre": {
        "label": "Cor 9.12 compact",
        "section": 9,
        "file": "ContinuousFOL/Completeness/CompactnessPre.lean",
        "detail": "Finite satisfiability ⇒ SatisfiablePre.",
    },
    "compactness_metric": {
        "label": "Cor 9.12 metric",
        "section": 9,
        "file": "ContinuousFOL/Completeness/CompactnessMetric.lean",
        "detail": "Finite complete-satisfiability ⇒ CompletelySatisfiable.",
    },
    "complete_re_theory_decidable": {
        "label": "Cor 9.11 RE ⇒ dec.",
        "section": 9,
        "file": "ContinuousFOL/Completeness/UniformlyComputableDegree.lean",
        "detail": "Complete theory with recursive or r.e. axiomatization is decidable (Mathlib computability).",
    },
}

# Hard edges: from → to means the current Lean proof of `to` still needs `from`.
HARD_EDGES: list[tuple[str, str]] = [
    # §1 → §3
    ("unit_closed_neg", "DyadicCode.val_mem_Icc"),
    ("unit_closed_half", "DyadicCode.val_mem_Icc"),
    # §5 uses §1
    ("unit_closed_neg", "Formula.eval_in_Icc"),
    ("unit_closed_half", "Formula.eval_in_Icc"),
    # §6
    ("exists_metric_completion", "entails_metric_iff_complete"),
    ("exists_metric_completion", "satisfiable_metric_iff_complete"),
    # §7
    ("soundness_pre", "satisfiable_consistent_pre"),
    ("soundness_metric", "satisfiable_consistent_metric"),
    # §8 Lindenbaum chain
    ("ProvableQ.tsub_one", "inconsistent_iff_provable_one"),
    ("inconsistent_iff_provable_one", "exists_maximal_consistent"),
    ("mem_iff_provable", "maximal_consistent_sup_eq_inf"),
    ("maximal_consistent_sup_instantiate_aux", "maximal_consistent_sup_instantiate"),
    ("maximal_consistent_sup_instantiate_aux", "termPreStructure_eval_eq_sup"),
    ("maximal_in_consistent_extensions_iff", "exists_maximal_consistent"),
    ("exists_maximal_consistent", "exists_maximal_consistent_metric"),
    # §9 Henkin → completeness → corollaries
    ("exists_henkin_extension", "henkin_model_existence"),
    ("exists_maximal_consistent", "henkin_model_existence"),
    ("termPreStructure_eval_eq_sup", "henkin_model_existence"),
    ("maximal_consistent_sup_eq_inf", "henkin_model_existence"),
    ("DyadicCode.val_mem_Icc", "henkin_model_existence"),
    ("eval_reduct", "completeness_pre"),
    ("henkin_model_existence", "completeness_pre"),
    ("satisfiable_consistent_pre", "completeness_pre"),
    ("exists_henkin_extension_metric", "henkin_model_existence_metric"),
    ("exists_maximal_consistent", "henkin_model_existence_metric"),
    ("termPreStructure_eval_eq_sup", "henkin_model_existence_metric"),
    ("henkin_model_existence", "metric_prestructure_model_of_consistent"),
    ("metric_prestructure_model_of_consistent", "completeness_metric"),
    ("satisfiable_consistent_metric", "completeness_metric"),
    ("completeness_pre", "compactness_pre"),
    ("inconsistent_iff_provable_one", "compactness_pre"),
    ("completeness_metric", "compactness_metric"),
    ("completeness_pre", "approximated_strong_completeness_pre"),
    ("soundness_pre", "approximated_strong_completeness_pre"),
    ("provable_tsub_of_inconsistent_adjoin", "approximated_strong_completeness_pre"),
    ("completeness_metric", "approximated_strong_completeness_metric"),
    ("soundness_metric", "approximated_strong_completeness_metric"),
    ("provable_tsub_of_inconsistent_adjoin_metric", "approximated_strong_completeness_metric"),
    ("completeness_pre", "pavelka_completeness_pre"),
    ("completeness_metric", "pavelka_completeness_metric"),
    ("pavelka_completeness_metric", "complete_re_theory_decidable"),
]

# Soft edges: paper/logical order only. Drawn dashed; do NOT force status.
SOFT_EDGES: list[tuple[str, str]] = [
    ("cl_consistent_iff_satisfiable", "cl_finite_strong_completeness"),
    ("cl_finite_strong_completeness", "cl_approx_strong_completeness"),
    ("luk_consistent_iff_satisfiable", "luk_weak_completeness"),
    ("cl_approx_strong_completeness", "approximated_strong_completeness_pre"),
    ("substitution_lemma", "bound_substitution_lemma"),
    ("bound_substitution_lemma", "provable_bound_subst"),
    ("surjective_morphism_elementary", "eval_uniformly_continuous"),
    ("eval_uniformly_continuous", "exists_metric_completion"),
    ("soundness_pre", "soundness_metric"),
    ("deduction_theorem", "deduction_theorem_metric"),
    ("generalization_theorem", "generalize_fresh_const"),
    ("consistent_adjoin_approx", "consistent_adjoin_comparable"),
    ("consistent_adjoin_comparable", "exists_maximal_consistent"),
    ("DyadicCode.dense_in_Icc", "approximated_strong_completeness_pre"),
    ("approximated_strong_completeness_pre", "approximated_strong_completeness_metric"),
    ("pavelka_completeness_pre", "pavelka_completeness_metric"),
    ("compactness_pre", "compactness_metric"),
]


def scan_lean() -> dict[str, dict]:
    """Return map decl_name → {file, line, has_sorry}.

    Declaration names are recorded both bare and dotted under open namespaces
    (skipping the project root `ContinuousFOL`), so board ids like
    `DyadicCode.dense_in_Icc` resolve after Mathlib-style nesting.
    """
    found: dict[str, dict] = {}
    for path in sorted(LEAN_ROOT.rglob("*.lean")):
        lines = path.read_text(encoding="utf-8").splitlines()
        decls: list[tuple[int, str, bool, tuple[str, ...]]] = []
        ns_stack: list[str] = []
        for i, line in enumerate(lines):
            stripped = line.split("--", 1)[0].rstrip()
            m = NS_OPEN_RE.match(stripped)
            if m:
                for part in m.group(1).split("."):
                    if part:
                        ns_stack.append(part)
                continue
            m = NS_END_RE.match(stripped)
            if m:
                end_name = m.group(1)
                if end_name:
                    parts = [p for p in end_name.split(".") if p]
                    while parts and ns_stack:
                        if ns_stack[-len(parts) :] == parts:
                            del ns_stack[-len(parts) :]
                            break
                        ns_stack.pop()
                elif ns_stack:
                    ns_stack.pop()
                continue
            m = DECL_RE.match(stripped)
            if m:
                decls.append((i, m.group(2), False, tuple(ns_stack)))
                continue
            m = AXIOM_RE.match(stripped)
            if m:
                decls.append((i, m.group(1), True, tuple(ns_stack)))
        for idx, (lineno, name, is_axiom, ns_parts) in enumerate(decls):
            end = decls[idx + 1][0] if idx + 1 < len(decls) else len(lines)
            body = "\n".join(lines[lineno:end])
            stripped = re.sub(r"/-.*?-/", "", body, flags=re.S)
            stripped = re.sub(r"--.*?$", "", stripped, flags=re.M)
            has = is_axiom or bool(SORRY_RE.search(stripped))
            rel = str(path.relative_to(ROOT))
            dotted_parts = [p for p in ns_parts if p != "ContinuousFOL"]
            # Bare leaf, full dotted decl, and ns-prefixed variants.
            leaf = name.rsplit(".", 1)[-1]
            names = [name, leaf]
            if dotted_parts:
                names.append(".".join(dotted_parts + [name]))
                names.append(".".join(dotted_parts + [leaf]))
            for key in names:
                if key not in found:
                    found[key] = {"file": rel, "line": lineno + 1, "has_sorry": has}
                elif has and not found[key]["has_sorry"]:
                    found[key] = {"file": rel, "line": lineno + 1, "has_sorry": has}
    return found


def build() -> dict:
    scanned = scan_lean()
    raw_sorry = {
        nid: True if nid not in scanned else scanned[nid]["has_sorry"]
        for nid in NODES
    }
    hard_preds: dict[str, list[str]] = {nid: [] for nid in NODES}
    for frm, to in HARD_EDGES:
        if frm in NODES and to in NODES:
            hard_preds[to].append(frm)

    status: dict[str, str] = {}
    for _ in range(len(NODES) + 2):
        changed = False
        for nid in NODES:
            preds_done = all(status.get(p) == "done" for p in hard_preds[nid])
            if not raw_sorry[nid] and preds_done:
                st = "done"
            elif preds_done:
                st = "open"
            else:
                st = "blocked"
            if status.get(nid) != st:
                status[nid] = st
                changed = True
        if not changed:
            break

    nodes = []
    for nid, meta in NODES.items():
        info = scanned.get(nid, {})
        file_ = info.get("file", meta["file"])
        nodes.append({
            "id": nid,
            "label": meta["label"],
            "section": meta["section"],
            "file": file_ + (f":{info['line']}" if "line" in info else ""),
            "status": status[nid],
            "blocker": None,
            "detail": meta.get("detail"),
        })

    by_id = {n["id"]: n for n in nodes}
    for n in nodes:
        if n["status"] != "blocked":
            continue
        unfinished = [
            p for p in hard_preds[n["id"]]
            if by_id.get(p, {}).get("status") != "done"
        ]
        if unfinished:
            n["blocker"] = "needs " + ", ".join(unfinished)

    edges = [
        {"from": frm, "to": to, "kind": "hard"}
        for frm, to in HARD_EDGES
        if frm in NODES and to in NODES
    ] + [
        {"from": frm, "to": to, "kind": "soft"}
        for frm, to in SOFT_EDGES
        if frm in NODES and to in NODES
    ]
    sorry_count = sum(1 for n in nodes if n["status"] in ("open", "blocked"))
    open_ids = [n["id"] for n in nodes if n["status"] == "open"]

    return {
        "updated": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "sorryCount": sorry_count,
        "legend": {
            "open": "No unfinished required proof-deps — try next",
            "blocked": "Waiting on incomplete required proof-deps",
            "done": "Proved (no sorry)",
        },
        "notes": [
            "Hard edge B→A: Lean proof of A still needs B — A cannot be done while B is unfinished.",
            "Soft edge B→A: paper-order aspiration only (drawn dashed); does not affect status.",
            "Done = no local sorry and every hard predecessor is done (no unproven→proven).",
            "§4 axioms are intentional black boxes and stay open until discharged.",
            "Blue = done. Green = open. Grey = blocked.",
            "Regenerate with: python3 scripts/build_holes.py",
            f"Open tips: {', '.join(open_ids) if open_ids else '(none)'}.",
        ],
        "nodes": nodes,
        "edges": edges,
    }


def write_md(data: dict) -> None:
    by_sec: dict[int, list] = {}
    for n in data["nodes"]:
        by_sec.setdefault(n["section"], []).append(n)
    open_n = [n for n in data["nodes"] if n["status"] == "open"]
    blocked_n = [n for n in data["nodes"] if n["status"] == "blocked"]
    done_n = [n for n in data["nodes"] if n["status"] == "done"]

    lines = [
        "# Proof holes (ContinuousFOL / Ben Yaacov–Pedersen 2010)",
        "",
        "Inventory of paper-facing Lean holes, ordered **prove-first**.",
        "",
        f"**Updated:** {data['updated']}",
        f"**Holes:** {data['sorryCount']} open+blocked · "
        f"{len(open_n)} open · {len(blocked_n)} blocked · {len(done_n)} done.",
        "",
        "**Live board:** [`holes.html`](holes.html) (graph embedded; open the file directly).",
        "",
        "**Writeup:** [`ContinuousFOL.md`](ContinuousFOL.md).",
        "",
        "```bash",
        "python3 scripts/build_holes.py   # refreshes HOLES.md, holes-graph.json, embeds into holes.html",
        "```",
        "",
        "## Open now (Layer 0)",
        "",
    ]
    if not open_n:
        lines.append(
            "_None — every paper-facing hole is done. Browse the formalization in [`ContinuousFOL.md`](ContinuousFOL.md)._"
        )
    else:
        lines.append("| Id | Label | File |")
        lines.append("|---|---|---|")
        for n in open_n:
            lines.append(f"| `{n['id']}` | {n['label']} | `{n['file']}` |")
    lines += ["", "## By section", ""]
    for sec in sorted(by_sec):
        rows = by_sec[sec]
        holes = sum(1 for n in rows if n["status"] != "done")
        lines.append(f"### §{sec} — {holes} hole(s)")
        lines.append("")
        lines.append("| Status | Id | Label | File |")
        lines.append("|---|---|---|---|")
        for n in rows:
            lines.append(
                f"| {n['status']} | `{n['id']}` | {n['label']} | `{n['file']}` |"
            )
        lines.append("")
    lines += [
        "## Dependency sketch",
        "",
        "```mermaid",
        "flowchart TD",
        "  Sound[soundness_pre] --> SatCons[satisfiable_consistent_pre]",
        "  HenkExt[exists_henkin_extension] --> Henk[henkin_model_existence]",
        "  Lind[exists_maximal_consistent] --> Henk",
        "  TermEval[termPreStructure_eval_eq_sup] --> Henk",
        "  SupInf[maximal_consistent_sup_eq_inf] --> Henk",
        "  Henk --> Comp[completeness_pre]",
        "  SatCons --> Comp",
        "  Comp --> Compact[compactness_pre]",
        "  Comp --> Approx[approximated_strong_completeness_pre]",
        "  Comp --> Pavelka[pavelka_completeness_pre]",
        "  CompM[completeness_metric] --> CompactM[compactness_metric]",
        "  CompM --> ApproxM[approximated_strong_completeness_metric]",
        "  CompM --> PavelkaM[pavelka_completeness_metric]",
        "```",
        "",
    ]
    OUT_MD.write_text("\n".join(lines) + "\n", encoding="utf-8")


def embed_html(data: dict) -> None:
    """Inline the graph JSON into holes.html so opening the file works offline."""
    if not OUT_HTML.exists():
        print(f"skip embed: {OUT_HTML.name} missing")
        return
    text = OUT_HTML.read_text(encoding="utf-8")
    start = text.find("const EMBEDDED_HOLES_GRAPH = ")
    marker = text.find(HTML_EMBED_MARKER, start)
    if start < 0 or marker < 0:
        print(f"skip embed: could not find EMBEDDED_HOLES_GRAPH / marker in {OUT_HTML.name}")
        return
    line_start = text.rfind("\n", 0, start) + 1
    end = marker + len(HTML_EMBED_MARKER)
    payload = json.dumps(data, separators=(",", ":"))
    new_line = f"    const EMBEDDED_HOLES_GRAPH = {payload}; {HTML_EMBED_MARKER}"
    OUT_HTML.write_text(text[:line_start] + new_line + text[end:], encoding="utf-8")


def main() -> None:
    data = build()
    OUT_JSON.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    write_md(data)
    OUT_EDGES.write_text(
        "\n".join(f"{e['from']} -{e['kind']}-> {e['to']}" for e in data["edges"]) + "\n",
        encoding="utf-8",
    )
    embed_html(data)
    open_n = sum(1 for n in data["nodes"] if n["status"] == "open")
    blocked_n = sum(1 for n in data["nodes"] if n["status"] == "blocked")
    done_n = sum(1 for n in data["nodes"] if n["status"] == "done")
    print(
        f"Wrote {OUT_JSON.name}, {OUT_MD.name}, embedded {OUT_HTML.name}: "
        f"{open_n} open, {blocked_n} blocked, {done_n} done "
        f"(sorryCount={data['sorryCount']})"
    )


if __name__ == "__main__":
    main()
