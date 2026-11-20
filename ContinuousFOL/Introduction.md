# Introduction

@import "../ContinuousFOL.svg" {code_block=false, caption="Section dependencies (§1–§9): arrows point from a prerequisite section to the section that uses it; edges implied by longer paths are omitted. §8 and §9 depend on each other because the §8 adjoining lemma uses an auxiliary module filed with §9."}

This formalization reconstructs, in Lean 4 [@lean4; @gh-lean4] on top of
Mathlib [@mathlib2020; @gh-mathlib4], the proof of completeness for continuous
first-order logic given by Ben Yaacov and Pedersen [@BenYaacovPedersen2010].
The source used throughout is the arXiv preprint arXiv:0903.4051v1; page
references in the green boxes are to that preprint.

The Lean library `ContinuousFOL` follows the paper's section order, and so
does this writeup: §1–§9 below each open with a short orientation, a graph of
the Lean modules belonging to that section, and then one subsection per
module. Each module subsection has three parts. A green box restates, in our
own words, the part of the paper that the module formalizes; it is a
paraphrase, not a quotation. Next comes an account in mathematical English of
what the Lean code itself defines and proves, with the main theorems stated
and their proofs sketched as the Lean code carries them out. Last, the
complete Lean source of the module is reproduced.

The main results are all proved, with no `sorry` and no Lean `axiom`
beyond Lean's standard `propext`, `Classical.choice` and `Quot.sound`:
soundness (Theorem 7.2), completeness (Theorem 9.5), approximated strong
completeness (Corollary 9.6), Pavelka-style completeness (Corollary 9.8),
decidability of complete recursively axiomatized theories (Corollary 9.11) and
compactness (Corollary 9.12). The propositional Facts 4.1–4.5, which the paper
uses as black boxes from the literature
[@Cha58; @Cha59; @RR58; @CDM00; @Hay63; @Pav79; @Haj98], are proved in Lean
rather than assumed. Fact 4.1 (Chang's completeness theorem for Łukasiewicz
logic) is proved along Chang's algebraic route through MV-algebras.

**Faithfulness notes.**

- *Facts 4.2 and 4.3.* As stated in the paper, these are false when there are
  no propositional variables: then there are no formulae, so the empty set is
  satisfiable but inconsistent. The Lean statements add the premise
  `[Nonempty I]`, and the counterexample is itself proved. The first-order
  results of §§7–9 do not depend on these two Facts.
- *§6 completions.* The paper first takes the quotient by $d=0$ and then the
  metric completion. In Lean these are one step: Mathlib's completion of a
  pseudo-metric space is already a complete metric space.
- *§9 Henkin signature.* The paper uses a tower of languages
  $\mathcal L_0\subseteq\mathcal L_1\subseteq\cdots$. Lean instead uses a single
  inductive type of codes for the new constants, and the size of a code takes
  the place of the paper's level in the minimality argument.
- *Universes.* The Henkin model is built in universe $0$. Universe-lifting
  lemmas from §5 transfer the results to arbitrary universes.
- *Corollary 9.8 for inconsistent $\Gamma$.* The paper does not discuss this
  case. In Lean, the stated value $0$ relies on Mathlib's convention
  $\sup\emptyset=0$ for the reals.
- *Complete theories and decidability.* A complete theory (Definition 9.9)
  is restricted to sentences. The countable recursive language assumed in
  Corollary 9.11 is made explicit as a `RecursivePresentation` structure.

These choices are explained in the section notes and module summaries where
they occur.

## Sources, software and AI assistance

All direct and transitive Lake repositories, with their pinned revisions, are
credited in the bibliography
[@gh-plausible; @gh-leansearchclient; @gh-importgraph; @gh-proofwidgets; @gh-aesop; @gh-qq; @gh-batteries; @gh-cli];
the exact full hashes are in `lake-manifest.json`.

Challenge/Solution packaging follows the scott_models and nowakowska1982
repositories [@gh-scott-models; @gh-nowakowska1982], using the Palomar policy,
Comparator conventions and formalization metadata schema
[@gh-palomar-policy; @gh-comparator; @gh-formalization-yaml; @PalomarAbout].
The layout of this writeup and its Markdown-to-LaTeX pipeline follow the
lyasoff2016 repository [@gh-lyasoff2016]. The Unicode-to-LaTeX listing
sanitizer was adapted from scott1964 [@gh-scott1964]. The formalization source
is available on GitHub [@gh-yaacov-pedersen-2010].
**Palomar Registration:** TBD.

Lars Warren Ericson directed and reviewed the development and takes
responsibility for the mathematical claims. As recorded in `formalization.yaml`
and `scripts/ai_model_cards.py`, AI assistance came from Grok Bot
[@ai-grok-bot] and Google Gemini 4 Carbon [@Gem4C]. Grok Bot wrote the
paraphrased paper boxes and the mathematical-English module summaries
(`ContinuousFOL/module_writeup.json`) from the Lean source. Following COPE
guidance [@COPE24], no AI system is listed as an author.

Itaï Ben Yaacov and Arthur Paul Pedersen did not participate in, review or
endorse this formalization. Dana Scott has contacted Pedersen about it, and no
reply has been received so far.
