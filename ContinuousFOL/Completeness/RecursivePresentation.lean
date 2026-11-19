/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.10; vision.md page 25
-/
module

public import ContinuousFOL.LanguageAndSemantics.MetricSignature
public import ContinuousFOL.Group1Axioms.DyadicCode.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Abstract computability predicates for recursive languages and decidable theories
    (Definitions 9.10 & Corollary 9.11). -/
structure RecursivePresentation (LM : MetricSignature) where
  encodeFormula  : Formula LM.toSignature ≃ ℕ
  encodeDyadic   : DyadicCode ≃ ℕ
  axiomRE        : Set ℕ -- r.e. encoding of logical axioms

end ContinuousFOL
