/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.4; vision.md page 8
-/
module

public import ContinuousFOL.LanguageAndSemantics.Signature

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- A continuous signature with a distinguished binary metric symbol `d` (Definition 5.4). -/
structure MetricSignature extends Signature where
  distSym   : Rel
  distArity : relArity distSym = 2

end ContinuousFOL
