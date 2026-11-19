/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 formulae; vision.md page 8
-/
module

public import ContinuousFOL.LanguageAndSemantics.Term

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Continuous first-order `𝓛`-formulae (§5). -/
inductive Formula (L : Signature) : Type
  | rel  : (P : L.Rel) → (Fin (L.relArity P) → Term L) → Formula L
  | tsub : Formula L → Formula L → Formula L
  | neg  : Formula L → Formula L
  | half : Formula L → Formula L
  | sup  : Var → Formula L → Formula L

end ContinuousFOL
