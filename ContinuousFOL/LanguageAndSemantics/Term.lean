/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 terms; vision.md page 8
-/
module

public import ContinuousFOL.LanguageAndSemantics.Var
public import ContinuousFOL.LanguageAndSemantics.Signature

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- First-order `𝓛`-terms (§5). -/
inductive Term (L : Signature) : Type _
  | var  : Var → Term L
  | func : (f : L.Func) → (Fin (L.funcArity f) → Term L) → Term L

end ContinuousFOL
