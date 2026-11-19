/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Notation 3.3 in FO language; vision.md page 6
-/
module

public import ContinuousFOL.LanguageAndSemantics.FormulaDefaultAtom

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

/-- Constant `1` shorthand (Notation 3.3). -/
def one (L : Signature) : Formula L :=
  let φ₀ := defaultAtom L
  .neg (.tsub φ₀ φ₀)

/-- Constant `0` shorthand (Notation 3.3). -/
def zero (L : Signature) : Formula L := .neg (one L)

end Formula

end ContinuousFOL
