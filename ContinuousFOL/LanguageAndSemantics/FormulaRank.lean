/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.3 (defined with Formula syntax)
-/
module

public import ContinuousFOL.LanguageAndSemantics.Formula

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

variable {L : Signature}

/-- Rank of a formula (Definition 9.3). -/
def rank : Formula L → ℕ
  | .rel _ _  => 0
  | .half φ   => rank φ + 1
  | .neg φ    => rank φ + 1
  | .tsub φ ψ => rank φ + rank ψ + 1
  | .sup _ φ  => rank φ + 1

end Formula

end ContinuousFOL
