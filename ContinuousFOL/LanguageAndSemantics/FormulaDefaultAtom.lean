/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 / Notation 3.3 anchor
-/
module

public import ContinuousFOL.LanguageAndSemantics.Formula

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

variable {L : Signature}

/-- Canonical closed anchor formula `P x₀ ... x₀` used for constant `1 := ¬(φ₀ ∸ φ₀)`. -/
def defaultAtom (L : Signature) : Formula L :=
  let P : L.Rel := Classical.arbitrary L.Rel
  .rel P (fun _ => .var 0)

end Formula

end ContinuousFOL
