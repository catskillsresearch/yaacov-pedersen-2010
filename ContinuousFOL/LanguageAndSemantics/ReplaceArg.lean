/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 / §7 uniform continuity moduli helpers
-/
module

public import Mathlib.Data.Fin.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Helper: replace the `i`-th entry of a tuple `v : Fin n → M` by `c`. -/
def replaceArg {n : ℕ} {M : Type*} (v : Fin n → M) (i : Fin n) (c : M) : Fin n → M :=
  fun j => if j = i then c else v j

end ContinuousFOL
