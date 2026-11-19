/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Remark 3.4; vision.md page 6
-/
module

public import ContinuousFOL.Introduction.UnitInterval

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Syntactic codes for dyadic expressions generated from `1` using `¬`, `∸`, `1/2` (Remark 3.4). -/
inductive DyadicCode : Type
  | one  : DyadicCode
  | neg  : DyadicCode → DyadicCode
  | tsub : DyadicCode → DyadicCode → DyadicCode
  | half : DyadicCode → DyadicCode
  deriving DecidableEq, Repr

end ContinuousFOL
