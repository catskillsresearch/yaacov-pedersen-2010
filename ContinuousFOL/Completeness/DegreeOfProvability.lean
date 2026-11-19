/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.7 (ii); vision.md page 24
-/
module

public import ContinuousFOL.Group2Axioms.ProvableQ
public import ContinuousFOL.Group2Axioms.ProvableMetricQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.Group1Axioms.DyadicCode.Val
public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Definition 9.7 (ii): Degree of provability `φ^⊛_Γ` with respect to `Γ`. -/
def degreeOfProvabilityPre {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) : ℝ :=
  sInf {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ ProvableQ Γ (.tsub φ (Formula.dyadic L p))}

def degreeOfProvabilityMetric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : ℝ :=
  sInf {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
    ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p))}

end ContinuousFOL
