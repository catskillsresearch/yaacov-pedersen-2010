/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Definition 9.7 (i); vision.md page 24
-/
module

public import ContinuousFOL.LanguageAndSemantics.ModelsPre
public import ContinuousFOL.LanguageAndSemantics.ContinuousStructure
public import Mathlib.Data.Set.Lattice

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Definition 9.7 (i): Degree of truth `φ°_Γ` with respect to `Γ`. -/
def degreeOfTruthPre {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) : ℝ :=
  sSup {r : ℝ | ∃ (M : PreStructure L) (σ : Var → M.Carrier),
    ModelsPre M σ Γ ∧ r = φ.eval M σ}

def degreeOfTruthComplete {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : ℝ :=
  sSup {r : ℝ | ∃ (M : ContinuousStructure LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}

end ContinuousFOL
