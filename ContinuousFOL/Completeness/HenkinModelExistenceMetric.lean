/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Theorem 9.4 metric; vision.md page 23
-/
module

public import ContinuousFOL.Completeness.HenkinModelExistence
public import ContinuousFOL.LanguageAndSemantics.MetricPreStructure

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

theorem henkin_model_existence_metric {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (hcons : ConsistentMetricQ Γ) :
    ∃ (M : MetricPreStructure LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ Γ := by
  sorry

end ContinuousFOL
