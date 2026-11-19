/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 Definition 3.1 / §7 consistency
-/
module

public import ContinuousFOL.Group2Axioms.ProvableQ
public import ContinuousFOL.Group2Axioms.ProvableMetricQ

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Consistency (Definition 3.1). -/
def ConsistentQ {L : Signature} (Γ : Set (Formula L)) : Prop :=
  ∃ φ : Formula L, ¬ ProvableQ Γ φ

def ConsistentMetricQ {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) : Prop :=
  ∃ φ : Formula LM.toSignature, ¬ ProvableMetricQ Γ φ

end ContinuousFOL
