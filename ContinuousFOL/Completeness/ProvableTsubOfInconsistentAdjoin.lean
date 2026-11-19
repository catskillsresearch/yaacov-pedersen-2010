/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §8/§9 auxiliary for strong completeness; vision.md page 23–24
-/
module

public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Auxiliary lemma (cf. proof of Lemma 8.5): if `Γ ∪ {p ∸ φ}` is inconsistent,
    then `Γ ⊢_Q φ ∸ p`. -/
lemma provable_tsub_of_inconsistent_adjoin {L : Signature} (Γ : Set (Formula L))
    (φ : Formula L) (p : DyadicCode)
    (hincons : ¬ ConsistentQ (Γ ∪ {.tsub (Formula.dyadic L p) φ})) :
    ProvableQ Γ (.tsub φ (Formula.dyadic L p)) := by
  sorry

lemma provable_tsub_of_inconsistent_adjoin_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) (p : DyadicCode)
    (hincons : ¬ ConsistentMetricQ (Γ ∪ {.tsub (Formula.dyadic LM.toSignature p) φ})) :
    ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p)) := by
  sorry

end ContinuousFOL
