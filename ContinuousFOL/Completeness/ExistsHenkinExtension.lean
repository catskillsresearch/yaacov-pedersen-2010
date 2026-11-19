/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Proposition 9.2; vision.md page 21
-/
module

public import ContinuousFOL.Completeness.HenkinComplete
public import ContinuousFOL.Completeness.SignatureExtension
public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.LanguageAndSemantics.MetricSignature

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Proposition 9.2: Existence of a conservative Henkin completion `(L^c, Γ^c)`. -/
theorem exists_henkin_extension (L : Signature) :
    ∃ (Lc : Signature) (ext : SignatureExtension L Lc) (Γc : Set (Formula Lc)),
      (∀ Γ : Set (Formula L), HenkinComplete ((ext.mapFormula '' Γ) ∪ Γc)) ∧
      (∀ Γ : Set (Formula L), ConsistentQ Γ → ConsistentQ ((ext.mapFormula '' Γ) ∪ Γc)) := by
  sorry

theorem exists_henkin_extension_metric (LM : MetricSignature) :
    ∃ (LMc : MetricSignature) (ext : SignatureExtension LM.toSignature LMc.toSignature)
      (hdist : ext.relEquiv LM.distSym = LMc.distSym)
      (Γc : Set (Formula LMc.toSignature)),
      (∀ Γ : Set (Formula LM.toSignature), HenkinComplete ((ext.mapFormula '' Γ) ∪ Γc)) ∧
      (∀ Γ : Set (Formula LM.toSignature),
        ConsistentMetricQ Γ → ConsistentMetricQ ((ext.mapFormula '' Γ) ∪ Γc)) := by
  sorry

end ContinuousFOL
