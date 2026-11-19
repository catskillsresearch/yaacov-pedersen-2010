/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Theorem 9.5 without metric; vision.md page 23
-/
module

public import ContinuousFOL.Completeness.HenkinModelExistence
public import ContinuousFOL.Group2Axioms.SoundnessPre

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Theorem 9.5 (Completeness for Continuous First-Order Logic — without metric). -/
theorem completeness_pre {L : Signature} (Γ : Set (Formula L)) :
    ConsistentQ Γ ↔ SatisfiablePre Γ := by
  refine ⟨?_, satisfiable_consistent_pre Γ⟩
  intro hcons
  obtain ⟨Lc, ext, Δ, M, σ, _, _, hΓΔ, hMΔ⟩ := henkin_model_existence hcons
  refine ⟨ext.reductPre M, σ, ?_⟩
  intro φ hφ
  rw [ext.eval_reduct M σ φ]
  exact hMΔ (ext.mapFormula φ) (hΓΔ ⟨φ, hφ, rfl⟩)

end ContinuousFOL
