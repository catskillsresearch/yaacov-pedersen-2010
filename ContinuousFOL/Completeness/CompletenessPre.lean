/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Theorem 9.5 without metric; vision.md page 23
-/
module

public import ContinuousFOL.Completeness.HenkinModelExistence
public import ContinuousFOL.Group2Axioms.SoundnessPre
public import ContinuousFOL.LanguageAndSemantics.UliftPreStructure

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Theorem 9.5 (Completeness for Continuous First-Order Logic — without metric). -/
theorem completeness_pre {L : Signature} (Γ : Set (Formula L)) :
    ConsistentQ Γ → SatisfiablePre.{0} Γ := by
  intro hcons
  obtain ⟨Lc, ext, Δ, M, σ, _, _, hΓΔ, hMΔ⟩ := henkin_model_existence hcons
  refine ⟨ext.reductPre M, σ, ?_⟩
  intro φ hφ
  rw [ext.eval_reduct M σ φ]
  exact hMΔ (ext.mapFormula φ) (hΓΔ ⟨φ, hφ, rfl⟩)

/-- Satisfiability of `Γ` does not depend on the universe: a universe-0 model
    (e.g. a term/Henkin model) lifts by `ULift` to any universe, and a model in
    any universe yields consistency, hence a universe-0 model by Theorem 9.5. -/
theorem satisfiablePre_iff_universe.{u} {L : Signature} (Γ : Set (Formula L)) :
    SatisfiablePre.{u} Γ ↔ SatisfiablePre.{0} Γ :=
  ⟨fun h => completeness_pre Γ (satisfiable_consistent_pre Γ h),
    SatisfiablePre.of_universe0⟩

/-- Theorem 9.5 together with soundness (Theorem 7.2): `Γ` is consistent iff satisfiable
(helper; not a paper statement). The right-hand side ranges over pre-structures
in an arbitrary universe. -/
theorem completeness_pre_iff.{u} {L : Signature} (Γ : Set (Formula L)) :
    ConsistentQ Γ ↔ SatisfiablePre.{u} Γ :=
  ⟨fun h => (satisfiablePre_iff_universe.{u} Γ).mpr (completeness_pre Γ h),
    satisfiable_consistent_pre Γ⟩

end ContinuousFOL
