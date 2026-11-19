/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 Corollary 9.12 without metric; vision.md page 25–26
-/
module

public import ContinuousFOL.Completeness.CompletenessPre
public import ContinuousFOL.Essentials.InconsistentIffProvableOne
public import ContinuousFOL.Essentials.ProvableQMono

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Corollary 9.12 (Compactness — without metric). -/
theorem compactness_pre {L : Signature} (Γ : Set (Formula L))
    (hfin : ∀ Γ₀ : Finset (Formula L), (Γ₀ : Set (Formula L)) ⊆ Γ →
      SatisfiablePre.{0} (Γ₀ : Set (Formula L))) :
    SatisfiablePre.{0} Γ := by
  rw [← completeness_pre_iff]
  by_contra hincons
  rw [inconsistent_iff_provable_one] at hincons
  obtain ⟨Γ₀, hsub, hprov₀⟩ := hincons.compact
  have hcons₀ : ConsistentQ (Γ₀ : Set (Formula L)) :=
    satisfiable_consistent_pre _ (hfin Γ₀ hsub)
  have hincons₀ : ¬ ConsistentQ (Γ₀ : Set (Formula L)) :=
    (inconsistent_iff_provable_one _).mpr hprov₀
  exact hincons₀ hcons₀

end ContinuousFOL
