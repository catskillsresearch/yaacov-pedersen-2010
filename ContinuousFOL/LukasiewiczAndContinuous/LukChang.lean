/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §4 Fact 4.1 (Chang 1959), the completeness direction. If `⊬ φ`,
extend `∅` to a linear `Δ` with `Δ ⊬ φ` (`exists_linear_extension`). The
Lindenbaum algebra of `Δ` is an MV-chain, and `φ` is non-zero at its canonical
assignment. Embedding the chain in its ordered group and transferring to `ℝ`
(`exists_real_of_evalMV_chain_ne_zero`) gives a `[0, 1]`-assignment with
`φ ≠ 0`, so `⊭ φ`.
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukLinearTheory
public import ContinuousFOL.LukasiewiczAndContinuous.ChainGroup
public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormSoundness

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

/-- Completeness direction of Fact 4.1: `⊨ φ → ⊢ φ`. -/
theorem provable_of_entails_empty {I : Type*} (φ : LukPropForm I) (h : Entails ∅ φ) :
    Provable ∅ φ := by
  by_contra hφ
  have : Inhabited (LukPropForm I) := ⟨φ⟩
  obtain ⟨Δ, -, hΔφ, hlin⟩ := exists_linear_extension ∅ φ hφ
  have : MVAlgebra.MVChain (LukLindT Δ) :=
    { total := LukLind.le_total_of_isLinear hlin
      zero_ne_one := by
        intro h01
        apply hΔφ
        apply (LukLind.mk_eq_zero_iff φ).mp
        have hle := MVAlgebra.le_one (LukLind.mk φ : LukLindT Δ)
        rw [← h01] at hle
        exact MVAlgebra.le_zero_iff.mp hle }
  have hne : evalMV (A := LukLindT Δ) (fun i => LukLind.mk (.var i)) φ ≠ 0 := fun h0 =>
    hΔφ ((LukLind.provable_iff_evalMV_canonical φ).mpr h0)
  obtain ⟨w, hw, hev⟩ := exists_real_of_evalMV_chain_ne_zero _ φ hne
  exact hev (h w ⟨hw, fun _ hm => by simp at hm⟩)

/-- Fact 4.1 (proof): `⊨ φ ↔ ⊢ φ`. -/
theorem entails_empty_iff_provable {I : Type*} (φ : LukPropForm I) :
    Entails ∅ φ ↔ Provable ∅ φ :=
  ⟨provable_of_entails_empty φ, soundness⟩

end LukPropForm

end ContinuousFOL
