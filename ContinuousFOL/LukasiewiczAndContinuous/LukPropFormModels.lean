/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §2 satisfaction / entailment for Łukasiewicz propositional logic
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukPropFormEval
public import Mathlib.Data.Set.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace LukPropForm

def Models {I : Type*} (v₀ : I → ℝ) (Σ_set : Set (LukPropForm I)) : Prop :=
  (∀ i, 0 ≤ v₀ i ∧ v₀ i ≤ 1) ∧ ∀ φ ∈ Σ_set, eval v₀ φ = 0

def Satisfiable {I : Type*} (Σ_set : Set (LukPropForm I)) : Prop :=
  ∃ v₀, Models v₀ Σ_set

def Entails {I : Type*} (Σ_set : Set (LukPropForm I)) (φ : LukPropForm I) : Prop :=
  ∀ v₀, Models v₀ Σ_set → eval v₀ φ = 0

end LukPropForm

end ContinuousFOL
