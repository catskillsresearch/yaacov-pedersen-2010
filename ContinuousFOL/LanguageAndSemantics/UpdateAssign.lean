/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.10 (ii); vision.md page 9
-/
module

public import ContinuousFOL.LanguageAndSemantics.Var

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Update an assignment `σ : Var → M` at `x` with `a` (Definition 5.10 (ii)). -/
def updateAssign {M : Type*} (σ : Var → M) (x : Var) (a : M) : Var → M :=
  fun y => if x = y then a else σ y

@[simp] lemma updateAssign_same {M : Type*} (σ : Var → M) (x : Var) (a : M) :
    updateAssign σ x a x = a := by simp [updateAssign]

@[simp] lemma updateAssign_ne {M : Type*} (σ : Var → M) {x y : Var} (h : x ≠ y) (a : M) :
    updateAssign σ x a y = σ y := by simp [updateAssign, h]

end ContinuousFOL
