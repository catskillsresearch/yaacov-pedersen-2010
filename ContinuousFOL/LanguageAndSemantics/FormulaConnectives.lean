/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 derived connectives; vision.md page 8
-/
module

public import ContinuousFOL.LanguageAndSemantics.Formula
public import ContinuousFOL.LanguageAndSemantics.MetricSignature

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

variable {L : Signature}

/-- Derived connectives and quantifiers (§5, p. 8). -/
def infQ (x : Var) (φ : Formula L) : Formula L := .neg (.sup x (.neg φ))
def minF (φ ψ : Formula L) : Formula L := .tsub φ (.tsub φ ψ)
def maxF (φ ψ : Formula L) : Formula L := .neg (minF (.neg φ) (.neg ψ))
def absDiff (φ ψ : Formula L) : Formula L := maxF (.tsub φ ψ) (.tsub ψ φ)
def addF (φ ψ : Formula L) : Formula L := .neg (.tsub (.neg φ) ψ)

/-- Metric atomic formula `d t₀ t₁` in a `MetricSignature`. -/
def dist {LM : MetricSignature} (t₀ t₁ : Term LM.toSignature) : Formula LM.toSignature :=
  .rel LM.distSym (fun i =>
    let j : Fin 2 := Fin.cast LM.distArity i
    if j = 0 then t₀ else t₁)

end Formula

end ContinuousFOL
