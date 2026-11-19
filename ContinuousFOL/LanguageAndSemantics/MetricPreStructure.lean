/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §5 Definition 5.6 (iii)–(v); vision.md page 8–9
-/
module

public import ContinuousFOL.LanguageAndSemantics.PreStructure
public import ContinuousFOL.LanguageAndSemantics.MetricSignature
public import ContinuousFOL.LanguageAndSemantics.ReplaceArg
public import ContinuousFOL.Introduction.TsubR

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- A continuous `𝓛`-pre-structure for a metric signature (Definition 5.6 (iii)–(v)). -/
structure MetricPreStructure (LM : MetricSignature) extends PreStructure LM.toSignature where
  /-- Convenience projection for `d^𝔐(x, y)`. -/
  distVal (x y : Carrier) : ℝ :=
    relInterp LM.distSym (fun i =>
      let j : Fin 2 := Fin.cast LM.distArity i
      if j = 0 then x else y)
  distVal_eq : ∀ x y, distVal x y =
    relInterp LM.distSym (fun i =>
      let j : Fin 2 := Fin.cast LM.distArity i
      if j = 0 then x else y) := by intros; rfl
  dist_self : ∀ a, distVal a a = 0
  dist_symm : ∀ a b, distVal a b = distVal b a
  dist_triangle : ∀ a b c, distVal a c ≤ distVal a b + distVal b c
  func_unif_cont : ∀ (f : LM.Func) (i : Fin (LM.funcArity f)) (ε : ℝ),
    0 < ε → ε ≤ 1 → ∀ (v : Fin (LM.funcArity f) → Carrier) (c e : Carrier),
      distVal c e < LM.funcMod f i ε →
      distVal (funcInterp f (replaceArg v i c)) (funcInterp f (replaceArg v i e)) ≤ ε
  rel_unif_cont : ∀ (P : LM.Rel) (i : Fin (LM.relArity P)) (ε : ℝ),
    0 < ε → ε ≤ 1 → ∀ (v : Fin (LM.relArity P) → Carrier) (c e : Carrier),
      distVal c e < LM.relMod P i ε →
      relInterp P (replaceArg v i c) ∸ relInterp P (replaceArg v i e) ≤ ε

end ContinuousFOL
