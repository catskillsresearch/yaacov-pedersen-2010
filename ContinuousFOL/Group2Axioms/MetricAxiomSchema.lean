/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §7 (A10)–(A14); vision.md page 14–15
-/
module

public import ContinuousFOL.Group2Axioms.BaseAxiomSchema
public import ContinuousFOL.LanguageAndSemantics.FormulaConnectives
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.LanguageAndSemantics.ReplaceArg
public import ContinuousFOL.Group1Axioms.DyadicCode.Val

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Metric and uniform continuity axiom schemata (A10)–(A14) (§7). -/
inductive MetricAxiomSchema {LM : MetricSignature} : Formula LM.toSignature → Prop
  | base {φ} : BaseAxiomSchema φ → MetricAxiomSchema φ
  | A10 (x : Var) :
      MetricAxiomSchema (Formula.dist (LM := LM) (.var x) (.var x))
  | A11 (x y : Var) :
      MetricAxiomSchema (.tsub (Formula.dist (LM := LM) (.var x) (.var y))
                               (Formula.dist (LM := LM) (.var y) (.var x)))
  | A12 (x y z : Var) :
      MetricAxiomSchema (.tsub (.tsub (Formula.dist (LM := LM) (.var x) (.var z))
                                      (Formula.dist (LM := LM) (.var x) (.var y)))
                               (Formula.dist (LM := LM) (.var y) (.var z)))
  | A13 (f : LM.Func) (i : Fin (LM.funcArity f)) (ε : ℝ) (r q : DyadicCode)
      (v : Fin (LM.funcArity f) → Var) (z w : Var) :
      0 < ε → ε ≤ 1 → ε < r.val → q.val < LM.funcMod f i ε →
      MetricAxiomSchema
        (Formula.minF
          (.tsub (Formula.dyadic LM.toSignature q) (Formula.dist (LM := LM) (.var z) (.var w)))
          (.tsub (Formula.dist (LM := LM)
                    (.func f (replaceArg (fun j => .var (v j)) i (.var z)))
                    (.func f (replaceArg (fun j => .var (v j)) i (.var w))))
                 (Formula.dyadic LM.toSignature r)))
  | A14 (P : LM.Rel) (i : Fin (LM.relArity P)) (ε : ℝ) (r q : DyadicCode)
      (v : Fin (LM.relArity P) → Var) (z w : Var) :
      0 < ε → ε ≤ 1 → ε < r.val → q.val < LM.relMod P i ε →
      MetricAxiomSchema
        (Formula.minF
          (.tsub (Formula.dyadic LM.toSignature q) (Formula.dist (LM := LM) (.var z) (.var w)))
          (.tsub (.tsub (.rel P (replaceArg (fun j => .var (v j)) i (.var z)))
                        (.rel P (replaceArg (fun j => .var (v j)) i (.var w))))
                 (Formula.dyadic LM.toSignature r)))

end ContinuousFOL
