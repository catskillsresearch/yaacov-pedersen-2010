/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §9 signature extensions; vision.md page 20–21
-/
module

public import ContinuousFOL.LanguageAndSemantics.Signature
public import ContinuousFOL.LanguageAndSemantics.Term
public import ContinuousFOL.LanguageAndSemantics.Formula
public import ContinuousFOL.LanguageAndSemantics.PreStructure
public import ContinuousFOL.LanguageAndSemantics.FormulaEval

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Embedding of signatures `ι : L₁ → L₂` that adds new constant symbols (preserving `Rel`
    and moduli). -/
structure SignatureExtension (L₁ L₂ : Signature) where
  relEquiv      : L₁.Rel ≃ L₂.Rel
  funcMap       : L₁.Func → L₂.Func
  funcMap_inj   : Function.Injective funcMap
  relArity_eq   : ∀ P, L₂.relArity (relEquiv P) = L₁.relArity P
  funcArity_eq  : ∀ f, L₂.funcArity (funcMap f) = L₁.funcArity f
  relMod_eq     : ∀ P i ε, L₂.relMod (relEquiv P) (Fin.cast (relArity_eq P).symm i) ε =
                    L₁.relMod P i ε
  funcMod_eq    : ∀ f i ε, L₂.funcMod (funcMap f) (Fin.cast (funcArity_eq f).symm i) ε =
                    L₁.funcMod f i ε

namespace SignatureExtension

def mapTerm {L₁ L₂ : Signature} (e : SignatureExtension L₁ L₂) : Term L₁ → Term L₂
  | .var x       => .var x
  | .func f args =>
      .func (e.funcMap f) (fun i => e.mapTerm (args (Fin.cast (e.funcArity_eq f) i)))

def mapFormula {L₁ L₂ : Signature} (e : SignatureExtension L₁ L₂) : Formula L₁ → Formula L₂
  | .rel P args =>
      .rel (e.relEquiv P) (fun i => e.mapTerm (args (Fin.cast (e.relArity_eq P) i)))
  | .tsub α β   => .tsub (e.mapFormula α) (e.mapFormula β)
  | .neg α      => .neg (e.mapFormula α)
  | .half α     => .half (e.mapFormula α)
  | .sup x α    => .sup x (e.mapFormula α)

/-- Reduct of an `L₂`-pre-structure to `L₁` along `e : SignatureExtension L₁ L₂`. -/
def reductPre {L₁ L₂ : Signature} (e : SignatureExtension L₁ L₂) (M : PreStructure L₂) :
    PreStructure L₁ where
  Carrier    := M.Carrier
  nonempty   := M.nonempty
  funcInterp := fun f args =>
    M.funcInterp (e.funcMap f) (fun i => args (Fin.cast (e.funcArity_eq f) i))
  relInterp  := fun P args =>
    M.relInterp (e.relEquiv P) (fun i => args (Fin.cast (e.relArity_eq P) i))
  rel_in_Icc := fun P _args => M.rel_in_Icc (e.relEquiv P) _

lemma eval_reduct {L₁ L₂ : Signature} (e : SignatureExtension L₁ L₂) (M : PreStructure L₂)
    (σ : Var → M.Carrier) (φ : Formula L₁) :
    φ.eval (e.reductPre M) σ = (e.mapFormula φ).eval M σ := by
  sorry

end SignatureExtension

end ContinuousFOL
