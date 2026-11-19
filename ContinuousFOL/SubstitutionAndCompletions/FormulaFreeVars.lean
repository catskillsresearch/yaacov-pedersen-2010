/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §6 free/bound variables; vision.md page 11
-/
module

public import ContinuousFOL.SubstitutionAndCompletions.TermVars
public import ContinuousFOL.LanguageAndSemantics.Formula

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace Formula

variable {L : Signature}

/-- Free variables of a formula `φ`. -/
def freeVars : Formula L → Finset Var
  | .rel _ args => Finset.univ.biUnion (fun i => (args i).vars)
  | .tsub α β   => α.freeVars ∪ β.freeVars
  | .neg α      => α.freeVars
  | .half α     => α.freeVars
  | .sup x α    => α.freeVars.erase x

/-- All variables (free or bound) occurring in `φ`. -/
def allVars : Formula L → Finset Var
  | .rel _ args => Finset.univ.biUnion (fun i => (args i).vars)
  | .tsub α β   => α.allVars ∪ β.allVars
  | .neg α      => α.allVars
  | .half α     => α.allVars
  | .sup x α    => insert x α.allVars

/-- Bound variables occurring in `φ`. -/
def boundVars : Formula L → Finset Var
  | .rel _ _  => ∅
  | .tsub α β => α.boundVars ∪ β.boundVars
  | .neg α    => α.boundVars
  | .half α   => α.boundVars
  | .sup x α  => insert x α.boundVars

end Formula

end ContinuousFOL
