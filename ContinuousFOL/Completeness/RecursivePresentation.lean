/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §1 (decidability paragraph: "a theory (in a countable, recursive language)");
§9 Definition 9.10 / Corollary 9.11; vision.md pages 3, 25
-/
module

public import Mathlib.Computability.RE
public import ContinuousFOL.Essentials.MaximalConsistentMetric
public import ContinuousFOL.Group1Axioms.DyadicCode.Val

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- A *countable, recursive* presentation of a metric signature `𝓛` (the standing assumption
of the paper's decidability discussion, §1): a Gödel numbering `⌜·⌝` of `For(𝓛)` into `ℕ`
such that

* the set of codes of formulae is decidable;
* the syntactic operation `(φ, ψ) ↦ φ ∸ ψ` is computable on codes;
* the dyadic constants `k / 2ⁿ` (as the formulae `mulPow2Neg k n`, Remark 3.4) have codes
  computable from `(k, n)`;
* the set of codes of the logical axioms (all generalizations of (A1)–(A14), §7) is
  recursively enumerable.

These make the proof system `⊢` (over a recursively enumerable set of premises) effective,
which is what "recursive language" means for the proof system of §7. -/
structure RecursivePresentation (LM : MetricSignature) where
  code : Formula LM.toSignature → ℕ
  code_injective : Function.Injective code
  isCode_computable : ComputablePred (fun n : ℕ => n ∈ Set.range code)
  tsubCode : ℕ → ℕ → ℕ
  tsubCode_computable : Computable₂ tsubCode
  tsubCode_spec : ∀ φ ψ, tsubCode (code φ) (code ψ) = code (.tsub φ ψ)
  dyadicCode : ℕ → ℕ → ℕ
  dyadicCode_computable : Computable₂ dyadicCode
  dyadicCode_spec : ∀ k n,
    dyadicCode k n = code (Formula.dyadic LM.toSignature (DyadicCode.mulPow2Neg k n))
  axioms_re : REPred (fun n : ℕ => ∃ φ ∈ metricAxiomSet LM, code φ = n)

end ContinuousFOL
