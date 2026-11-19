/-
Copyright (c) 2026 Lars Warren Ericson
Released under Apache-2.0 license as described in file LICENSE.
-/
module

public import ContinuousFOL.LanguageAndSemantics.EntailsPre
public import ContinuousFOL.LanguageAndSemantics.CompletelySatisfiable
public import ContinuousFOL.LanguageAndSemantics.FormulaDyadic
public import ContinuousFOL.LanguageAndSemantics.MetricPreStructure
public import ContinuousFOL.Group2Axioms.ConsistentQ
public import ContinuousFOL.Group2Axioms.ProvableQ
public import ContinuousFOL.Group2Axioms.ProvableMetricQ
public import ContinuousFOL.Completeness.DegreeOfTruth
public import ContinuousFOL.Completeness.DegreeOfProvability
public import ContinuousFOL.Completeness.SignatureExtension
public import ContinuousFOL.Completeness.HenkinComplete
public import ContinuousFOL.Essentials.MaximalConsistent
public import ContinuousFOL.Essentials.MaximalConsistentMetric
public import ContinuousFOL.Completeness.DecidableTheory
public import Mathlib.Data.Finset.Basic

/-!
# Palomar Challenge (statement of record)

Paper-facing statements for the ContinuousFOL comparator family, each matching
the corresponding theorem in the `ContinuousFOL/` library. This file imports
the library's type formers (syntax, semantics, and provability) but not the
compared theorems; every compared declaration is a deliberate `sorry` hole.

Framing: reconstruction/verification of I. Ben Yaacov and A. P. Pedersen,
*A proof of completeness for continuous first-order logic*, J. Symbolic Logic
75 (2010) 168–190. The source authors did not participate in or endorse this
formalization. Every compared theorem's Solution proof uses only `propext` /
`Quot.sound` / `Classical.choice`. See `PROVENANCE.md` / `formalization.yaml`.
-/
@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

/-- Theorem 7.2 (Soundness). "Let \(\mathcal{L}\) be a continuous signature
    (with a metric), and let \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\).
    Then for every formula \(\varphi\), (i) If \(\Gamma \vdash_Q \varphi\),
    then \(\Gamma \vDash_Q \varphi\) (\(\Gamma \vDash_{QC} \varphi\)).
    (ii) If \(\Gamma\) is (completely) satisfiable, then \(\Gamma\) is
    consistent."

    This is the reading for a signature without a metric: \(\Gamma \vdash_Q \varphi\)
    implies \(\Gamma \vDash_Q \varphi\). -/
theorem soundness_pre.{u} {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) :
    ProvableQ Γ φ → EntailsPre.{u} Γ φ := by
  sorry

/-- Theorem 7.2 (Soundness). "Let \(\mathcal{L}\) be a continuous signature
    (with a metric), and let \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\).
    Then for every formula \(\varphi\), (i) If \(\Gamma \vdash_Q \varphi\),
    then \(\Gamma \vDash_Q \varphi\) (\(\Gamma \vDash_{QC} \varphi\)).
    (ii) If \(\Gamma\) is (completely) satisfiable, then \(\Gamma\) is
    consistent." -/
theorem soundness_metric_full.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    (ProvableMetricQ Γ φ → EntailsMetricPre.{u} Γ φ ∧ EntailsComplete.{u} Γ φ) ∧
    (SatisfiableMetricPre.{u} Γ → ConsistentMetricQ Γ) ∧
    (CompletelySatisfiable.{u} Γ → ConsistentMetricQ Γ) := by
  sorry

/-- Theorem 9.4. "Let \(\mathcal{L}\) be a continuous signature (possibly with
    a metric), and let \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\). Assume
    \(\Gamma\) is consistent. Then there is a continuous signature
    \(\mathcal{L}^c \supseteq \mathcal{L}\), a maximal consistent and Henkin
    complete set \(\Delta \subseteq \mathrm{For}(\mathcal{L}^c)\) with
    \(\Delta \supseteq \Gamma\), a continuous \(\mathcal{L}^c\)-prestructure
    \(\mathfrak{M}\), and an \(\mathfrak{M}\)-assignment \(\sigma\) such that
    \((\mathfrak{M}, \sigma) \vDash_Q \Delta\)." -/
theorem henkin_model_existence {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) :
    ∃ (Lc : Signature) (ext : SignatureExtension L Lc) (Δ : Set (Formula Lc))
      (M : PreStructure.{0} Lc) (σ : Var → M.Carrier),
      MaximalConsistent Δ ∧ HenkinComplete Δ ∧
      (ext.mapFormula '' Γ) ⊆ Δ ∧ ModelsPre M σ Δ := by
  sorry

/-- Theorem 9.4 (for a signature with a metric). "Let \(\mathcal{L}\) be a
    continuous signature (possibly with a metric), and let
    \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\). Assume \(\Gamma\) is
    consistent. Then there is a continuous signature
    \(\mathcal{L}^c \supseteq \mathcal{L}\), a maximal consistent and Henkin
    complete set \(\Delta \subseteq \mathrm{For}(\mathcal{L}^c)\) with
    \(\Delta \supseteq \Gamma\), a continuous \(\mathcal{L}^c\)-prestructure
    \(\mathfrak{M}\), and an \(\mathfrak{M}\)-assignment \(\sigma\) such that
    \((\mathfrak{M}, \sigma) \vDash_Q \Delta\)."

    When \(\mathcal{L}\) has a metric, \(\vdash_Q\) includes axioms A10–A14,
    \(\mathcal{L}^c\) carries the same metric symbol, and \(\mathfrak{M}\) is
    a metric pre-structure. -/
theorem henkin_model_existence_metric {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (hcons : ConsistentMetricQ Γ) :
    ∃ (LMc : MetricSignature) (ext : SignatureExtension LM.toSignature LMc.toSignature)
      (_ : ext.relEquiv LM.distSym = LMc.distSym)
      (Δ : Set (Formula LMc.toSignature)) (M : MetricPreStructure.{0} LMc) (σ : Var → M.Carrier),
      MaximalConsistentMetric Δ ∧ HenkinComplete Δ ∧
      (ext.mapFormula '' Γ) ⊆ Δ ∧ ModelsPre M.toPreStructure σ Δ := by
  sorry

/-- Theorem 9.5 (Completeness for Continuous First-Order Logic). "Let
    \(\mathcal{L}\) be a continuous signature, and let
    \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\). Then \(\Gamma\) is
    consistent only if \(\Gamma\) is satisfiable." -/
theorem completeness_pre {L : Signature} (Γ : Set (Formula L)) :
    ConsistentQ Γ → SatisfiablePre.{0} Γ := by
  sorry

/-- Theorem 9.5 (Completeness for Continuous First-Order Logic). "Furthermore,
    if \(\mathcal{L}\) is a continuous signature with a metric, then \(\Gamma\)
    is consistent only if \(\Gamma\) is completely satisfiable." -/
theorem completeness_metric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    ConsistentMetricQ Γ → CompletelySatisfiable.{0} Γ := by
  sorry

/-- Corollary 9.6 (Approximated Strong Completeness for Continuous Logic).
    "Let \(\mathcal{L}\) be a continuous signature, let
    \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\), and let \(\varphi\) be a
    formula. Then \(\Gamma \vDash_Q \varphi\) if and only if
    \(\Gamma \vdash_Q \varphi \dot{-} 2^{-n}\) for all \(n < \omega\)." -/
theorem approximated_strong_completeness_pre.{u} {L : Signature}
    (Γ : Set (Formula L)) (φ : Formula L) :
    EntailsPre.{u} Γ φ ↔ ∀ n : ℕ, ProvableQ Γ (.tsub φ (Formula.pow2Neg L n)) := by
  sorry

/-- Corollary 9.6 (Approximated Strong Completeness for Continuous Logic).
    "Moreover, if \(\mathcal{L}\) is a continuous signature with a metric, then
    \(\Gamma \vDash_{QC} \varphi\) if and only if
    \(\Gamma \vdash_Q \varphi \dot{-} 2^{-n}\) for all \(n < \omega\)."

    The Lean states both readings the paper gives for a metric signature:
    \(\Gamma \vDash_Q \varphi\) iff \(\Gamma \vdash_Q \varphi \dot{-} 2^{-n}\)
    for all \(n\), and \(\Gamma \vDash_{QC} \varphi\) iff
    \(\Gamma \vdash_Q \varphi \dot{-} 2^{-n}\) for all \(n\). -/
theorem approximated_strong_completeness_metric.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    (EntailsMetricPre.{u} Γ φ ↔
      ∀ n : ℕ, ProvableMetricQ Γ (.tsub φ (Formula.pow2Neg LM.toSignature n))) ∧
    (EntailsComplete.{u} Γ φ ↔
      ∀ n : ℕ, ProvableMetricQ Γ (.tsub φ (Formula.pow2Neg LM.toSignature n))) := by
  sorry

/-- Corollary 9.8. "Let \(\mathcal{L}\) be a continuous signature, and let
    \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\). Then for every formula
    \(\varphi\), the degree of truth of \(\varphi\) with respect to \(\Gamma\)
    equals the degree of provability of \(\varphi\) with respect to \(\Gamma\).
    In other words, \(\varphi^{\circ}_{\Gamma} = \varphi^{\circledcirc}_{\Gamma}\)." -/
theorem pavelka_completeness_pre.{u} {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) :
    degreeOfTruthPre.{u} Γ φ = degreeOfProvabilityPre Γ φ := by
  sorry

/-- Corollary 9.8, for a signature with a metric. "Let \(\mathcal{L}\) be a
    continuous signature, and let \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\).
    Then for every formula \(\varphi\), the degree of truth of \(\varphi\) with
    respect to \(\Gamma\) equals the degree of provability of \(\varphi\) with
    respect to \(\Gamma\). In other words,
    \(\varphi^{\circ}_{\Gamma} = \varphi^{\circledcirc}_{\Gamma}\)." -/
theorem pavelka_completeness_metric.{u} {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    degreeOfTruthMetric.{u} Γ φ = degreeOfProvabilityMetric Γ φ := by
  sorry

/-- Corollary 9.11. "Every complete theory with a recursive or recursively
    enumerable axiomatization is decidable." -/
theorem complete_re_theory_decidable.{u} {LM : MetricSignature}
    (P : RecursivePresentation LM) (T : Set (Formula LM.toSignature))
    (hcomp : IsCompleteTheory.{u} T)
    (hax : ∃ Ax : Set (Formula LM.toSignature), IsAxiomatization.{u} Ax T ∧
      (ComputablePred (fun n : ℕ => ∃ φ ∈ Ax, P.code φ = n) ∨
        REPred (fun n : ℕ => ∃ φ ∈ Ax, P.code φ = n))) :
    IsDecidableTheory.{u} P T := by
  sorry

/-- Corollary 9.12 (Compactness). "Let \(\mathcal{L}\) be a continuous
    signature, and let \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\). If every
    finite subset \(\Gamma_0\) of \(\Gamma\) is (completely) satisfiable, then
    \(\Gamma\) is (completely) satisfiable."

    This is the reading for a signature without a metric. -/
theorem compactness_pre.{u} {L : Signature} (Γ : Set (Formula L))
    (hfin : ∀ Γ₀ : Finset (Formula L), (Γ₀ : Set (Formula L)) ⊆ Γ →
      SatisfiablePre.{u} (Γ₀ : Set (Formula L))) :
    SatisfiablePre.{u} Γ := by
  sorry

/-- Corollary 9.12 (Compactness). "Let \(\mathcal{L}\) be a continuous
    signature, and let \(\Gamma \subseteq \mathrm{For}(\mathcal{L})\). If every
    finite subset \(\Gamma_0\) of \(\Gamma\) is (completely) satisfiable, then
    \(\Gamma\) is (completely) satisfiable."

    For a signature with a metric, the Lean is the conjunction of the
    pre-structure reading and the complete-structure reading. -/
theorem compactness_metric.{u} {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    ((∀ Γ₀ : Finset (Formula LM.toSignature),
        (Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ →
          SatisfiableMetricPre.{u} (Γ₀ : Set (Formula LM.toSignature))) →
      SatisfiableMetricPre.{u} Γ) ∧
    ((∀ Γ₀ : Finset (Formula LM.toSignature),
        (Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ →
          CompletelySatisfiable.{u} (Γ₀ : Set (Formula LM.toSignature))) →
      CompletelySatisfiable.{u} Γ) := by
  sorry

end ContinuousFOL
