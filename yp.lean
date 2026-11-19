import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Order.Zorn

/-!
# A Proof of Completeness for Continuous First-Order Logic
Formalization of Itaï Ben Yaacov and Arthur Paul Pedersen (arXiv:0903.4051v1)

Single-file Lean 4 + Mathlib4 blueprint / partial proof script covering:
- §2-4: Łukasiewicz and Continuous Propositional Logic, Group 1 Axioms, Black Box Theorems
- §5: Continuous Signatures, Syntax (Terms, Formulae), Pre-structures, Metric Structures, Semantics
- §6: Free and Bound Substitution, Morphisms, Metric Completions
- §7: Group 2 Axioms (Quantifier, Pseudo-metric, Uniform Continuity Moduli) and Soundness
- §8: Weak Deduction Theorem, Generalization, Maximal Consistent Sets (Zorn's Lemma)
- §9: Henkin Completeness, Term Pre-structure, Main Completeness Theorems, Pavelka Completeness, Compactness
-/

noncomputable section
open Classical

namespace ContinuousLogic

/-! ## Preliminaries: Truncated Subtraction and Dyadic Syntactic Sugar -/

/-- Truncated subtraction on ℝ: `x ∸ y = max (x - y) 0`. -/
def tsubR (x y : ℝ) : ℝ := max (x - y) 0

infixl:65 " ∸ " => tsubR

@[simp] lemma tsubR_def (x y : ℝ) : x ∸ y = max (x - y) 0 := rfl

lemma tsubR_nonneg (x y : ℝ) : 0 ≤ x ∸ y := le_max_right _ _

lemma tsubR_eq_zero_iff (x y : ℝ) : x ∸ y = 0 ↔ x ≤ y := by
  simp [tsubR, max_eq_right_iff, sub_nonpos]

lemma tsubR_le_iff (x y z : ℝ) (hz : 0 ≤ z) : x ∸ y ≤ z ↔ x - y ≤ z := by
  simp [tsubR, max_le_iff, hz]

lemma unit_closed_tsubR {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hy0 : 0 ≤ y) :
    0 ≤ x ∸ y ∧ x ∸ y ≤ 1 := by
  refine ⟨tsubR_nonneg x y, max_le ?_ zero_le_one⟩
  linarith

lemma unit_closed_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ 1 - x ∧ 1 - x ≤ 1 := by
  constructor <;> linarith

lemma unit_closed_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x / 2 ∧ x / 2 ≤ 1 := by
  constructor <;> linarith

/-- Syntactic codes for dyadic expressions generated from `1` using `¬`, `∸`, `1/2` (Remark 3.4). -/
inductive DyadicCode : Type
  | one  : DyadicCode
  | neg  : DyadicCode → DyadicCode
  | tsub : DyadicCode → DyadicCode → DyadicCode
  | half : DyadicCode → DyadicCode
  deriving DecidableEq, Repr

namespace DyadicCode

def zero : DyadicCode := .neg .one

/-- `2^{-n}` as `n` applications of `half` to `one` (Notation 3.3). -/
def pow2Neg : ℕ → DyadicCode
  | 0     => .one
  | n + 1 => .half (pow2Neg n)

/-- Real evaluation of a dyadic code in `[0, 1]`. -/
def val : DyadicCode → ℝ
  | .one      => 1
  | .neg d    => 1 - d.val
  | .tsub a b => a.val ∸ b.val
  | .half d   => d.val / 2

@[simp] lemma val_one : DyadicCode.one.val = 1 := rfl
@[simp] lemma val_zero : DyadicCode.zero.val = 0 := by simp [zero, val]

lemma val_pow2Neg (n : ℕ) : (pow2Neg n).val = (2 : ℝ) ^ (-(n : ℤ)) := by
  induction n with
  | zero => simp [pow2Neg, val]
  | succ n ih =>
    simp [pow2Neg, val, ih, zpow_neg, zpow_natCast, pow_succ]
    ring

lemma val_mem_Icc (d : DyadicCode) : 0 ≤ d.val ∧ d.val ≤ 1 := by
  induction d with
  | one => simp [val]
  | neg d ih => exact unit_closed_neg ih.1 ih.2
  | tsub a b iha ihb => exact unit_closed_tsubR iha.1 iha.2 ihb.1
  | half d ih => exact unit_closed_half ih.1 ih.2

/-- Every dyadic rational `k / 2^n` in `[0, 1]` is realized by a `DyadicCode` (Remark 3.4). -/
lemma dense_in_Icc {x y : ℝ} (hx : 0 ≤ x) (hy : y ≤ 1) (hxy : x < y) :
    ∃ d : DyadicCode, x < d.val ∧ d.val < y := by
  sorry

end DyadicCode


/-! ## §2–4: Łukasiewicz and Continuous Propositional Logic -/

/-- Łukasiewicz propositional formulae over propositional variables `I` (Definition 2.1). -/
inductive LukPropForm (I : Type*) : Type _
  | var  : I → LukPropForm I
  | tsub : LukPropForm I → LukPropForm I → LukPropForm I
  | neg  : LukPropForm I → LukPropForm I
  deriving DecidableEq

namespace LukPropForm

def eval {I : Type*} (v₀ : I → ℝ) : LukPropForm I → ℝ
  | .var i    => v₀ i
  | .tsub φ ψ => eval v₀ φ ∸ eval v₀ ψ
  | .neg φ    => 1 - eval v₀ φ

def Models {I : Type*} (v₀ : I → ℝ) (Σ_set : Set (LukPropForm I)) : Prop :=
  (∀ i, 0 ≤ v₀ i ∧ v₀ i ≤ 1) ∧ ∀ φ ∈ Σ_set, eval v₀ φ = 0

def Satisfiable {I : Type*} (Σ_set : Set (LukPropForm I)) : Prop :=
  ∃ v₀, Models v₀ Σ_set

def Entails {I : Type*} (Σ_set : Set (LukPropForm I)) (φ : LukPropForm I) : Prop :=
  ∀ v₀, Models v₀ Σ_set → eval v₀ φ = 0

/-- Axioms (A1)–(A4) for Łukasiewicz propositional logic (§3). -/
inductive IsAxiom {I : Type*} : LukPropForm I → Prop
  | A1 (φ ψ)   : IsAxiom (.tsub (.tsub φ ψ) φ)
  | A2 (φ ψ χ) : IsAxiom (.tsub (.tsub (.tsub χ φ) (.tsub χ ψ)) (.tsub ψ φ))
  | A3 (φ ψ)   : IsAxiom (.tsub (.tsub φ (.tsub φ ψ)) (.tsub ψ (.tsub ψ φ)))
  | A4 (φ ψ)   : IsAxiom (.tsub (.tsub φ ψ) (.tsub (.neg ψ) (.neg φ)))

/-- Formal provability `Σ ⊢^L φ` (§3). -/
inductive Provable {I : Type*} (Σ_set : Set (LukPropForm I)) : LukPropForm I → Prop
  | ax  {φ}   : IsAxiom φ → Provable Σ_set φ
  | hyp {φ}   : φ ∈ Σ_set → Provable Σ_set φ
  | mp  {φ ψ} : Provable Σ_set φ → Provable Σ_set (.tsub ψ φ) → Provable Σ_set ψ

def Consistent {I : Type*} (Σ_set : Set (LukPropForm I)) : Prop :=
  ∃ φ, ¬ Provable Σ_set φ

end LukPropForm

/-- Continuous propositional formulae over `I` (Definition 2.4). -/
inductive CLPropForm (I : Type*) : Type _
  | var  : I → CLPropForm I
  | tsub : CLPropForm I → CLPropForm I → CLPropForm I
  | neg  : CLPropForm I → CLPropForm I
  | half : CLPropForm I → CLPropForm I
  deriving DecidableEq

namespace CLPropForm

def eval {I : Type*} (v₀ : I → ℝ) : CLPropForm I → ℝ
  | .var i    => v₀ i
  | .tsub φ ψ => eval v₀ φ ∸ eval v₀ ψ
  | .neg φ    => 1 - eval v₀ φ
  | .half φ   => eval v₀ φ / 2

def Models {I : Type*} (v₀ : I → ℝ) (Σ_set : Set (CLPropForm I)) : Prop :=
  (∀ i, 0 ≤ v₀ i ∧ v₀ i ≤ 1) ∧ ∀ φ ∈ Σ_set, eval v₀ φ = 0

def Satisfiable {I : Type*} (Σ_set : Set (CLPropForm I)) : Prop :=
  ∃ v₀, Models v₀ Σ_set

def Entails {I : Type*} (Σ_set : Set (CLPropForm I)) (φ : CLPropForm I) : Prop :=
  ∀ v₀, Models v₀ Σ_set → eval v₀ φ = 0

/-- Iterated subtraction `ψ ∸ nφ` (Notation 3.2). -/
def iterSub {I : Type*} (ψ φ : CLPropForm I) : ℕ → CLPropForm I
  | 0     => ψ
  | n + 1 => .tsub (iterSub ψ φ n) φ

/-- Canonical formula `1 := ¬(φ₀ ∸ φ₀)` given any anchor formula `φ₀` (Notation 3.3). -/
def one {I : Type*} (anchor : CLPropForm I) : CLPropForm I :=
  .neg (.tsub anchor anchor)

def dyadic {I : Type*} (anchor : CLPropForm I) : DyadicCode → CLPropForm I
  | .one      => one anchor
  | .neg d    => .neg (dyadic anchor d)
  | .tsub a b => .tsub (dyadic anchor a) (dyadic anchor b)
  | .half d   => .half (dyadic anchor d)

/-- Axioms (A1)–(A6) for Continuous Propositional Logic (§3). -/
inductive IsAxiom {I : Type*} : CLPropForm I → Prop
  | A1 (φ ψ)   : IsAxiom (.tsub (.tsub φ ψ) φ)
  | A2 (φ ψ χ) : IsAxiom (.tsub (.tsub (.tsub χ φ) (.tsub χ ψ)) (.tsub ψ φ))
  | A3 (φ ψ)   : IsAxiom (.tsub (.tsub φ (.tsub φ ψ)) (.tsub ψ (.tsub ψ φ)))
  | A4 (φ ψ)   : IsAxiom (.tsub (.tsub φ ψ) (.tsub (.neg ψ) (.neg φ)))
  | A5 (φ)     : IsAxiom (.tsub (.half φ) (.tsub φ (.half φ)))
  | A6 (φ)     : IsAxiom (.tsub (.tsub φ (.half φ)) (.half φ))

/-- Formal provability `Σ ⊢^{CL} φ` (§3). -/
inductive Provable {I : Type*} (Σ_set : Set (CLPropForm I)) : CLPropForm I → Prop
  | ax  {φ}   : IsAxiom φ → Provable Σ_set φ
  | hyp {φ}   : φ ∈ Σ_set → Provable Σ_set φ
  | mp  {φ ψ} : Provable Σ_set φ → Provable Σ_set (.tsub ψ φ) → Provable Σ_set ψ

def Consistent {I : Type*} (Σ_set : Set (CLPropForm I)) : Prop :=
  ∃ φ, ¬ Provable Σ_set φ

end CLPropForm

section BlackBoxTheorems

/-- Fact 4.1: Weak Completeness for Łukasiewicz Logic [Cha59, RR58]. -/
theorem luk_weak_completeness {I : Type*} (φ : LukPropForm I) :
    LukPropForm.Entails ∅ φ ↔ LukPropForm.Provable ∅ φ := by
  sorry

/-- Fact 4.2: Consistency ↔ Satisfiability for Łukasiewicz Logic. -/
theorem luk_consistent_iff_satisfiable {I : Type*} (Σ_set : Set (LukPropForm I)) :
    LukPropForm.Consistent Σ_set ↔ LukPropForm.Satisfiable Σ_set := by
  sorry

/-- Fact 4.3: Consistency ↔ Satisfiability for Continuous Propositional Logic [Ben]. -/
theorem cl_consistent_iff_satisfiable {I : Type*} (Σ_set : Set (CLPropForm I)) :
    CLPropForm.Consistent Σ_set ↔ CLPropForm.Satisfiable Σ_set := by
  sorry

/-- Fact 4.4: Approximated Strong Completeness for Continuous Propositional Logic. -/
theorem cl_approx_strong_completeness {I : Type*} [Inhabited I]
    (Σ_set : Set (CLPropForm I)) (φ : CLPropForm I) :
    CLPropForm.Entails Σ_set φ ↔
      ∀ n : ℕ, CLPropForm.Provable Σ_set
        (.tsub φ (CLPropForm.dyadic (.var default) (.pow2Neg n))) := by
  sorry

/-- Fact 4.5: Finite Strong Completeness for Continuous Propositional Logic. -/
theorem cl_finite_strong_completeness {I : Type*} (Σ_set : Finset (CLPropForm I))
    (φ : CLPropForm I) :
    CLPropForm.Entails (Σ_set : Set (CLPropForm I)) φ ↔
      CLPropForm.Provable (Σ_set : Set (CLPropForm I)) φ := by
  sorry

end BlackBoxTheorems


/-! ## §5: The Language and Semantics of Continuous First-Order Logic -/

/-- Variable identifiers `V = {v₀, v₁, ...}` (Definition 5.1). -/
abbrev Var := ℕ

/-- A continuous signature `𝓛 = (ℛ, ℱ, 𝒢, n)` (Definition 5.2).
    Note: `ℛ ≠ ∅` is captured by `Nonempty L.Rel`.
    Moduli `δ : ℝ → ℝ` map `(0, 1]` into `(0, 1]`. -/
structure Signature where
  Rel      : Type*
  Func     : Type*
  nonempty_rel : Nonempty Rel
  relArity  : Rel → ℕ
  funcArity : Func → ℕ
  relMod   : (P : Rel) → Fin (relArity P) → ℝ → ℝ
  funcMod  : (f : Func) → Fin (funcArity f) → ℝ → ℝ
  relMod_pos  : ∀ P i ε, 0 < ε → ε ≤ 1 → 0 < relMod P i ε ∧ relMod P i ε ≤ 1
  funcMod_pos : ∀ f i ε, 0 < ε → ε ≤ 1 → 0 < funcMod f i ε ∧ funcMod f i ε ≤ 1

attribute [instance] Signature.nonempty_rel

/-- A continuous signature with a distinguished binary metric symbol `d` (Definition 5.4). -/
structure MetricSignature extends Signature where
  distSym   : Rel
  distArity : relArity distSym = 2

/-- First-order `𝓛`-terms (§5). -/
inductive Term (L : Signature) : Type _
  | var  : Var → Term L
  | func : (f : L.Func) → (Fin (L.funcArity f) → Term L) → Term L

/-- Continuous first-order `𝓛`-formulae (§5). -/
inductive Formula (L : Signature) : Type _
  | rel  : (P : L.Rel) → (Fin (L.relArity P) → Term L) → Formula L
  | tsub : Formula L → Formula L → Formula L
  | neg  : Formula L → Formula L
  | half : Formula L → Formula L
  | sup  : Var → Formula L → Formula L

namespace Formula

variable {L : Signature}

/-- Canonical closed anchor formula `P x₀ ... x₀` used for constant `1 := ¬(φ₀ ∸ φ₀)`. -/
def defaultAtom (L : Signature) : Formula L :=
  let P : L.Rel := Classical.arbitrary L.Rel
  .rel P (fun _ => .var 0)

/-- Constant `1` shorthand (Notation 3.3). -/
def one (L : Signature) : Formula L :=
  let φ₀ := defaultAtom L
  .neg (.tsub φ₀ φ₀)

/-- Constant `0` shorthand (Notation 3.3). -/
def zero (L : Signature) : Formula L := .neg (one L)

/-- Syntactic dyadic constant in `Formula L` (Remark 3.4). -/
def dyadic (L : Signature) : DyadicCode → Formula L
  | .one      => one L
  | .neg d    => .neg (dyadic L d)
  | .tsub a b => .tsub (dyadic L a) (dyadic L b)
  | .half d   => .half (dyadic L d)

/-- `2^{-n}` shorthand in `Formula L` (Notation 3.3). -/
def pow2Neg (L : Signature) (n : ℕ) : Formula L :=
  dyadic L (.pow2Neg n)

/-- Iterated subtraction `ψ ∸ nφ` (Notation 3.2). -/
def iterSub (ψ φ : Formula L) : ℕ → Formula L
  | 0     => ψ
  | n + 1 => .tsub (iterSub ψ φ n) φ

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

/-- Rank of a formula (Definition 9.3). -/
def rank : Formula L → ℕ
  | .rel _ _  => 0
  | .half φ   => rank φ + 1
  | .neg φ    => rank φ + 1
  | .tsub φ ψ => rank φ + rank ψ + 1
  | .sup _ φ  => rank φ + 1

end Formula

/-- Update an assignment `σ : Var → M` at `x` with `a` (Definition 5.10 (ii)). -/
def updateAssign {M : Type*} (σ : Var → M) (x : Var) (a : M) : Var → M :=
  fun y => if x = y then a else σ y

@[simp] lemma updateAssign_same {M : Type*} (σ : Var → M) (x : Var) (a : M) :
    updateAssign σ x a x = a := by simp [updateAssign]

@[simp] lemma updateAssign_ne {M : Type*} (σ : Var → M) {x y : Var} (h : x ≠ y) (a : M) :
    updateAssign σ x a y = σ y := by simp [updateAssign, h]

/-- Helper: replace the `i`-th entry of a tuple `v : Fin n → M` by `c`. -/
def replaceArg {n : ℕ} {M : Type*} (v : Fin n → M) (i : Fin n) (c : M) : Fin n → M :=
  fun j => if j = i then c else v j

/-- A continuous `𝓛`-pre-structure (Definition 5.6 (i)–(ii)). -/
structure PreStructure (L : Signature) where
  Carrier    : Type*
  nonempty   : Nonempty Carrier
  funcInterp : (f : L.Func) → (Fin (L.funcArity f) → Carrier) → Carrier
  relInterp  : (P : L.Rel) → (Fin (L.relArity P) → Carrier) → ℝ
  rel_in_Icc : ∀ P args, 0 ≤ relInterp P args ∧ relInterp P args ≤ 1

attribute [instance] PreStructure.nonempty

/-- Interpretation of a term `t^{𝔐, σ}` (Definition 5.10). -/
def Term.eval {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier) : Term L → M.Carrier
  | .var x       => σ x
  | .func f args => M.funcInterp f (fun i => (args i).eval M σ)

/-- Value of a formula `𝔐(φ, σ)` in `[0, 1]` (Definition 5.11). -/
def Formula.eval {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier) : Formula L → ℝ
  | .rel P args => M.relInterp P (fun i => (args i).eval M σ)
  | .tsub α β   => α.eval M σ ∸ β.eval M σ
  | .neg α      => 1 - α.eval M σ
  | .half α     => α.eval M σ / 2
  | .sup x α    => sSup (Set.range (fun a : M.Carrier => α.eval M (updateAssign σ x a)))

lemma Formula.eval_in_Icc {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (φ : Formula L) : 0 ≤ φ.eval M σ ∧ φ.eval M σ ≤ 1 := by
  induction φ generalizing σ with
  | rel P args => exact M.rel_in_Icc P _
  | tsub α β ihα ihβ => exact unit_closed_tsubR (ihα σ).1 (ihα σ).2 (ihβ σ).1
  | neg α ih => exact unit_closed_neg (ih σ).1 (ih σ).2
  | half α ih => exact unit_closed_half (ih σ).1 (ih σ).2
  | sup x α ih =>
    let S := Set.range (fun a : M.Carrier => α.eval M (updateAssign σ x a))
    have hne : S.Nonempty := Set.range_nonempty _
    have hbdd : BddAbove S := ⟨1, by rintro _ ⟨a, rfl⟩; exact (ih _).2⟩
    refine ⟨?_, csSup_le hne (by rintro _ ⟨a, rfl⟩; exact (ih _).2)⟩
    obtain ⟨a₀⟩ := M.nonempty
    exact le_trans (ih (updateAssign σ x a₀)).1 (le_csSup hbdd ⟨a₀, rfl⟩)

@[simp] lemma Formula.eval_one {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier) :
    (Formula.one L).eval M σ = 1 := by
  simp [Formula.one, Formula.eval, tsubR]

@[simp] lemma Formula.eval_dyadic {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (d : DyadicCode) : (Formula.dyadic L d).eval M σ = d.val := by
  induction d with
  | one => simp [Formula.dyadic]
  | neg d ih => simp [Formula.dyadic, Formula.eval, DyadicCode.val, ih]
  | tsub a b iha ihb => simp [Formula.dyadic, Formula.eval, DyadicCode.val, iha, ihb]
  | half d ih => simp [Formula.dyadic, Formula.eval, DyadicCode.val, ih]

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

/-- A continuous `𝓛`-structure: metric pre-structure where `d^𝔐` is a *complete metric*
    (Definition 5.9). -/
structure ContinuousStructure (LM : MetricSignature) extends MetricPreStructure LM where
  metricSpace   : MetricSpace Carrier
  dist_eq       : ∀ a b, @Dist.dist Carrier metricSpace.toDist a b = distVal a b
  completeSpace : @CompleteSpace Carrier metricSpace.toUniformSpace

/-- Satisfaction `(𝔐, σ) ⊨_Q Γ` (Definition 5.12). -/
def ModelsPre {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (Γ : Set (Formula L)) : Prop :=
  ∀ φ ∈ Γ, φ.eval M σ = 0

def SatisfiablePre {L : Signature} (Γ : Set (Formula L)) : Prop :=
  ∃ (M : PreStructure L) (σ : Var → M.Carrier), ModelsPre M σ Γ

def SatisfiableMetricPre {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) : Prop :=
  ∃ (M : MetricPreStructure LM) (σ : Var → M.Carrier), ModelsPre M.toPreStructure σ Γ

/-- Logical entailment `Γ ⊨_Q φ` over pre-structures (Definition 5.13). -/
def EntailsPre {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) : Prop :=
  ∀ (M : PreStructure L) (σ : Var → M.Carrier), ModelsPre M σ Γ → φ.eval M σ = 0

def EntailsMetricPre {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : Prop :=
  ∀ (M : MetricPreStructure LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ → φ.eval M.toPreStructure σ = 0

/-- Logical equivalence `φ ≡ ψ` (Definition 5.14). -/
def FormulaEquiv {L : Signature} (φ ψ : Formula L) : Prop :=
  ∀ (M : PreStructure L) (σ : Var → M.Carrier), φ.eval M σ = ψ.eval M σ

infix:50 " ≡ᶠ " => FormulaEquiv

/-- Complete satisfiability and entailment `Γ ⊨_{QC} φ` (Definition 6.10). -/
def CompletelySatisfiable {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) : Prop :=
  ∃ (M : ContinuousStructure LM) (σ : Var → M.Carrier), ModelsPre M.toPreStructure σ Γ

def EntailsComplete {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : Prop :=
  ∀ (M : ContinuousStructure LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ → φ.eval M.toPreStructure σ = 0


/-! ## §6: Substitution and Metric Completions -/

namespace Term

variable {L : Signature}

/-- Variables occurring in a term `t`. -/
def vars : Term L → Finset Var
  | .var x       => {x}
  | .func _ args => Finset.univ.biUnion (fun i => (args i).vars)

/-- Replace `x` by `t` inside a term `s`. -/
def subst (s : Term L) (t : Term L) (x : Var) : Term L :=
  match s with
  | .var y       => if y = x then t else .var y
  | .func f args => .func f (fun i => (args i).subst t x)

/-- Replace a 0-ary constant symbol `c` by a variable `x` inside a term (§8, Lemma 8.4). -/
def substConstVar (s : Term L) (c : L.Func) (x : Var) : Term L :=
  match s with
  | .var y       => .var y
  | .func f args =>
      if f = c ∧ L.funcArity f = 0 then .var x
      else .func f (fun i => (args i).substConstVar c x)

end Term

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

/-- Free substitution `φ[t/x]` (Definition 6.1). -/
def freeSubst (φ : Formula L) (t : Term L) (x : Var) : Formula L :=
  match φ with
  | .rel P args => .rel P (fun i => (args i).subst t x)
  | .tsub α β   => .tsub (α.freeSubst t x) (β.freeSubst t x)
  | .neg α      => .neg (α.freeSubst t x)
  | .half α     => .half (α.freeSubst t x)
  | .sup y α    => if y = x then .sup y α else .sup y (α.freeSubst t x)

/-- Correctness of free substitution `φ[t/x]` (Definition 6.1): no variable in `t`
    is captured by a quantifier when `x` occurs free. -/
def FreeSubstCorrect (φ : Formula L) (t : Term L) (x : Var) : Prop :=
  match φ with
  | .rel _ _  => True
  | .tsub α β => α.FreeSubstCorrect t x ∧ β.FreeSubstCorrect t x
  | .neg α    => α.FreeSubstCorrect t x
  | .half α   => α.FreeSubstCorrect t x
  | .sup y α  =>
      if y = x then True
      else (x ∈ α.freeVars → y ∉ t.vars) ∧ α.FreeSubstCorrect t x

/-- Bound substitution `φ{y/x}` (Definition 6.3). -/
def boundSubst (φ : Formula L) (y x : Var) : Formula L :=
  match φ with
  | .rel P args => .rel P args
  | .tsub α β   => .tsub (α.boundSubst y x) (β.boundSubst y x)
  | .neg α      => .neg (α.boundSubst y x)
  | .half α     => .half (α.boundSubst y x)
  | .sup z α    =>
      let α' := α.boundSubst y x
      if z = x then .sup y (α'.freeSubst (.var y) x) else .sup z α'

/-- Replace a 0-ary constant symbol `c` by a variable `x` inside `φ` (Lemma 8.4). -/
def substConstVar (φ : Formula L) (c : L.Func) (x : Var) : Formula L :=
  match φ with
  | .rel P args => .rel P (fun i => (args i).substConstVar c x)
  | .tsub α β   => .tsub (α.substConstVar c x) (β.substConstVar c x)
  | .neg α      => .neg (α.substConstVar c x)
  | .half α     => .half (α.substConstVar c x)
  | .sup z α    => .sup z (α.substConstVar c x)

/-- Whether a function symbol `c` occurs in a term `t`. -/
def Term.hasFunc (t : Term L) (c : L.Func) : Prop :=
  match t with
  | .var _       => False
  | .func f args => f = c ∨ ∃ i, Term.hasFunc (args i) c

/-- Whether a function symbol `c` occurs in `φ`. -/
def hasFunc (φ : Formula L) (c : L.Func) : Prop :=
  match φ with
  | .rel _ args => ∃ i, Formula.Term.hasFunc (args i) c
  | .tsub α β   => α.hasFunc c ∨ β.hasFunc c
  | .neg α      => α.hasFunc c
  | .half α     => α.hasFunc c
  | .sup _ α    => α.hasFunc c

end Formula

/-- Lemma 6.2 (Substitution Lemma). -/
theorem substitution_lemma {L : Signature} (M : PreStructure L) (σ : Var → M.Carrier)
    (t : Term L) (x : Var) (φ : Formula L) (hcorr : φ.FreeSubstCorrect t x) :
    (φ.freeSubst t x).eval M σ = φ.eval M (updateAssign σ x (t.eval M σ)) := by
  sorry

/-- Lemma 6.4 (Bound Substitution Lemma). -/
theorem bound_substitution_lemma {L : Signature} (φ : Formula L) (xs : Finset Var) :
    ∃ φ' : Formula L, Disjoint xs φ'.boundVars ∧ (φ ≡ᶠ φ') := by
  sorry

/-- An `𝓛`-morphism between pre-structures (Definition 6.5). -/
structure LMorphism {L : Signature} (M N : PreStructure L) where
  toFun    : M.Carrier → N.Carrier
  map_func : ∀ (f : L.Func) (args : Fin (L.funcArity f) → M.Carrier),
    toFun (M.funcInterp f args) = N.funcInterp f (fun i => toFun (args i))
  map_rel  : ∀ (P : L.Rel) (args : Fin (L.relArity P) → M.Carrier),
    M.relInterp P args = N.relInterp P (fun i => toFun (args i))

/-- An elementary `𝓛`-morphism (Definition 6.5). -/
structure ElementaryLMorphism {L : Signature} (M N : PreStructure L)
    extends LMorphism M N where
  map_eval : ∀ (σ : Var → M.Carrier) (φ : Formula L),
    φ.eval M σ = φ.eval N (toFun ∘ σ)

lemma LMorphism.map_term {L : Signature} {M N : PreStructure L} (h : LMorphism M N)
    (σ : Var → M.Carrier) (t : Term L) :
    h.toFun (t.eval M σ) = t.eval N (h.toFun ∘ σ) := by
  induction t with
  | var x => rfl
  | func f args ih =>
    simp only [Term.eval, h.map_func]
    congr 1; ext i; exact ih i

/-- Theorem 6.6: Every surjective `𝓛`-morphism is elementary. -/
theorem surjective_morphism_elementary {L : Signature} {M N : PreStructure L}
    (h : LMorphism M N) (hsurj : Function.Surjective h.toFun) :
    ∀ (σ : Var → M.Carrier) (φ : Formula L), φ.eval M σ = φ.eval N (h.toFun ∘ σ) := by
  intro σ φ
  induction φ generalizing σ with
  | rel P args =>
    simp only [Formula.eval, h.map_rel]
    congr 1; ext i; exact h.map_term σ (args i)
  | tsub α β ihα ihβ => simp [Formula.eval, ihα σ, ihβ σ]
  | neg α ih => simp [Formula.eval, ih σ]
  | half α ih => simp [Formula.eval, ih σ]
  | sup x α ih =>
    simp only [Formula.eval]
    congr 1
    ext r
    simp only [Set.mem_range]
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨h.toFun a, ?_⟩
      rw [ih (updateAssign σ x a)]
      congr 1; ext y; by_cases hxy : x = y <;> simp [updateAssign, hxy]
    · rintro ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj b
      refine ⟨a, ?_⟩
      rw [ih (updateAssign σ x a)]
      congr 1; ext y; by_cases hxy : x = y <;> simp [updateAssign, hxy]

/-- Theorem 6.8: Induced mappings of terms and formulae on `M^n` are uniformly continuous. -/
theorem eval_uniformly_continuous {LM : MetricSignature} (M : MetricPreStructure LM)
    (n : ℕ) (xs : Fin n ↪ Var) (φ : Formula LM.toSignature)
    (hvars : ∀ v ∈ φ.freeVars, v ∈ Set.range xs) :
    ∀ ε > 0, ∃ δ > 0, ∀ (a b : Fin n → M.Carrier),
      (∀ i, M.distVal (a i) (b i) < δ) →
      |φ.eval M.toPreStructure (fun v =>
          if h : ∃ i, xs i = v then a (Classical.choose h) else Classical.arbitrary M.Carrier) -
       φ.eval M.toPreStructure (fun v =>
          if h : ∃ i, xs i = v then b (Classical.choose h) else Classical.arbitrary M.Carrier)| ≤ ε := by
  sorry

/-- Theorem 6.9 (Existence of Metric Completion): Every metric pre-structure admits an
    elementary morphism into a complete continuous `𝓛`-structure `𝔐̂`. -/
theorem exists_metric_completion {LM : MetricSignature} (M : MetricPreStructure LM) :
    ∃ (Mhat : ContinuousStructure LM),
      Nonempty (ElementaryLMorphism M.toPreStructure Mhat.toPreStructure) := by
  sorry

/-- Corollary 6.11: Pre-structure entailment/satisfiability coincides with complete metric
    entailment/satisfiability. -/
theorem entails_metric_iff_complete {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    EntailsMetricPre Γ φ ↔ EntailsComplete Γ φ := by
  constructor
  · intro h M σ hM
    exact h M.toMetricPreStructure σ hM
  · intro h M σ hM
    obtain ⟨Mhat, ⟨e⟩⟩ := exists_metric_completion M
    have hMhat : ModelsPre Mhat.toPreStructure (e.toFun ∘ σ) Γ := by
      intro ψ hψ
      rw [← e.map_eval σ ψ]
      exact hM ψ hψ
    rw [e.map_eval σ φ]
    exact h Mhat (e.toFun ∘ σ) hMhat

theorem satisfiable_metric_iff_complete {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) :
    SatisfiableMetricPre Γ ↔ CompletelySatisfiable Γ := by
  constructor
  · rintro ⟨M, σ, hM⟩
    obtain ⟨Mhat, ⟨e⟩⟩ := exists_metric_completion M
    refine ⟨Mhat, e.toFun ∘ σ, ?_⟩
    intro ψ hψ
    rw [← e.map_eval σ ψ]
    exact hM ψ hψ
  · rintro ⟨M, σ, hM⟩
    exact ⟨M.toMetricPreStructure, σ, hM⟩


/-! ## §7: Axioms: Group 2 and Soundness -/

/-- Generalization of a formula `sup_{x₁} ... sup_{x_n} ψ` (§7). -/
def Formula.genList {L : Signature} : List Var → Formula L → Formula L
  | [],      ψ => ψ
  | x :: xs, ψ => .sup x (Formula.genList xs ψ)

/-- Core axiom schemata (A1)–(A9) for an arbitrary continuous signature `L` (§3, §7). -/
inductive BaseAxiomSchema {L : Signature} : Formula L → Prop
  | A1 (φ ψ)   : BaseAxiomSchema (.tsub (.tsub φ ψ) φ)
  | A2 (φ ψ χ) : BaseAxiomSchema (.tsub (.tsub (.tsub χ φ) (.tsub χ ψ)) (.tsub ψ φ))
  | A3 (φ ψ)   : BaseAxiomSchema (.tsub (.tsub φ (.tsub φ ψ)) (.tsub ψ (.tsub ψ φ)))
  | A4 (φ ψ)   : BaseAxiomSchema (.tsub (.tsub φ ψ) (.tsub (.neg ψ) (.neg φ)))
  | A5 (φ)     : BaseAxiomSchema (.tsub (.half φ) (.tsub φ (.half φ)))
  | A6 (φ)     : BaseAxiomSchema (.tsub (.tsub φ (.half φ)) (.half φ))
  | A7 (x φ ψ) : BaseAxiomSchema (.tsub (.tsub (.sup x ψ) (.sup x φ)) (.sup x (.tsub ψ φ)))
  | A8 (x t φ) : φ.FreeSubstCorrect t x → BaseAxiomSchema (.tsub (φ.freeSubst t x) (.sup x φ))
  | A9 (x φ)   : x ∉ φ.freeVars → BaseAxiomSchema (.tsub (.sup x φ) φ)

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

/-- Provability `Γ ⊢_Q φ` over a signature without metric (all generalizations of (A1)–(A9)). -/
inductive ProvableQ {L : Signature} (Γ : Set (Formula L)) : Formula L → Prop
  | ax  {xs : List Var} {ψ : Formula L} : BaseAxiomSchema ψ → ProvableQ Γ (Formula.genList xs ψ)
  | hyp {φ : Formula L} : φ ∈ Γ → ProvableQ Γ φ
  | mp  {φ ψ : Formula L} : ProvableQ Γ φ → ProvableQ Γ (.tsub ψ φ) → ProvableQ Γ ψ

/-- Provability `Γ ⊢_Q φ` over a metric signature (all generalizations of (A1)–(A14)). -/
inductive ProvableMetricQ {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    Formula LM.toSignature → Prop
  | ax  {xs : List Var} {ψ : Formula LM.toSignature} :
      MetricAxiomSchema (LM := LM) ψ → ProvableMetricQ Γ (Formula.genList xs ψ)
  | hyp {φ : Formula LM.toSignature} : φ ∈ Γ → ProvableMetricQ Γ φ
  | mp  {φ ψ : Formula LM.toSignature} :
      ProvableMetricQ Γ φ → ProvableMetricQ Γ (.tsub ψ φ) → ProvableMetricQ Γ ψ

/-- Consistency (Definition 3.1). -/
def ConsistentQ {L : Signature} (Γ : Set (Formula L)) : Prop :=
  ∃ φ : Formula L, ¬ ProvableQ Γ φ

def ConsistentMetricQ {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) : Prop :=
  ∃ φ : Formula LM.toSignature, ¬ ProvableMetricQ Γ φ

/-- Theorem 7.2 (Soundness) for signatures without metric. -/
theorem soundness_pre {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) :
    ProvableQ Γ φ → EntailsPre Γ φ := by
  sorry

theorem satisfiable_consistent_pre {L : Signature} (Γ : Set (Formula L)) :
    SatisfiablePre Γ → ConsistentQ Γ := by
  rintro ⟨M, σ, hM⟩
  refine ⟨Formula.one L, fun hprov => ?_⟩
  have hval := soundness_pre Γ (Formula.one L) hprov M σ hM
  simp at hval

/-- Theorem 7.2 (Soundness) for signatures with a metric. -/
theorem soundness_metric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) :
    ProvableMetricQ Γ φ → EntailsComplete Γ φ := by
  sorry

theorem satisfiable_consistent_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) :
    CompletelySatisfiable Γ → ConsistentMetricQ Γ := by
  rintro ⟨M, σ, hM⟩
  refine ⟨Formula.one LM.toSignature, fun hprov => ?_⟩
  have hval := soundness_metric Γ (Formula.one LM.toSignature) hprov M σ hM
  simp at hval


/-! ## §8: The Essentials -/

/-- Theorem 8.1 (Weak Deduction Theorem). -/
theorem deduction_theorem {L : Signature} (Γ : Set (Formula L)) (φ ψ : Formula L) :
    ProvableQ (Γ ∪ {ψ}) φ ↔ ∃ n : ℕ, ProvableQ Γ (Formula.iterSub φ ψ n) := by
  sorry

theorem deduction_theorem_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ ψ : Formula LM.toSignature) :
    ProvableMetricQ (Γ ∪ {ψ}) φ ↔
      ∃ n : ℕ, ProvableMetricQ Γ (Formula.iterSub φ ψ n) := by
  sorry

/-- Lemma 8.2 (Generalization Theorem). -/
theorem generalization_theorem {L : Signature} (Γ : Set (Formula L)) (φ : Formula L)
    (x : Var) (hx : ∀ ψ ∈ Γ, x ∉ ψ.freeVars) (h : ProvableQ Γ φ) :
    ProvableQ Γ (.sup x φ) := by
  sorry

/-- Lemma 8.3: Provable equivalence of bound variable renaming `φ` and `φ{y/x}`. -/
theorem provable_bound_subst {L : Signature} (φ : Formula L) (x y : Var)
    (hy : y ∉ φ.allVars) :
    ProvableQ ∅ (.tsub φ (φ.boundSubst y x)) ∧
    ProvableQ ∅ (.tsub (φ.boundSubst y x) φ) := by
  sorry

/-- Lemma 8.4: Generalizing over a fresh constant symbol `c`. -/
theorem generalize_fresh_const {L : Signature} (Γ : Set (Formula L)) (φ : Formula L)
    (c : L.Func) (hc0 : L.funcArity c = 0)
    (hcΓ : ∀ ψ ∈ Γ, ¬ ψ.hasFunc c) (x : Var) (hxφ : x ∉ φ.allVars)
    (hprov : ProvableQ Γ φ) :
    ProvableQ Γ (.sup x (φ.substConstVar c x)) := by
  sorry

/-- Consistency criterion via `1`: `Γ` is inconsistent iff `Γ ⊢_Q 1`. -/
lemma inconsistent_iff_provable_one {L : Signature} (Γ : Set (Formula L)) :
    ¬ ConsistentQ Γ ↔ ProvableQ Γ (Formula.one L) := by
  sorry

/-- Lemma 8.5: Closure properties of consistent sets. -/
theorem consistent_adjoin_approx {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) (φ : Formula L)
    (happrox : ∀ n : ℕ, ProvableQ Γ (.tsub φ (Formula.pow2Neg L n))) :
    ConsistentQ (Γ ∪ {φ}) := by
  sorry

theorem consistent_adjoin_comparable {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) (φ ψ : Formula L) :
    ConsistentQ (Γ ∪ {.tsub φ ψ}) ∨ ConsistentQ (Γ ∪ {.tsub ψ φ}) := by
  sorry

/-- Definition 8.8: Maximal consistent set of formulae in continuous first-order logic. -/
structure MaximalConsistent {L : Signature} (Δ : Set (Formula L)) : Prop where
  consistent : ConsistentQ Δ
  archimedean : ∀ φ, (∀ n : ℕ, ProvableQ Δ (.tsub φ (Formula.pow2Neg L n))) → φ ∈ Δ
  comparable  : ∀ φ ψ, Formula.tsub φ ψ ∈ Δ ∨ Formula.tsub ψ φ ∈ Δ

structure MaximalConsistentMetric {LM : MetricSignature}
    (Δ : Set (Formula LM.toSignature)) : Prop where
  consistent : ConsistentMetricQ Δ
  archimedean : ∀ φ,
    (∀ n : ℕ, ProvableMetricQ Δ (.tsub φ (Formula.pow2Neg LM.toSignature n))) → φ ∈ Δ
  comparable  : ∀ φ ψ, Formula.tsub φ ψ ∈ Δ ∨ Formula.tsub ψ φ ∈ Δ

/-- Monotonicity and finiteness of `ProvableQ`. -/
lemma ProvableQ.mono {L : Signature} {Γ Γ' : Set (Formula L)} (hsub : Γ ⊆ Γ')
    {φ : Formula L} (h : ProvableQ Γ φ) : ProvableQ Γ' φ := by
  induction h with
  | ax hax => exact .ax hax
  | hyp hmem => exact .hyp (hsub hmem)
  | mp h₁ h₂ ih₁ ih₂ => exact .mp ih₁ ih₂

lemma ProvableQ.compact {L : Signature} {Γ : Set (Formula L)} {φ : Formula L}
    (h : ProvableQ Γ φ) :
    ∃ Γ₀ : Finset (Formula L), (↑Γ₀ : Set (Formula L)) ⊆ Γ ∧ ProvableQ (↑Γ₀) φ := by
  induction h with
  | ax hax => exact ⟨∅, Set.empty_subset _, .ax hax⟩
  | hyp hmem => exact ⟨{φ}, Set.singleton_subset_iff.mpr hmem, .hyp (Finset.mem_singleton_self φ)⟩
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, h₁s, hp₁⟩ := ih₁
    obtain ⟨Γ₂, h₂s, hp₂⟩ := ih₂
    refine ⟨Γ₁ ∪ Γ₂, ?_, .mp (hp₁.mono ?_) (hp₂.mono ?_)⟩
    · rw [Finset.coe_union]; exact Set.union_subset h₁s h₂s
    · rw [Finset.coe_union]; exact Set.subset_union_left
    · rw [Finset.coe_union]; exact Set.subset_union_right

/-- Lemma 8.6: Maximal elements of `E(Γ)` coincide with `MaximalConsistent`. -/
theorem maximal_in_consistent_extensions_iff {L : Signature} {Γ Δ : Set (Formula L)}
    (hΓ : ConsistentQ Γ) :
    Maximal (fun Γ' => Γ ⊆ Γ' ∧ ConsistentQ Γ') Δ ↔ (Γ ⊆ Δ ∧ MaximalConsistent Δ) := by
  constructor
  · rintro ⟨⟨hsub, hcons⟩, hmax⟩
    refine ⟨hsub, ⟨hcons, ?_, ?_⟩⟩
    · intro φ happrox
      have hcons' := consistent_adjoin_approx hcons φ happrox
      have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hcons'⟩ Set.subset_union_left
      exact heq (Set.mem_union_right _ (Set.mem_singleton φ))
    · intro φ ψ
      rcases consistent_adjoin_comparable hcons φ ψ with hc₁ | hc₂
      · left
        have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hc₁⟩ Set.subset_union_left
        exact heq (Set.mem_union_right _ (Set.mem_singleton _))
      · right
        have heq := hmax ⟨Set.Subset.trans hsub Set.subset_union_left, hc₂⟩ Set.subset_union_left
        exact heq (Set.mem_union_right _ (Set.mem_singleton _))
  · rintro ⟨hsub, hmc⟩
    refine ⟨⟨hsub, hmc.consistent⟩, ?_⟩
    rintro Γ' ⟨hΓ'sub, hΓ'cons⟩ hΔΓ' φ hφ
    apply hmc.archimedean
    intro n
    sorry

/-- Theorem 8.10: Lindenbaum's Lemma via Zorn's Lemma. -/
theorem exists_maximal_consistent {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) :
    ∃ Δ : Set (Formula L), Γ ⊆ Δ ∧ MaximalConsistent Δ := by
  let E : Set (Set (Formula L)) := {Γ' | Γ ⊆ Γ' ∧ ConsistentQ Γ'}
  have hchain : ∀ c ⊆ E, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ ub ∈ E, ∀ s ∈ c, s ⊆ ub := by
    intro c hcE hch ⟨s₀, hs₀⟩
    refine ⟨⋃₀ c, ⟨?_, ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    · exact Set.Subset.trans (hcE hs₀).1 (Set.subset_sUnion_of_mem hs₀)
    · rw [← not_iff_not, inconsistent_iff_provable_one]
      intro hprov
      obtain ⟨Γ₀, hΓ₀sub, hΓ₀prov⟩ := hprov.compact
      have hmem_s₀ : (s₀ : Set (Formula L)) ∈ c := hs₀
      have hdir : DirectedOn (· ⊆ ·) c := hch.directedOn
      have hex : ∃ t ∈ c, (↑Γ₀ : Set (Formula L)) ⊆ t := by
        induction Γ₀ using Finset.induction with
        | empty => exact ⟨s₀, hs₀, Set.empty_subset _⟩
        | @insert ψ S _ ih =>
          obtain ⟨t₁, ht₁c, ht₁sub⟩ := ih
          have hψ : ψ ∈ ⋃₀ c := hΓ₀sub (by simp)
          obtain ⟨t₂, ht₂c, hψt₂⟩ := Set.mem_sUnion.mp hψ
          obtain ⟨t₃, ht₃c, h₁₃, h₂₃⟩ := hdir t₁ ht₁c t₂ ht₂c
          refine ⟨t₃, ht₃c, ?_⟩
          rw [Finset.coe_insert]
          exact Set.insert_subset (h₂₃ hψt₂) (Set.Subset.trans ht₁sub h₁₃)
      obtain ⟨t, htc, htsub⟩ := hex
      have ht_incons : ¬ ConsistentQ t := by
        rw [inconsistent_iff_provable_one]
        exact hΓ₀prov.mono htsub
      exact ht_incons (hcE htc).2
  have hΓE : Γ ∈ E := ⟨Set.Subset.rfl, hcons⟩
  obtain ⟨Δ, hΓΔ, hmax⟩ := zorn_subset_nonempty E hchain Γ hΓE
  exact ⟨Δ, (maximal_in_consistent_extensions_iff hcons).mp hmax⟩

theorem exists_maximal_consistent_metric {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (hcons : ConsistentMetricQ Γ) :
    ∃ Δ : Set (Formula LM.toSignature), Γ ⊆ Δ ∧ MaximalConsistentMetric Δ := by
  sorry

/-- Remark 8.9: Deductive closure of maximal consistent sets. -/
lemma MaximalConsistent.mem_iff_provable {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (φ : Formula L) :
    φ ∈ Δ ↔ ProvableQ Δ φ := by
  sorry

/-- Lemma 8.11: Instantiation inside maximal consistent sets after bound renaming. -/
theorem maximal_consistent_sup_instantiate {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (t : Term L) (x : Var) (φ : Formula L) (p : DyadicCode)
    (hmem : Formula.tsub (.sup x φ) (Formula.dyadic L p) ∈ Δ) :
    ∃ φ' : Formula L, (φ ≡ᶠ φ') ∧ φ'.rank = φ.rank ∧
      Formula.FreeSubstCorrect φ' t x ∧
      Formula.tsub (φ'.freeSubst t x) (Formula.dyadic L p) ∈ Δ := by
  sorry

/-- Lemma 8.12: Dedekind cut equality of dyadic lower and upper bounds in `Δ`. -/
theorem maximal_consistent_sup_eq_inf {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (φ : Formula L) :
    sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ Formula.tsub (Formula.dyadic L p) φ ∈ Δ} =
    sInf {r : ℝ | ∃ q : DyadicCode, r = q.val ∧ Formula.tsub φ (Formula.dyadic L q) ∈ Δ} := by
  sorry


/-! ## §9: Henkin Completeness and the Completeness Theorem -/

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
  rel_in_Icc := fun P args => M.rel_in_Icc (e.relEquiv P) _

lemma eval_reduct {L₁ L₂ : Signature} (e : SignatureExtension L₁ L₂) (M : PreStructure L₂)
    (σ : Var → M.Carrier) (φ : Formula L₁) :
    φ.eval (e.reductPre M) σ = (e.mapFormula φ).eval M σ := by
  sorry

end SignatureExtension

/-- Definition 9.1: Henkin completeness of a set of formulae `Γ`. -/
def HenkinComplete {L : Signature} (Γ : Set (Formula L)) : Prop :=
  ∀ (φ : Formula L) (x : Var) (p q : DyadicCode),
    p.val < q.val →
    ∃ (c : L.Func) (hc : L.funcArity c = 0),
      let cTerm : Term L := .func c (fun i => (Fin.elim0 (Fin.cast hc i)))
      Formula.minF (.tsub (.sup x φ) (Formula.dyadic L q))
                   (.tsub (Formula.dyadic L p) (φ.freeSubst cTerm x)) ∈ Γ

/-- Proposition 9.2: Existence of a conservative Henkin completion `(L^c, Γ^c)`. -/
theorem exists_henkin_extension (L : Signature) :
    ∃ (Lc : Signature) (ext : SignatureExtension L Lc) (Γc : Set (Formula Lc)),
      (∀ Γ : Set (Formula L), HenkinComplete ((ext.mapFormula '' Γ) ∪ Γc)) ∧
      (∀ Γ : Set (Formula L), ConsistentQ Γ → ConsistentQ ((ext.mapFormula '' Γ) ∪ Γc)) := by
  sorry

theorem exists_henkin_extension_metric (LM : MetricSignature) :
    ∃ (LMc : MetricSignature) (ext : SignatureExtension LM.toSignature LMc.toSignature)
      (hdist : ext.relEquiv LM.distSym = LMc.distSym)
      (Γc : Set (Formula LMc.toSignature)),
      (∀ Γ : Set (Formula LM.toSignature), HenkinComplete ((ext.mapFormula '' Γ) ∪ Γc)) ∧
      (∀ Γ : Set (Formula LM.toSignature),
        ConsistentMetricQ Γ → ConsistentMetricQ ((ext.mapFormula '' Γ) ∪ Γc)) := by
  sorry

/-- Canonical syntactic term pre-structure built from a maximal consistent set `Δ`
    (Proof of Theorem 9.4). -/
def termPreStructure {L : Signature} (Δ : Set (Formula L)) : PreStructure L where
  Carrier    := Term L
  nonempty   := ⟨.var 0⟩
  funcInterp := fun f args => .func f args
  relInterp  := fun P args =>
    sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
      Formula.tsub (Formula.dyadic L p) (.rel P args) ∈ Δ}
  rel_in_Icc := by
    intro P args
    let S := {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
      Formula.tsub (Formula.dyadic L p) (.rel P args) ∈ Δ}
    by_cases hne : S.Nonempty
    · have hbdd : BddAbove S := ⟨1, by rintro _ ⟨p, rfl, _⟩; exact (p.val_mem_Icc).2⟩
      obtain ⟨r₀, p₀, rfl, hp₀⟩ := hne
      exact ⟨le_trans (p₀.val_mem_Icc).1 (le_csSup hbdd ⟨p₀, rfl, hp₀⟩),
             csSup_le hne (by rintro _ ⟨p, rfl, _⟩; exact (p.val_mem_Icc).2)⟩
    · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
      exact ⟨le_rfl, zero_le_one⟩

/-- Canonical identity assignment `σ(x) = x` in the term pre-structure. -/
def idTermAssign (L : Signature) : Var → Term L := Term.var

@[simp] lemma term_eval_idTermAssign {L : Signature} (Δ : Set (Formula L)) (t : Term L) :
    t.eval (termPreStructure Δ) (idTermAssign L) = t := by
  induction t with
  | var x => rfl
  | func f args ih =>
    simp only [Term.eval, termPreStructure]
    congr 1; ext i; exact ih i

/-- Truth Lemma for the Henkin term model (core induction of Theorem 9.4):
    `𝔐(φ, σ) = sup { p ∈ D : p ∸ φ ∈ Δ }`. -/
theorem termPreStructure_eval_eq_sup {L : Signature} {Δ : Set (Formula L)}
    (hmc : MaximalConsistent Δ) (hhenk : HenkinComplete Δ) (φ : Formula L) :
    φ.eval (termPreStructure Δ) (idTermAssign L) =
      sSup {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
        Formula.tsub (Formula.dyadic L p) φ ∈ Δ} := by
  sorry

/-- Theorem 9.4: Every consistent `Γ` extends to a maximal consistent Henkin complete `Δ`
    satisfied by a term pre-structure `(𝔐, σ) ⊨_Q Δ`. -/
theorem henkin_model_existence {L : Signature} {Γ : Set (Formula L)}
    (hcons : ConsistentQ Γ) :
    ∃ (Lc : Signature) (ext : SignatureExtension L Lc) (Δ : Set (Formula Lc))
      (M : PreStructure Lc) (σ : Var → M.Carrier),
      MaximalConsistent Δ ∧ HenkinComplete Δ ∧
      (ext.mapFormula '' Γ) ⊆ Δ ∧ ModelsPre M σ Δ := by
  obtain ⟨Lc, ext, Γc, hhenk, hcons_ext⟩ := exists_henkin_extension L
  obtain ⟨Δ, hsub, hmc⟩ := exists_maximal_consistent (hcons_ext Γ hcons)
  have hhenkΔ : HenkinComplete Δ := by
    intro φ x p q hpq
    obtain ⟨c, hc, hmem⟩ := hhenk Γ φ x p q hpq
    exact ⟨c, hc, hsub hmem⟩
  refine ⟨Lc, ext, Δ, termPreStructure Δ, idTermAssign Lc, hmc, hhenkΔ, ?_, ?_⟩
  · exact Set.Subset.trans Set.subset_union_left hsub
  · intro φ hφ
    rw [termPreStructure_eval_eq_sup hmc hhenkΔ φ, maximal_consistent_sup_eq_inf hmc φ]
    have h0 : Formula.tsub φ (Formula.dyadic Lc .zero) ∈ Δ := by
      sorry
    have hnonneg : ∀ r ∈ {r : ℝ | ∃ q : DyadicCode, r = q.val ∧
        Formula.tsub φ (Formula.dyadic Lc q) ∈ Δ}, 0 ≤ r := by
      rintro _ ⟨q, rfl, _⟩; exact (q.val_mem_Icc).1
    apply le_antisymm
    · exact le_trans (csInf_le ⟨0, hnonneg⟩ ⟨.zero, rfl, h0⟩) (by simp)
    · exact le_csInf ⟨0, .zero, rfl, h0⟩ hnonneg

theorem henkin_model_existence_metric {LM : MetricSignature}
    {Γ : Set (Formula LM.toSignature)} (hcons : ConsistentMetricQ Γ) :
    ∃ (M : MetricPreStructure LM) (σ : Var → M.Carrier),
      ModelsPre M.toPreStructure σ Γ := by
  sorry

/-- Theorem 9.5 (Completeness for Continuous First-Order Logic — without metric). -/
theorem completeness_pre {L : Signature} (Γ : Set (Formula L)) :
    ConsistentQ Γ ↔ SatisfiablePre Γ := by
  refine ⟨?_, satisfiable_consistent_pre Γ⟩
  intro hcons
  obtain ⟨Lc, ext, Δ, M, σ, _, _, hΓΔ, hMΔ⟩ := henkin_model_existence hcons
  refine ⟨ext.reductPre M, σ, ?_⟩
  intro φ hφ
  rw [ext.eval_reduct M σ φ]
  exact hMΔ (ext.mapFormula φ) (hΓΔ ⟨φ, hφ, rfl⟩)

/-- Theorem 9.5 (Completeness for Continuous First-Order Logic — with complete metric). -/
theorem completeness_metric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    ConsistentMetricQ Γ ↔ CompletelySatisfiable Γ := by
  refine ⟨?_, satisfiable_consistent_metric Γ⟩
  intro hcons
  obtain ⟨M, σ, hM⟩ := henkin_model_existence_metric hcons
  exact (satisfiable_metric_iff_complete Γ).mp ⟨M, σ, hM⟩


/-! ## Corollaries 9.6 – 9.12: Strong Completeness, Pavelka Completeness, Decidability, Compactness -/

/-- Auxiliary lemma (cf. proof of Lemma 8.5): if `Γ ∪ {p ∸ φ}` is inconsistent,
    then `Γ ⊢_Q φ ∸ p`. -/
lemma provable_tsub_of_inconsistent_adjoin {L : Signature} (Γ : Set (Formula L))
    (φ : Formula L) (p : DyadicCode)
    (hincons : ¬ ConsistentQ (Γ ∪ {.tsub (Formula.dyadic L p) φ})) :
    ProvableQ Γ (.tsub φ (Formula.dyadic L p)) := by
  sorry

lemma provable_tsub_of_inconsistent_adjoin_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) (p : DyadicCode)
    (hincons : ¬ ConsistentMetricQ (Γ ∪ {.tsub (Formula.dyadic LM.toSignature p) φ})) :
    ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p)) := by
  sorry

/-- Corollary 9.6 (Approximated Strong Completeness — without metric). -/
theorem approximated_strong_completeness_pre {L : Signature}
    (Γ : Set (Formula L)) (φ : Formula L) :
    EntailsPre Γ φ ↔ ∀ n : ℕ, ProvableQ Γ (.tsub φ (Formula.pow2Neg L n)) := by
  constructor
  · intro hent n
    apply provable_tsub_of_inconsistent_adjoin Γ φ (.pow2Neg n)
    rw [completeness_pre]
    rintro ⟨M, σ, hM⟩
    have hφ0 : φ.eval M σ = 0 := hent M σ (fun ψ hψ => hM ψ (Set.mem_union_left _ hψ))
    have hmem : Formula.tsub (Formula.dyadic L (.pow2Neg n)) φ ∈
        Γ ∪ {Formula.tsub (Formula.dyadic L (.pow2Neg n)) φ} :=
      Set.mem_union_right _ (Set.mem_singleton _)
    have hval := hM _ hmem
    simp [Formula.eval, hφ0, tsubR_eq_zero_iff, DyadicCode.val_pow2Neg] at hval
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
    linarith
  · intro hprov M σ hM
    have hle : ∀ n : ℕ, φ.eval M σ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
      intro n
      have hv := soundness_pre Γ _ (hprov n) M σ hM
      simp [Formula.eval, Formula.pow2Neg, tsubR_eq_zero_iff, DyadicCode.val_pow2Neg] at hv
      exact hv
    have hnonneg := (φ.eval_in_Icc M σ).1
    by_contra hne
    have hpos : 0 < φ.eval M σ := lt_of_le_of_ne hnonneg (Ne.symm hne)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (2 : ℝ) ^ (-(n : ℤ)) < φ.eval M σ := by
      sorry
    linarith [hle n]

/-- Corollary 9.6 (Approximated Strong Completeness — with complete metric). -/
theorem approximated_strong_completeness_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (φ : Formula LM.toSignature) :
    EntailsComplete Γ φ ↔
      ∀ n : ℕ, ProvableMetricQ Γ (.tsub φ (Formula.pow2Neg LM.toSignature n)) := by
  constructor
  · intro hent n
    apply provable_tsub_of_inconsistent_adjoin_metric Γ φ (.pow2Neg n)
    rw [completeness_metric]
    rintro ⟨M, σ, hM⟩
    have hφ0 : φ.eval M.toPreStructure σ = 0 :=
      hent M σ (fun ψ hψ => hM ψ (Set.mem_union_left _ hψ))
    have hmem : Formula.tsub (Formula.dyadic LM.toSignature (.pow2Neg n)) φ ∈
        Γ ∪ {Formula.tsub (Formula.dyadic LM.toSignature (.pow2Neg n)) φ} :=
      Set.mem_union_right _ (Set.mem_singleton _)
    have hval := hM _ hmem
    simp [Formula.eval, hφ0, tsubR_eq_zero_iff, DyadicCode.val_pow2Neg] at hval
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(n : ℤ)) := zpow_pos (by norm_num) _
    linarith
  · intro hprov M σ hM
    have hle : ∀ n : ℕ, φ.eval M.toPreStructure σ ≤ (2 : ℝ) ^ (-(n : ℤ)) := by
      intro n
      have hv := soundness_metric Γ _ (hprov n) M σ hM
      simp [Formula.eval, Formula.pow2Neg, tsubR_eq_zero_iff, DyadicCode.val_pow2Neg] at hv
      exact hv
    have hnonneg := (φ.eval_in_Icc M.toPreStructure σ).1
    by_contra hne
    have hpos : 0 < φ.eval M.toPreStructure σ := lt_of_le_of_ne hnonneg (Ne.symm hne)
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (2 : ℝ) ^ (-(n : ℤ)) < φ.eval M.toPreStructure σ := by
      sorry
    linarith [hle n]

/-- Definition 9.7 (i): Degree of truth `φ°_Γ` with respect to `Γ`. -/
def degreeOfTruthPre {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) : ℝ :=
  sSup {r : ℝ | ∃ (M : PreStructure L) (σ : Var → M.Carrier),
    ModelsPre M σ Γ ∧ r = φ.eval M σ}

def degreeOfTruthComplete {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : ℝ :=
  sSup {r : ℝ | ∃ (M : ContinuousStructure LM) (σ : Var → M.Carrier),
    ModelsPre M.toPreStructure σ Γ ∧ r = φ.eval M.toPreStructure σ}

/-- Definition 9.7 (ii): Degree of provability `φ^⊛_Γ` with respect to `Γ`. -/
def degreeOfProvabilityPre {L : Signature} (Γ : Set (Formula L)) (φ : Formula L) : ℝ :=
  sInf {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ ProvableQ Γ (.tsub φ (Formula.dyadic L p))}

def degreeOfProvabilityMetric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature))
    (φ : Formula LM.toSignature) : ℝ :=
  sInf {r : ℝ | ∃ p : DyadicCode, r = p.val ∧
    ProvableMetricQ Γ (.tsub φ (Formula.dyadic LM.toSignature p))}

/-- Corollary 9.8 (Pavelka-style Completeness): `φ°_Γ = φ^⊛_Γ`. -/
theorem pavelka_completeness_pre {L : Signature} (Γ : Set (Formula L))
    (hcons : ConsistentQ Γ) (φ : Formula L) :
    degreeOfTruthPre Γ φ = degreeOfProvabilityPre Γ φ := by
  let ST := {r : ℝ | ∃ (M : PreStructure L) (σ : Var → M.Carrier),
    ModelsPre M σ Γ ∧ r = φ.eval M σ}
  let SP := {r : ℝ | ∃ p : DyadicCode, r = p.val ∧ ProvableQ Γ (.tsub φ (Formula.dyadic L p))}
  obtain ⟨M₀, σ₀, hM₀⟩ := (completeness_pre Γ).mp hcons
  have hST_ne : ST.Nonempty := ⟨φ.eval M₀ σ₀, M₀, σ₀, hM₀, rfl⟩
  have hST_bdd : BddAbove ST := ⟨1, by rintro _ ⟨M, σ, _, rfl⟩; exact (φ.eval_in_Icc M σ).2⟩
  have hSP_ne : SP.Nonempty := by
    refine ⟨1, .one, DyadicCode.val_one.symm, ?_⟩
    sorry
  have hSP_bdd : BddBelow SP := ⟨0, by rintro _ ⟨p, rfl, _⟩; exact (p.val_mem_Icc).1⟩
  apply le_antisymm
  · -- Case (i): φ°_Γ ≤ φ^⊛_Γ
    apply le_csInf hSP_ne
    rintro _ ⟨p, rfl, hprov⟩
    apply csSup_le hST_ne
    rintro _ ⟨M, σ, hM, rfl⟩
    have hv := soundness_pre Γ _ hprov M σ hM
    simpa [Formula.eval, tsubR_eq_zero_iff] using hv
  · -- Case (ii): φ^⊛_Γ ≤ φ°_Γ
    by_contra hlt
    push_neg at hlt
    obtain ⟨p, hp₁, hp₂⟩ := DyadicCode.dense_in_Icc
      (le_trans (φ.eval_in_Icc M₀ σ₀).1 (le_csSup hST_bdd ⟨M₀, σ₀, hM₀, rfl⟩))
      (csInf_le hSP_bdd ⟨.one, DyadicCode.val_one.symm, by sorry⟩ |>.trans (by norm_num))
      hlt
    have hnprov : ¬ ProvableQ Γ (.tsub φ (Formula.dyadic L p)) := by
      intro hp
      have hle : degreeOfProvabilityPre Γ φ ≤ p.val := csInf_le hSP_bdd ⟨p, rfl, hp⟩
      linarith
    have hcons' : ConsistentQ (Γ ∪ {.tsub (Formula.dyadic L p) φ}) := by
      by_contra hinc
      exact hnprov (provable_tsub_of_inconsistent_adjoin Γ φ p hinc)
    obtain ⟨M, σ, hM⟩ := (completeness_pre _).mp hcons'
    have hMΓ : ModelsPre M σ Γ := fun ψ hψ => hM ψ (Set.mem_union_left _ hψ)
    have hpφ : (Formula.tsub (Formula.dyadic L p) φ).eval M σ = 0 :=
      hM _ (Set.mem_union_right _ (Set.mem_singleton _))
    simp [Formula.eval, tsubR_eq_zero_iff] at hpφ
    have hle_sup : φ.eval M σ ≤ degreeOfTruthPre Γ φ := le_csSup hST_bdd ⟨M, σ, hMΓ, rfl⟩
    linarith

theorem pavelka_completeness_metric {LM : MetricSignature}
    (Γ : Set (Formula LM.toSignature)) (hcons : ConsistentMetricQ Γ)
    (φ : Formula LM.toSignature) :
    degreeOfTruthComplete Γ φ = degreeOfProvabilityMetric Γ φ := by
  sorry

/-- Definition 9.9: Sentences, Theories, and Complete Theories. -/
def IsSentence {L : Signature} (φ : Formula L) : Prop := φ.freeVars = ∅

def IsTheory {LM : MetricSignature} (T : Set (Formula LM.toSignature)) : Prop :=
  ∀ φ ∈ T, IsSentence φ

def IsCompleteTheory {LM : MetricSignature} (T : Set (Formula LM.toSignature)) : Prop :=
  IsTheory T ∧ ∃ (M : ContinuousStructure LM) (σ : Var → M.Carrier),
    T = {φ | IsSentence φ ∧ φ.eval M.toPreStructure σ = 0}

/-- Abstract computability predicates for recursive languages and decidable theories
    (Definitions 9.10 & Corollary 9.11). -/
structure RecursivePresentation (LM : MetricSignature) where
  encodeFormula  : Formula LM.toSignature ≃ ℕ
  encodeDyadic   : DyadicCode ≃ ℕ
  axiomRE        : Set ℕ -- r.e. encoding of logical axioms

/-- A theory `T` is decidable if for every sentence `φ`, `φ°_T` is uniformly computable from `φ`
    (modeled via uniformly decidable rational Dedekind cuts / Cauchy approximations). -/
structure UniformlyComputableDegree {LM : MetricSignature}
    (P : RecursivePresentation LM) (T : Set (Formula LM.toSignature)) where
  approx : ℕ → ℕ → DyadicCode
  spec   : ∀ (φ : Formula LM.toSignature), IsSentence φ →
    ∀ n : ℕ, |(approx (P.encodeFormula φ) n).val - degreeOfTruthComplete T φ| ≤ (2 : ℝ) ^ (-(n : ℤ))

/-- Corollary 9.11: Every complete theory with an r.e. axiomatization is decidable. -/
theorem complete_re_theory_decidable {LM : MetricSignature}
    (P : RecursivePresentation LM) (T Ax : Set (Formula LM.toSignature))
    (hcomp : IsCompleteTheory T)
    (hax : ∀ φ, IsSentence φ → (φ ∈ T ↔ EntailsComplete Ax φ)) :
    Nonempty (UniformlyComputableDegree P T) := by
  sorry

/-- Corollary 9.12 (Compactness — without metric). -/
theorem compactness_pre {L : Signature} (Γ : Set (Formula L)) :
    (∀ Γ₀ : Finset (Formula L), (↑Γ₀ : Set (Formula L)) ⊆ Γ → SatisfiablePre (↑Γ₀)) →
    SatisfiablePre Γ := by
  intro hfin
  rw [← completeness_pre]
  by_contra hincons
  rw [inconsistent_iff_provable_one] at hincons
  obtain ⟨Γ₀, hsub, hprov₀⟩ := hincons.compact
  have hcons₀ : ConsistentQ (↑Γ₀ : Set (Formula L)) :=
    satisfiable_consistent_pre _ (hfin Γ₀ hsub)
  have hincons₀ : ¬ ConsistentQ (↑Γ₀ : Set (Formula L)) :=
    (inconsistent_iff_provable_one _).mpr hprov₀
  exact hincons₀ hcons₀

/-- Corollary 9.12 (Compactness — with complete metric). -/
theorem compactness_metric {LM : MetricSignature} (Γ : Set (Formula LM.toSignature)) :
    (∀ Γ₀ : Finset (Formula LM.toSignature),
      (↑Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ → CompletelySatisfiable (↑Γ₀)) →
    CompletelySatisfiable Γ := by
  intro hfin
  rw [← completeness_metric]
  by_contra hincons
  have hprov1 : ProvableMetricQ Γ (Formula.one LM.toSignature) := by
    by_contra hnot
    exact hincons ⟨Formula.one LM.toSignature, hnot⟩
  have hfin_prov : ∃ Γ₀ : Finset (Formula LM.toSignature),
      (↑Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ ∧
      ProvableMetricQ (↑Γ₀) (Formula.one LM.toSignature) := by
    induction hprov1 with
    | ax hax => exact ⟨∅, Set.empty_subset _, .ax hax⟩
    | hyp hmem =>
      exact ⟨{Formula.one LM.toSignature}, Set.singleton_subset_iff.mpr hmem,
             .hyp (Finset.mem_singleton_self _)⟩
    | mp _ _ ih₁ ih₂ =>
      sorry
  -- Clean finite extraction via general compactness of `ProvableMetricQ`:
  have hcompact_metric : ∀ {ψ}, ProvableMetricQ Γ ψ →
      ∃ Γ₀ : Finset (Formula LM.toSignature),
        (↑Γ₀ : Set (Formula LM.toSignature)) ⊆ Γ ∧ ProvableMetricQ (↑Γ₀) ψ := by
    intro ψ hp
    induction hp with
    | ax hax => exact ⟨∅, Set.empty_subset _, .ax hax⟩
    | hyp hmem => exact ⟨{_}, Set.singleton_subset_iff.mpr hmem, .hyp (Finset.mem_singleton_self _)⟩
    | mp _ _ ih₁ ih₂ =>
      obtain ⟨Γ₁, h₁s, hp₁⟩ := ih₁
      obtain ⟨Γ₂, h₂s, hp₂⟩ := ih₂
      have hmono : ∀ {A B : Set (Formula LM.toSignature)} (hab : A ⊆ B) {χ},
          ProvableMetricQ A χ → ProvableMetricQ B χ := by
        intro A B hab χ hd
        induction hd with
        | ax ha => exact .ax ha
        | hyp hm => exact .hyp (hab hm)
        | mp _ _ i1 i2 => exact .mp i1 i2
      refine ⟨Γ₁ ∪ Γ₂, ?_, .mp (hmono ?_ hp₁) (hmono ?_ hp₂)⟩
      · rw [Finset.coe_union]; exact Set.union_subset h₁s h₂s
      · rw [Finset.coe_union]; exact Set.subset_union_left
      · rw [Finset.coe_union]; exact Set.subset_union_right
  obtain ⟨Γ₀, hsub, hprov₀⟩ := hcompact_metric hprov1
  obtain ⟨M, σ, hM⟩ := hfin Γ₀ hsub
  have hv := soundness_metric (↑Γ₀) (Formula.one LM.toSignature) hprov₀ M σ hM
  simp at hv

end ContinuousLogic
