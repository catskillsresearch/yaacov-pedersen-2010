/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §4 Fact 4.5 (finite strong completeness for continuous propositional
logic), the completeness direction, reduced to Łukasiewicz logic. Read a
continuous formula as a Łukasiewicz formula whose atoms are the variables and
the `½χ` subformulas (`toLuk`). Add, for every `½χ` that occurs, the
translated instances of (A5) and (A6). Over `[0, 1]` these force the atom `½χ`
to take the value `χ/2`, so the translated premises entail the translated
conclusion in Łukasiewicz logic, which is then provable (finite strong
completeness from Fact 4.1). Substituting back (`ofLuk`) turns that proof into a
continuous-logic proof from `Σ` plus instances of (A5) and (A6).
-/
module

public import ContinuousFOL.LukasiewiczAndContinuous.LukFiniteStrong
public import ContinuousFOL.LukasiewiczAndContinuous.CLPropFormSoundness
public import ContinuousFOL.LukasiewiczAndContinuous.CLPropFormEval

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace CLPropForm

variable {I : Type*}

/-- Read a continuous formula as a Łukasiewicz formula; `½χ` becomes the atom `inr χ`. -/
def toLuk : CLPropForm I → LukPropForm (I ⊕ CLPropForm I)
  | .var i => .var (.inl i)
  | .tsub φ ψ => .tsub (toLuk φ) (toLuk ψ)
  | .neg φ => .neg (toLuk φ)
  | .half φ => .var (.inr φ)

/-- Substitute back: the atom `inr χ` becomes `½χ`. -/
def ofLuk : LukPropForm (I ⊕ CLPropForm I) → CLPropForm I
  | .var (.inl i) => .var i
  | .var (.inr φ) => .half φ
  | .tsub φ ψ => .tsub (ofLuk φ) (ofLuk ψ)
  | .neg φ => .neg (ofLuk φ)

lemma ofLuk_toLuk (φ : CLPropForm I) : ofLuk (toLuk φ) = φ := by
  induction φ with
  | var i => rfl
  | tsub φ ψ ihφ ihψ => simp only [toLuk, ofLuk, ihφ, ihψ]
  | neg φ ih => simp only [toLuk, ofLuk, ih]
  | half φ => rfl

/-- A Łukasiewicz proof becomes a continuous-logic proof after substitution. -/
lemma provable_ofLuk {S : Set (LukPropForm (I ⊕ CLPropForm I))}
    {φ : LukPropForm (I ⊕ CLPropForm I)} (h : LukPropForm.Provable S φ) :
    Provable (ofLuk '' S) (ofLuk φ) := by
  induction h with
  | ax hax =>
    apply Provable.ax
    cases hax with
    | A1 φ ψ => exact IsAxiom.A1 _ _
    | A2 φ ψ χ => exact IsAxiom.A2 _ _ _
    | A3 φ ψ => exact IsAxiom.A3 _ _
    | A4 φ ψ => exact IsAxiom.A4 _ _
  | hyp hm => exact Provable.hyp ⟨_, hm, rfl⟩
  | mp _ _ ih₁ ih₂ => exact Provable.mp ih₁ ih₂

/-- Cut: premises that are provable from `Σ` can be discharged. -/
lemma provable_cut {S T : Set (CLPropForm I)} {φ : CLPropForm I} (h : Provable S φ)
    (hS : ∀ s ∈ S, Provable T s) : Provable T φ := by
  induction h with
  | ax hax => exact Provable.ax hax
  | hyp hm => exact hS _ hm
  | mp _ _ ih₁ ih₂ => exact Provable.mp ih₁ ih₂

/-- The subformulas of a formula. -/
def sub : CLPropForm I → Finset (CLPropForm I)
  | .var i => {.var i}
  | .tsub φ ψ => insert (.tsub φ ψ) (sub φ ∪ sub ψ)
  | .neg φ => insert (.neg φ) (sub φ)
  | .half φ => insert (.half φ) (sub φ)

/-- The instance of (A5) at `χ`. -/
def axA5 (χ : CLPropForm I) : CLPropForm I := .tsub (.half χ) (.tsub χ (.half χ))

/-- The instance of (A6) at `χ`. -/
def axA6 (χ : CLPropForm I) : CLPropForm I := .tsub (.tsub χ (.half χ)) (.half χ)

/-- If the (A5)/(A6) instances hold for every `½χ` occurring in `ψ`, the Łukasiewicz
    reading of `ψ` has the continuous value of `ψ`. -/
lemma eval_toLuk (w : I ⊕ CLPropForm I → ℝ) (hw : ∀ a, 0 ≤ w a ∧ w a ≤ 1)
    (ψ : CLPropForm I)
    (hg : ∀ χ, CLPropForm.half χ ∈ sub ψ →
      LukPropForm.eval w (toLuk (axA5 χ)) = 0 ∧ LukPropForm.eval w (toLuk (axA6 χ)) = 0) :
    LukPropForm.eval w (toLuk ψ) = eval (w ∘ Sum.inl) ψ := by
  induction ψ with
  | var i => rfl
  | tsub φ ψ ihφ ihψ =>
    have h1 := ihφ (fun χ hχ => hg χ (by simp [sub, hχ]))
    have h2 := ihψ (fun χ hχ => hg χ (by simp [sub, hχ]))
    simp only [toLuk, LukPropForm.eval, eval, h1, h2]
  | neg φ ih =>
    have h1 := ih (fun χ hχ => hg χ (by simp [sub, hχ]))
    simp only [toLuk, LukPropForm.eval, eval, h1]
  | half χ ih =>
    have h1 := ih (fun χ' hχ => hg χ' (by simp [sub, hχ]))
    obtain ⟨h5, h6⟩ := hg χ (by simp [sub])
    simp only [axA5, axA6, toLuk, LukPropForm.eval, h1] at h5 h6
    have hy := eval_mem_Icc (w ∘ Sum.inl) (fun i => hw _) χ
    have hh := hw (Sum.inr χ)
    simp only [toLuk, LukPropForm.eval, eval]
    simp only [tsubR, max_def] at h5 h6
    split_ifs at h5 h6 <;> linarith

/-- Completeness direction of Fact 4.5: `Σ ⊨ φ → Σ ⊢ φ` for finite `Σ`. -/
theorem provable_of_entails_finset (hypSet : Finset (CLPropForm I)) (φ : CLPropForm I)
    (h : Entails (↑hypSet : Set (CLPropForm I)) φ) :
    Provable (↑hypSet : Set (CLPropForm I)) φ := by
  -- every formula involved, with its subformulas
  let C : Finset (CLPropForm I) := hypSet.biUnion sub ∪ sub φ
  -- the (A5)/(A6) instances for the `½χ` in `C`
  let hax : CLPropForm I → Finset (CLPropForm I) := fun ψ =>
    match ψ with
    | .half χ => {axA5 χ, axA6 χ}
    | _ => ∅
  let H : Finset (CLPropForm I) := C.biUnion hax
  let L : Finset (LukPropForm (I ⊕ CLPropForm I)) := (hypSet ∪ H).image toLuk
  have hH : ∀ χ, CLPropForm.half χ ∈ C → axA5 χ ∈ H ∧ axA6 χ ∈ H := by
    intro χ hχ
    refine ⟨Finset.mem_biUnion.mpr ⟨_, hχ, ?_⟩, Finset.mem_biUnion.mpr ⟨_, hχ, ?_⟩⟩ <;>
      simp [hax]
  have hgood : ∀ (w : I ⊕ CLPropForm I → ℝ), LukPropForm.Models w (↑L) →
      ∀ ψ, sub ψ ⊆ C → ∀ χ, CLPropForm.half χ ∈ sub ψ →
        LukPropForm.eval w (toLuk (axA5 χ)) = 0 ∧ LukPropForm.eval w (toLuk (axA6 χ)) = 0 := by
    intro w hw ψ hψ χ hχ
    obtain ⟨h5, h6⟩ := hH χ (hψ hχ)
    refine ⟨hw.2 _ ?_, hw.2 _ ?_⟩
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, Finset.mem_union_right _ h5, rfl⟩)
    · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨_, Finset.mem_union_right _ h6, rfl⟩)
  have hsem : LukPropForm.Entails (↑L : Set (LukPropForm (I ⊕ CLPropForm I))) (toLuk φ) := by
    intro w hw
    have hφC : sub φ ⊆ C := Finset.subset_union_right
    have hSC : ∀ s ∈ hypSet, sub s ⊆ C := fun s hs =>
      (Finset.subset_biUnion_of_mem sub hs).trans Finset.subset_union_left
    rw [eval_toLuk w hw.1 φ (hgood w hw φ hφC)]
    apply h
    refine ⟨fun i => hw.1 _, fun s hs => ?_⟩
    rw [← eval_toLuk w hw.1 s (hgood w hw s (hSC s hs))]
    exact hw.2 _ (Finset.mem_coe.mpr
      (Finset.mem_image.mpr ⟨_, Finset.mem_union_left _ (Finset.mem_coe.mp hs), rfl⟩))
  have hprov := provable_ofLuk (LukPropForm.provable_of_entails_finset L (toLuk φ) hsem)
  rw [ofLuk_toLuk] at hprov
  refine provable_cut hprov ?_
  rintro _ ⟨θ, hθ, rfl⟩
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hθ)
  rw [ofLuk_toLuk]
  rcases Finset.mem_union.mp ht with ht | ht
  · exact Provable.hyp (Finset.mem_coe.mpr ht)
  · obtain ⟨ψ, -, hψ⟩ := Finset.mem_biUnion.mp ht
    cases ψ with
    | half χ =>
      simp only [hax, Finset.mem_insert, Finset.mem_singleton] at hψ
      rcases hψ with rfl | rfl
      · exact Provable.ax (IsAxiom.A5 χ)
      · exact Provable.ax (IsAxiom.A6 χ)
    | var _ => simp [hax] at hψ
    | tsub _ _ => simp [hax] at hψ
    | neg _ => simp [hax] at hψ

/-- Fact 4.5 (proof): `Σ ⊨ φ ↔ Σ ⊢ φ` for finite `Σ`. -/
theorem entails_finset_iff_provable (hypSet : Finset (CLPropForm I)) (φ : CLPropForm I) :
    Entails (↑hypSet : Set (CLPropForm I)) φ ↔ Provable (↑hypSet : Set (CLPropForm I)) φ :=
  ⟨provable_of_entails_finset hypSet φ, soundness⟩

end CLPropForm

end ContinuousFOL
