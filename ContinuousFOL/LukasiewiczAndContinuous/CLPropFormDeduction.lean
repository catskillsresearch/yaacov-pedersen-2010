/-
Copyright (c) 2026 Lars Warren Ericson. All rights reserved.
Released under Apache 2.0 license as described in file LICENSE.

Paper pin: §3 / the propositional form of Theorem 8.1, for continuous propositional logic;
vision.md page 16. The (A1)–(A4) Hilbert steps are the same as in the Łukasiewicz case.
-/
module

public import ContinuousFOL.Group1Axioms.CLPropForm.Provable
public import ContinuousFOL.Group1Axioms.CLPropForm.IterSub
public import ContinuousFOL.LukasiewiczAndContinuous.CLPropFormEval
public import ContinuousFOL.Introduction.TsubR
public import Mathlib.Data.Finset.Basic

@[expose] public section

noncomputable section
open Classical

namespace ContinuousFOL

namespace CLPropForm

/-- Łukasiewicz implication `φ → ψ` as `ψ ∸ φ` (0 = true). -/
abbrev Imp {I : Type*} (φ ψ : CLPropForm I) : CLPropForm I := .tsub ψ φ

/-- Łukasiewicz disjunction `φ ∨ ψ` as `(φ → ψ) → ψ`. -/
abbrev OrF {I : Type*} (φ ψ : CLPropForm I) : CLPropForm I := Imp (Imp φ ψ) ψ

lemma mono {I : Type*} {Γ Γ' : Set (CLPropForm I)} (hsub : Γ ⊆ Γ')
    {φ : CLPropForm I} (h : Provable Γ φ) : Provable Γ' φ := by
  induction h with
  | ax hax => exact .ax hax
  | hyp hmem => exact .hyp (hsub hmem)
  | mp _ _ ih₁ ih₂ => exact .mp ih₁ ih₂

lemma compact {I : Type*} {Γ : Set (CLPropForm I)} {φ : CLPropForm I}
    (h : Provable Γ φ) :
    ∃ Γ₀ : Finset (CLPropForm I), (↑Γ₀ : Set (CLPropForm I)) ⊆ Γ ∧ Provable ↑Γ₀ φ := by
  induction h with
  | ax hax => exact ⟨∅, by simp [Finset.coe_empty], .ax hax⟩
  | hyp hmem =>
    refine ⟨{_}, ?_, .hyp (Finset.mem_singleton_self _)⟩
    simpa [Finset.coe_singleton] using Set.singleton_subset_iff.mpr hmem
  | mp _ _ ih₁ ih₂ =>
    obtain ⟨Γ₁, h₁s, hp₁⟩ := ih₁
    obtain ⟨Γ₂, h₂s, hp₂⟩ := ih₂
    refine ⟨Γ₁ ∪ Γ₂, ?_, .mp (mono ?_ hp₁) (mono ?_ hp₂)⟩
    · simpa [Finset.coe_union] using Set.union_subset h₁s h₂s
    · simp [Finset.coe_union]
    · simp [Finset.coe_union]

lemma ax0 {I : Type*} {Γ : Set (CLPropForm I)} {φ : CLPropForm I}
    (h : IsAxiom φ) : Provable Γ φ :=
  .ax h

lemma imp_mp {I : Type*} {Γ : Set (CLPropForm I)} {φ ψ : CLPropForm I}
    (hφ : Provable Γ φ) (himp : Provable Γ (Imp φ ψ)) : Provable Γ ψ :=
  Provable.mp hφ himp

/-- Syllogism (Rose–Rosser 2.1): A2 is `(φ → ψ) → ((ψ → χ) → (φ → χ))`. -/
lemma imp_trans {I : Type*} {Γ : Set (CLPropForm I)} {φ ψ χ : CLPropForm I}
    (hab : Provable Γ (Imp φ ψ)) (hbc : Provable Γ (Imp ψ χ)) :
    Provable Γ (Imp φ χ) :=
  imp_mp hbc (imp_mp hab (ax0 (.A2 φ ψ χ)))

/-- Rose–Rosser (2.4): `⊢ φ → (ψ ∨ φ)`. -/
lemma imp_or_swap {I : Type*} {Γ : Set (CLPropForm I)} (φ ψ : CLPropForm I) :
    Provable Γ (Imp φ (OrF ψ φ)) :=
  ax0 (.A1 φ (Imp ψ φ))

/-- Rose–Rosser (2.5): `⊢ φ → (φ ∨ ψ)`. -/
lemma imp_or {I : Type*} {Γ : Set (CLPropForm I)} (φ ψ : CLPropForm I) :
    Provable Γ (Imp φ (OrF φ ψ)) :=
  imp_trans (imp_or_swap (Γ := Γ) φ ψ) (ax0 (.A3 ψ φ))

/-- Rose–Rosser (2.6): `⊢ (φ → (ψ → χ)) → (ψ → (φ → χ))`. -/
lemma imp_perm_schema {I : Type*} {Γ : Set (CLPropForm I)} (φ ψ χ : CLPropForm I) :
    Provable Γ (Imp (Imp φ (Imp ψ χ)) (Imp ψ (Imp φ χ))) := by
  have y : Provable Γ (Imp (Imp φ (Imp ψ χ)) (Imp (OrF ψ χ) (Imp φ χ))) :=
    ax0 (.A2 φ (Imp ψ χ) χ)
  have x : Provable Γ (Imp (Imp (OrF ψ χ) (Imp φ χ)) (Imp ψ (Imp φ χ))) :=
    imp_mp (imp_or (Γ := Γ) ψ χ) (ax0 (.A2 ψ (OrF ψ χ) (Imp φ χ)))
  exact imp_trans y x

lemma imp_perm {I : Type*} {Γ : Set (CLPropForm I)} {φ ψ χ : CLPropForm I}
    (h : Provable Γ (Imp φ (Imp ψ χ))) : Provable Γ (Imp ψ (Imp φ χ)) :=
  imp_mp h (imp_perm_schema (Γ := Γ) φ ψ χ)

/-- Rose–Rosser (2.10): `⊢ φ → φ`, i.e. `⊢ φ ∸ φ`. -/
lemma imp_refl {I : Type*} {Γ : Set (CLPropForm I)} (φ : CLPropForm I) :
    Provable Γ (Imp φ φ) := by
  let ψ : CLPropForm I := Imp φ (Imp φ φ)
  have hweak : Provable Γ (Imp ψ (Imp φ φ)) :=
    imp_mp (ax0 (.A1 φ ψ)) (imp_perm_schema (Γ := Γ) φ ψ φ)
  exact imp_mp (ax0 (.A1 φ φ)) hweak

/-- `(φ → ψ) → ((χ → φ) → (χ → ψ))`. -/
lemma imp_suffix {I : Type*} {Γ : Set (CLPropForm I)} (φ ψ χ : CLPropForm I) :
    Provable Γ (Imp (Imp φ ψ) (Imp (Imp χ φ) (Imp χ ψ))) :=
  imp_perm (ax0 (.A2 χ φ ψ))

/-- Congruence in the left argument of `∸`: `(φ → ψ) → ((φ ∸ α) → (ψ ∸ α))`. -/
lemma imp_tsub_left {I : Type*} {Γ : Set (CLPropForm I)} (φ ψ α : CLPropForm I) :
    Provable Γ (Imp (Imp φ ψ) (Imp (φ.tsub α) (ψ.tsub α))) :=
  imp_suffix φ ψ α

lemma imp_mp_of_iff {I : Type*} {Γ : Set (CLPropForm I)} {φ ψ : CLPropForm I}
    (hφψ : Provable Γ (Imp φ ψ)) (h : Provable Γ φ) : Provable Γ ψ :=
  imp_mp h hφψ

/-- Monotonicity of iteration: `(φ → ψ) → ((φ ⊖_n α) → (ψ ⊖_n α))`. -/
lemma iter_mono_imp {I : Type*} {Γ : Set (CLPropForm I)}
    (φ ψ α : CLPropForm I) (n : ℕ) :
    Provable Γ (Imp (Imp φ ψ) (Imp (iterSub φ α n) (iterSub ψ α n))) := by
  induction n with
  | zero =>
    simpa [iterSub] using imp_refl (Γ := Γ) (Imp φ ψ)
  | succ n ih =>
    -- IH: (φ → ψ) → ((φ ⊖_n α) → (ψ ⊖_n α))
    -- and (β → γ) → ((β ∸ α) → (γ ∸ α)).
    have hstep : Provable Γ
        (Imp (Imp (iterSub φ α n) (iterSub ψ α n))
          (Imp (iterSub φ α n |>.tsub α) (iterSub ψ α n |>.tsub α))) :=
      imp_tsub_left (iterSub φ α n) (iterSub ψ α n) α
    have h := imp_trans ih hstep
    simpa [iterSub] using h

/-- From `⊢ φ → ψ` and `⊢ φ ⊖_n α` get `⊢ ψ ⊖_n α`. -/
lemma iter_mono {I : Type*} {Γ : Set (CLPropForm I)} {φ ψ α : CLPropForm I}
    (h : Provable Γ (Imp φ ψ)) (n : ℕ) (hn : Provable Γ (iterSub φ α n)) :
    Provable Γ (iterSub ψ α n) :=
  imp_mp hn (imp_mp h (iter_mono_imp (Γ := Γ) φ ψ α n))

/-- One-step commutation: `((β ∸ γ) ∸ α) → ((β ∸ α) ∸ γ)`. -/
lemma tsub_comm_imp {I : Type*} {Γ : Set (CLPropForm I)} (β γ α : CLPropForm I) :
    Provable Γ (Imp ((β.tsub γ).tsub α) ((β.tsub α).tsub γ)) :=
  imp_perm_schema (Γ := Γ) α γ β

/-- `(β ∸ γ) ⊖_n α` implies `(β ⊖_n α) ∸ γ`. -/
lemma iterSub_tsub_comm_imp {I : Type*} {Γ : Set (CLPropForm I)}
    (β γ α : CLPropForm I) (n : ℕ) :
    Provable Γ (Imp (iterSub (β.tsub γ) α n) ((iterSub β α n).tsub γ)) := by
  induction n with
  | zero =>
    simpa [iterSub] using imp_refl (Γ := Γ) (β.tsub γ)
  | succ n ih =>
    -- left: ((β ∸ γ) ⊖_n α) ∸ α
    -- IH: ((β ∸ γ) ⊖_n α) → ((β ⊖_n α) ∸ γ)
    -- so left → (((β ⊖_n α) ∸ γ) ∸ α), then commute to ((β ⊖_n α) ∸ α) ∸ γ.
    have hcong : Provable Γ
        (Imp (iterSub (β.tsub γ) α n |>.tsub α)
          (((iterSub β α n).tsub γ).tsub α)) :=
      imp_mp ih (imp_tsub_left (iterSub (β.tsub γ) α n) ((iterSub β α n).tsub γ) α)
    have hcomm : Provable Γ
        (Imp (((iterSub β α n).tsub γ).tsub α)
          (((iterSub β α n).tsub α).tsub γ)) :=
      tsub_comm_imp (iterSub β α n) γ α
    have h := imp_trans hcong hcomm
    simpa [iterSub] using h

lemma iterSub_tsub_comm {I : Type*} {Γ : Set (CLPropForm I)} {β γ α : CLPropForm I}
    (n : ℕ) (h : Provable Γ (iterSub (β.tsub γ) α n)) :
    Provable Γ ((iterSub β α n).tsub γ) :=
  imp_mp h (iterSub_tsub_comm_imp (Γ := Γ) β γ α n)

/-- From `⊢ β ∸ γ` and `⊢ γ ⊖_m α` get `⊢ β ⊖_m α`. -/
lemma iter_trans {I : Type*} {Γ : Set (CLPropForm I)} {β γ α : CLPropForm I}
    (hβγ : Provable Γ (β.tsub γ)) (m : ℕ) (hγ : Provable Γ (iterSub γ α m)) :
    Provable Γ (iterSub β α m) :=
  iter_mono (ψ := β) hβγ m hγ

/-- Folding iterations: `(β ⊖_n α) ⊖_m α = β ⊖_{n+m} α`. -/
lemma iterSub_add {I : Type*} (β α : CLPropForm I) (n m : ℕ) :
    iterSub (iterSub β α n) α m = iterSub β α (n + m) := by
  induction m with
  | zero => simp [iterSub]
  | succ m ih =>
    rw [iterSub, ih, Nat.add_succ, iterSub]

/-- Combine two iterated cuts: from `⊢ (β ∸ γ) ⊖_n α` and `⊢ γ ⊖_m α`
    get `⊢ β ⊖_{n+m} α`. -/
lemma iter_combine {I : Type*} {Γ : Set (CLPropForm I)} {β γ α : CLPropForm I}
    (n m : ℕ) (hn : Provable Γ (iterSub (β.tsub γ) α n))
    (hm : Provable Γ (iterSub γ α m)) :
    Provable Γ (iterSub β α (n + m)) := by
  have hcomm := iterSub_tsub_comm (Γ := Γ) n hn
  have h := iter_trans (β := iterSub β α n) hcomm m hm
  simpa [iterSub_add] using h

lemma cancel_iterSub {I : Type*} {Γ : Set (CLPropForm I)} {φ ψ : CLPropForm I}
    (hψ : Provable Γ ψ) (n : ℕ) (h : Provable Γ (iterSub φ ψ n)) :
    Provable Γ φ := by
  induction n generalizing φ with
  | zero =>
    simpa [iterSub] using h
  | succ n ih =>
    have hstep : Provable Γ (iterSub φ ψ n) := by
      simpa [iterSub] using Provable.mp hψ h
    exact ih hstep

/-- Evaluation of iterated truncated subtraction. -/
lemma eval_iterSub {I : Type*} (v₀ : I → ℝ) (ψ φ : CLPropForm I) (k : ℕ) :
    eval v₀ (iterSub ψ φ k) = iterSubR (eval v₀ ψ) (eval v₀ φ) k := by
  induction k with
  | zero => simp [iterSub, iterSubR]
  | succ k ih => simp [iterSub, iterSubR, eval, ih]

/-- Weak deduction theorem for continuous propositional logic (cf. Theorem 8.1):
    `Γ ∪ {ψ} ⊢ φ` iff `Γ ⊢ φ ∸ nψ` for some `n`. -/
theorem deduction_theorem {I : Type*} (Γ : Set (CLPropForm I)) (φ ψ : CLPropForm I) :
    Provable (Γ ∪ {ψ}) φ ↔ ∃ n : ℕ, Provable Γ (iterSub φ ψ n) := by
  constructor
  · intro h
    induction h with
    | ax hax =>
      exact ⟨0, by simpa [iterSub] using (ax0 (Γ := Γ) hax)⟩
    | hyp hmem =>
      rename_i θ
      rcases (Set.mem_union θ Γ {ψ}).mp hmem with hΓ | hψ
      · exact ⟨0, by simpa [iterSub] using Provable.hyp hΓ⟩
      · have hθeq : θ = ψ := by simpa [Set.mem_singleton_iff] using hψ
        exact ⟨1, by simpa [hθeq, iterSub] using (imp_refl (Γ := Γ) ψ)⟩
    | mp hα himp ihα ihimp =>
      rename_i α β
      obtain ⟨n, hn⟩ := ihα
      obtain ⟨m, hm⟩ := ihimp
      -- `himp` is `Provable (Γ ∪ {ψ}) (β ∸ α)`, so the IH gives `(β ∸ α) ⊖_m ψ`.
      exact ⟨m + n, iter_combine m n hm hn⟩
  · rintro ⟨n, hn⟩
    exact cancel_iterSub (.hyp (Set.mem_union_right _ (Set.mem_singleton _))) n
      (mono (by intro θ hθ; exact Set.mem_union_left _ hθ) hn)

end CLPropForm

end ContinuousFOL
