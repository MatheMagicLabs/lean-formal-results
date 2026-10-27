/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open IsLocalRing LinearMap Module
universe v u
open RingTheory.Sequence Ideal CategoryTheory Abelian Limits Pointwise ModuleCat IsSMulRegular
variable {R : Type u} [CommRing R] [Small.{v} R]
section depth
namespace ModuleCat
open Classical in

lemma depth_eq_sSup_lt_top (N M : ModuleCat.{v} R) : N.depth M =
    sSup {n : ℕ∞ | n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
  unfold depth
  apply le_antisymm
  · apply sSup_le
    intro n hn
    change (∀ i : ℕ, i < n → Subsingleton (Ext N M i)) at hn
    induction n using ENat.recTopCoe with
    | top =>
        cases hs : sSup {n : ℕ∞ |
            n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)}
            using ENat.recTopCoe with
        | top => simp
        | coe k =>
            have h : ((k + 1 : ℕ) : ℕ∞) ≤
                sSup {n : ℕ∞ |
                  n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
              apply le_sSup
              exact ⟨by simp, fun i _ => hn i (by simp)⟩
            rw [hs] at h
            norm_cast at h
            omega
    | coe k =>
        exact le_sSup ⟨by simp, hn⟩
  · apply sSup_le
    intro n hn
    exact le_sSup hn.2
