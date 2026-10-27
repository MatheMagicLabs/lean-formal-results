/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N3, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have hd : N.depth M =
      sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
    first
    | rfl
    | exact depth_eq_sSup N M
  rw [hd]
  have hfinite (n : ℕ∞) (hn : n < ⊤)
      (h : ∀ i : ℕ, i < n → Subsingleton (Ext N M i)) :
      n ≤ sSup {n : ℕ∞ |
        n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} :=
    le_sSup ⟨hn, h⟩
  refine le_antisymm (sSup_le ?_) (sSup_le ?_)
  · intro n hn
    cases n using ENat.recTopCoe with
    | top =>
      generalize he :
        sSup {n : ℕ∞ |
          n < ⊤ ∧ ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} = a
      cases a using ENat.recTopCoe with
      | top => exact le_rfl
      | coe k =>
        have hb := hfinite (↑(k + 1)) (by simp)
          (fun i _ => hn i (by simp))
        rw [he] at hb
        have : k + 1 ≤ k := by exact_mod_cast hb
        omega
    | coe k => exact hfinite _ (by simp) hn
  · intro n hn
    exact le_sSup hn.2
