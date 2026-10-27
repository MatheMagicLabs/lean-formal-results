/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  change sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} = _
  apply le_antisymm
  · refine sSup_le fun n hn => ?_
    by_cases h : n < ⊤
    · exact le_sSup ⟨h, hn⟩
    · have hn_top : n = ⊤ := top_unique (le_of_not_gt h)
      subst n
      by_contra h
      have hfin :
          sSup {n : ℕ∞ | n < ⊤ ∧
            ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} < ⊤ :=
        lt_of_not_ge h
      generalize hs :
        sSup {n : ℕ∞ | n < ⊤ ∧
          ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} = s at *
      lift s to ℕ using hfin.ne with k
      have hk :
          ((k + 1 : ℕ) : ℕ∞) ≤
            sSup {n : ℕ∞ | n < ⊤ ∧
              ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} :=
        le_sSup ⟨by simp, fun i _ => hn i (by simp)⟩
      rw [hs] at hk
      have : k + 1 ≤ k := by exact_mod_cast hk
      omega
  · exact sSup_le fun n hn => le_sSup hn.2
