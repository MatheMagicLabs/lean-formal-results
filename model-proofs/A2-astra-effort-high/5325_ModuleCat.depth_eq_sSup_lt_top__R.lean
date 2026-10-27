/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_sSup_lt_top
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 144
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  first
  | change sSup {n : ℕ∞ | ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} = _
  | rw [depth_eq_sSup]
  refine le_antisymm ?_ (sSup_le fun n hn => le_sSup hn.2)
  generalize hb :
    sSup {n : ℕ∞ | n < ⊤ ∧
      ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} = b
  by_cases htop : b = ⊤
  · simp [htop]
  lift b to ℕ using htop with k
  refine sSup_le fun n hn => ?_
  by_contra h
  have hkn : (k : ℕ∞) < n := lt_of_not_ge h
  have hmem : ((k + 1 : ℕ) : ℕ∞) ∈
      {n : ℕ∞ | n < ⊤ ∧
        ∀ i : ℕ, i < n → Subsingleton (Ext N M i)} := by
    refine ⟨by simp, ?_⟩
    intro i hi
    have hi' : i < k + 1 := by exact_mod_cast hi
    have hik : (i : ℕ∞) ≤ (k : ℕ∞) := by
      exact_mod_cast Nat.le_of_lt_succ hi'
    exact hn i (lt_of_le_of_lt hik hkn)
  have hle : ((k + 1 : ℕ) : ℕ∞) ≤ (k : ℕ∞) := by
    rw [← hb]
    exact le_sSup hmem
  have hle' : k + 1 ≤ k := by exact_mod_cast hle
  exact (Nat.not_succ_le_self k) hle'
