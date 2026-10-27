/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 124
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 1 (round 0 = first attempt)
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

lemma depth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : N.depth M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  have hb (i : ℕ) (hi : Nontrivial (Ext N M i)) :
      N.depth M ≤ (i : ℕ∞) := by
    change sSup {d : ℕ∞ | ∀ j : ℕ, (j : ℕ∞) < d →
      Subsingleton (Ext N M j)} ≤ (i : ℕ∞)
    apply sSup_le
    intro d hd
    by_contra hdi
    have hs := hd i (lt_of_not_ge hdi)
    obtain ⟨x, y, hxy⟩ := hi.exists_pair_ne
    exact hxy (@Subsingleton.elim _ hs x y)
  constructor
  · intro h
    have hs : ∀ i < n, Subsingleton (Ext N M i) := by
      intro i hi
      rcases subsingleton_or_nontrivial (Ext N M i) with hsi | hni
      · exact hsi
      · have hle := hb i hni
        rw [h] at hle
        have : n ≤ i := by exact_mod_cast hle
        omega
    refine ⟨?_, hs⟩
    rcases subsingleton_or_nontrivial (Ext N M n) with hsn | hnn
    · have hnext : ((n + 1 : ℕ) : ℕ∞) ≤ N.depth M := by
        change ((n + 1 : ℕ) : ℕ∞) ≤
          sSup {d : ℕ∞ | ∀ j : ℕ, (j : ℕ∞) < d →
            Subsingleton (Ext N M j)}
        apply le_sSup
        intro i hi
        have hi' : i < n + 1 := by exact_mod_cast hi
        by_cases hin : i < n
        · exact hs i hin
        · have hin' : i = n := by omega
          subst i
          exact hsn
      rw [h] at hnext
      have : n + 1 ≤ n := by exact_mod_cast hnext
      omega
    · exact hnn
  · rintro ⟨hn, hs⟩
    apply le_antisymm
    · exact hb n hn
    · change (n : ℕ∞) ≤
        sSup {d : ℕ∞ | ∀ j : ℕ, (j : ℕ∞) < d →
          Subsingleton (Ext N M j)}
      apply le_sSup
      intro i hi
      apply hs i
      exact_mod_cast hi
