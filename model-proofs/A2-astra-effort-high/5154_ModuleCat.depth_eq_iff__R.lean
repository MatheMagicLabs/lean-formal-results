/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 124
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
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

lemma depth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : N.depth M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  have upper (i : ℕ) (hi : Nontrivial (Ext N M i)) :
      N.depth M ≤ (i : ℕ∞) := by
    change sSup {k : ℕ∞ | ∀ j : ℕ, (j : ℕ∞) < k →
      Subsingleton (Ext N M j)} ≤ (i : ℕ∞)
    refine sSup_le fun k hk => ?_
    by_contra h
    have hs := hk i (lt_of_not_ge h)
    obtain ⟨a, b, hab⟩ := hi.exists_pair_ne
    exact hab (hs.elim a b)
  have lower (k : ℕ)
      (hk : ∀ i < k, Subsingleton (Ext N M i)) :
      (k : ℕ∞) ≤ N.depth M := by
    change (k : ℕ∞) ≤ sSup {l : ℕ∞ | ∀ i : ℕ, (i : ℕ∞) < l →
      Subsingleton (Ext N M i)}
    apply le_sSup
    intro i hi
    exact hk i (by exact_mod_cast hi)
  constructor
  · intro hd
    have hsmall : ∀ i < n, Subsingleton (Ext N M i) := by
      intro i hi
      rcases subsingleton_or_nontrivial (Ext N M i) with hs | ht
      · exact hs
      · have h := upper i ht
        rw [hd] at h
        have : n ≤ i := by exact_mod_cast h
        omega
    refine ⟨?_, hsmall⟩
    rcases subsingleton_or_nontrivial (Ext N M n) with hs | ht
    · have hnext : ∀ i < n + 1, Subsingleton (Ext N M i) := by
        intro i hi
        by_cases he : i = n
        · subst i
          exact hs
        · exact hsmall i (by omega)
      have h := lower (n + 1) hnext
      rw [hd] at h
      have : n + 1 ≤ n := by exact_mod_cast h
      omega
    · exact ht
  · rintro ⟨hn, hsmall⟩
    exact le_antisymm (upper n hn) (lower n hsmall)
