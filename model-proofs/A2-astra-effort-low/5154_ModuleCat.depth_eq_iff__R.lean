/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 124
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

lemma depth_eq_iff (N M : ModuleCat.{v} R) (n : ℕ) : N.depth M = n ↔
    Nontrivial (Ext N M n) ∧ ∀ i < n, Subsingleton (Ext N M i) := by
  classical
  change sSup {a : ℕ∞ | ∀ i : ℕ, (i : ℕ∞) < a →
    Subsingleton (Ext N M i)} = (n : ℕ∞) ↔ _
  constructor
  · intro h
    have hs : ∀ i < n, Subsingleton (Ext N M i) := by
      intro i hi
      by_contra hsi
      have hb : sSup {a : ℕ∞ | ∀ j : ℕ, (j : ℕ∞) < a →
          Subsingleton (Ext N M j)} ≤ (i : ℕ∞) := by
        refine sSup_le fun a ha => le_of_not_gt fun hia => ?_
        exact hsi (ha i hia)
      rw [h] at hb
      have hb' : n ≤ i := by exact_mod_cast hb
      omega
    refine ⟨?_, hs⟩
    by_contra hn
    have hsn : Subsingleton (Ext N M n) := by
      by_contra hsn
      exact hn (not_subsingleton_iff_nontrivial.mp hsn)
    have hb : ((n + 1 : ℕ) : ℕ∞) ≤
        sSup {a : ℕ∞ | ∀ i : ℕ, (i : ℕ∞) < a →
          Subsingleton (Ext N M i)} := by
      apply le_sSup
      intro i hi
      have hi' : i < n + 1 := by exact_mod_cast hi
      by_cases hin : i < n
      · exact hs i hin
      · have he : i = n := by omega
        subst i
        exact hsn
    rw [h] at hb
    have hb' : n + 1 ≤ n := by exact_mod_cast hb
    omega
  · rintro ⟨hn, hs⟩
    apply le_antisymm
    · refine sSup_le fun a ha => le_of_not_gt fun hna => ?_
      exact (not_subsingleton_iff_nontrivial.mpr hn) (ha n hna)
    · apply le_sSup
      intro i hi
      exact hs i (by exact_mod_cast hi)
