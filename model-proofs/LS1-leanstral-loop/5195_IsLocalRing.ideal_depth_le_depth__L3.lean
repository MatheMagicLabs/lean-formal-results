/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsLocalRing.ideal_depth_le_depth
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 375
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 1 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
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
end ModuleCat

lemma IsLocalRing.ideal_depth_le_depth [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (netop : I ≠ ⊤) (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    I.depth M ≤ IsLocalRing.depth M := by
  have hI_le : I ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal netop
  have h_sub : {(List.length rs : ℕ∞) | (rs : List R) (_ : IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ I)} ⊆
      {(List.length rs : ℕ∞) | (rs : List R) (_ : IsRegular M rs) (_ : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R)} := by
    intro n hn
    simp only [Set.mem_setOf_eq] at hn ⊢
    rcases hn with ⟨rs, reg, mem, len⟩
    exact ⟨rs, reg, fun r hr => hI_le (mem r hr), len⟩
  rw [IsLocalRing.ideal_depth_eq_sSup_length_isRegular I netop M,
    IsLocalRing.depth_eq_sSup_length_isRegular M]
  exact sSup_le_sSup h_sub
