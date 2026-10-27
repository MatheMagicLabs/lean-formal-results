/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsLocalRing.ideal_depth_le_depth
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 375
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L1, verified in round 1 (round 0 = first attempt)
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
  have hle : I ≤ IsLocalRing.maximalIdeal R :=
    IsLocalRing.le_maximalIdeal netop
  have hsmul : (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) < ⊤ := by
    have hle_jacobson : IsLocalRing.maximalIdeal R ≤ (Module.annihilator R M).jacobson :=
      IsLocalRing.maximalIdeal_le_jacobson (Module.annihilator R M)
    have hne := Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator hle_jacobson
    exact lt_of_le_of_ne le_top hne.symm
  exact Ideal.depth_le_depth_of_le hle M hsmul
