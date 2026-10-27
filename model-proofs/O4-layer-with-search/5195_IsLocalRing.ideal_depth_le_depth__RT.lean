/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsLocalRing.ideal_depth_le_depth
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 375
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  have hJ : Module.annihilator R M ≠ ⊤ := by
    rw [Ne, Module.annihilator_eq_top_iff]
    exact not_subsingleton M
  have hlt : (maximalIdeal R) • (⊤ : Submodule R M) < ⊤ :=
    lt_top_iff_ne_top.mpr
      (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
        (IsLocalRing.jacobson_eq_maximalIdeal _ hJ).ge).symm
  exact Ideal.depth_le_depth_of_le (le_maximalIdeal netop) M hlt
