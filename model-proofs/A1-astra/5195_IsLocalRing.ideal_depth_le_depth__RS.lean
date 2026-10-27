/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsLocalRing.ideal_depth_le_depth
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 375
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
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
end ModuleCat

lemma IsLocalRing.ideal_depth_le_depth [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (netop : I ≠ ⊤) (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    I.depth M ≤ IsLocalRing.depth M := by
  have hI : I ≤ maximalIdeal R := by
    apply IsLocalRing.le_maximalIdeal
    exact netop
  rw [IsLocalRing.ideal_depth_eq_sSup_length_isRegular I netop M,
    IsLocalRing.depth_eq_sSup_length_isRegular M]
  apply sSup_le_sSup
  rintro n ⟨rs, hreg, hmem, rfl⟩
  exact ⟨rs, hreg, fun r hr => hI (hmem r hr), rfl⟩
