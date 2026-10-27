/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_le_depth_of_le
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 359
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
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

lemma Ideal.depth_le_depth_of_le [IsNoetherianRing R] {I J : Ideal R} (h : I ≤ J)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : J • (⊤ : Submodule R M) < ⊤) :
    I.depth M ≤ J.depth M := by
  have hI : I • (⊤ : Submodule R M) < ⊤ :=
    lt_of_le_of_lt (Submodule.smul_mono h le_rfl) smul_lt
  rw [Ideal.depth_eq_sSup_length_isRegular I M hI,
    Ideal.depth_eq_sSup_length_isRegular J M smul_lt]
  apply sSup_le_sSup
  rintro n ⟨rs, hreg, hmem, rfl⟩
  exact ⟨rs, hreg, fun r hr => h (hmem r hr), rfl⟩
