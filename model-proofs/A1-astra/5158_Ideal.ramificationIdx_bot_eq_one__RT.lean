/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_bot_eq_one
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 87
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Ideal
section
variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]
open scoped Classical in

@[simp]
theorem ramificationIdx_bot_eq_one [IsDomain S] : (⊥ : Ideal S).ramificationIdx R = 1 := by
  rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
    ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff]
  rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime (⊥ : Ideal S)),
    ← map_map, under_def, map_comap_bot]
  exact Localization.AtPrime.map_eq_maximalIdeal
