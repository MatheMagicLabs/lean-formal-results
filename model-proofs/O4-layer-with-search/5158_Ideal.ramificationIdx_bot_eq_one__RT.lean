/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_bot_eq_one
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 87
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Ideal
section
variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]
open scoped Classical in

@[simp]
theorem ramificationIdx_bot_eq_one [IsDomain S] : (⊥ : Ideal S).ramificationIdx R = 1 := by
  rw [ramificationIdx_def]
  try dsimp only
  have hI : ((⊥ : Ideal S).under R).map (algebraMap R (Localization.AtPrime (⊥ : Ideal S))) = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [Ideal.under, Ideal.mem_comap, Ideal.mem_bot] at hx
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply R S, hx, map_zero]
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal S)) = ⊥ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]
  have hs : IsSimpleModule (Localization.AtPrime (⊥ : Ideal S))
      (Localization.AtPrime (⊥ : Ideal S) ⧸ (⊥ : Ideal (Localization.AtPrime (⊥ : Ideal S)))) := by
    rw [isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, ← hmax]
    infer_instance
  first
    | rw [hI]
    | erw [hI]
    | simp only [hI]
  first
    | simp [Module.length_eq_one_iff.mpr hs]
    | rw [Module.length_eq_one_iff.mpr hs]; rfl
