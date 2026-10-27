/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_bot_eq_one
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 87
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Ideal
section
variable {S : Type*} [CommRing S] (q : Ideal S) (R : Type*) [CommRing R] [Algebra R S]
open scoped Classical in

@[simp]
theorem ramificationIdx_bot_eq_one [IsDomain S] : (⊥ : Ideal S).ramificationIdx R = 1 := by
  classical
  unfold ramificationIdx
  have hp : (⊥ : Ideal S).IsPrime := inferInstance
  rw [dif_pos hp]
  have hI : map (algebraMap R (Localization.AtPrime (⊥ : Ideal S))) ((⊥ : Ideal S).under R)
      = IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal S)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (⊥ : Ideal S), Ideal.map_bot,
      eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro r hr
    change algebraMap R S r ∈ (⊥ : Ideal S) at hr
    rw [Ideal.mem_bot] at hr
    change algebraMap R (Localization.AtPrime (⊥ : Ideal S)) r ∈ (⊥ : Ideal _)
    rw [Ideal.mem_bot, IsScalarTower.algebraMap_apply R S, hr, map_zero]
  rw [hI]
  have hs : IsSimpleModule (Localization.AtPrime (⊥ : Ideal S))
      (Localization.AtPrime (⊥ : Ideal S) ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal S))) :=
    isSimpleModule_iff_isCoatom.mpr
      (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime (⊥ : Ideal S))).out
  rw [Module.length_eq_one_iff.mpr hs]
  rfl
