/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_bot_eq_one
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 87
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 3 (round 0 = first attempt)
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
  have hp : (⊥ : Ideal S).IsPrime := by
    first
    | infer_instance
    | exact Ideal.isPrime_iff.mpr ⟨bot_ne_top, fun {x y} h => by
        simpa [Ideal.mem_bot, mul_eq_zero] using h⟩
    | exact ⟨bot_ne_top, fun {x y} h => by
        simpa [Ideal.mem_bot, mul_eq_zero] using h⟩
  unfold ramificationIdx
  rw [dif_pos hp]
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal S)) = ⊥ := by
    first
    | rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]
    | rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (⊥ : Ideal S)
        (Localization.AtPrime (⊥ : Ideal S)), Ideal.map_bot]
  have hb : map (algebraMap R (Localization.AtPrime (⊥ : Ideal S)))
      (under R (⊥ : Ideal S)) = ⊥ := by
    rw [eq_bot_iff, Ideal.map_le_iff_le_comap]
    intro x hx
    change algebraMap R S x ∈ (⊥ : Ideal S) at hx
    rw [Ideal.mem_bot] at hx
    rw [Ideal.mem_comap, Ideal.mem_bot,
      IsScalarTower.algebraMap_apply R S (Localization.AtPrime (⊥ : Ideal S)), hx, map_zero]
  rw [hb, ← hm]
  have : IsSimpleModule (Localization.AtPrime (⊥ : Ideal S))
      (Localization.AtPrime (⊥ : Ideal S) ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime (⊥ : Ideal S))) :=
    isSimpleModule_iff_isCoatom.mpr
      (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime (⊥ : Ideal S))).out
  first
  | (rw [Module.length_eq_one_iff.mpr this]; first | rfl | simp)
  | simp
