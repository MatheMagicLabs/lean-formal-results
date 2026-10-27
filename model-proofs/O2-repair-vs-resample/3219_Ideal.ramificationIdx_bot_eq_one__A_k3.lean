/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_bot_eq_one
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 87
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[simp]
theorem ramificationIdx_bot_eq_one [IsDomain S] : (⊥ : Ideal S).ramificationIdx R = 1 := by
  rw [ramificationIdx_def, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff,
    isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff,
    ← Localization.AtPrime.map_eq_maximalIdeal (I := (⊥ : Ideal S)), Ideal.map_bot]
  apply le_antisymm _ bot_le
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have h : algebraMap R S x = 0 := Ideal.mem_bot.mp (Ideal.mem_comap.mp hx)
  rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply R S (Localization.AtPrime (⊥ : Ideal S)),
    h, map_zero]
  exact Submodule.zero_mem _
