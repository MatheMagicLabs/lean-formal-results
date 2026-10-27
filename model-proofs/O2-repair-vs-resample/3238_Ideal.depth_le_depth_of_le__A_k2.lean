/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.depth_le_depth_of_le
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 359
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Ideal.depth_le_depth_of_le [IsNoetherianRing R] {I J : Ideal R} (h : I ≤ J)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : J • (⊤ : Submodule R M) < ⊤) :
    I.depth M ≤ J.depth M := by
  have smul_lt' : I • (⊤ : Submodule R M) < ⊤ :=
    lt_of_le_of_lt (Submodule.smul_mono h (le_refl _)) smul_lt
  rw [Ideal.depth_eq_sSup_length_isRegular I M smul_lt',
    Ideal.depth_eq_sSup_length_isRegular J M smul_lt]
  apply sSup_le_sSup
  rintro _ ⟨rs, reg, mem, rfl⟩
  exact ⟨rs, reg, fun r hr ↦ h (mem r hr), rfl⟩
