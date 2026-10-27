/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsLocalRing.ideal_depth_le_depth
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 375
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma IsLocalRing.ideal_depth_le_depth [IsLocalRing R] [IsNoetherianRing R]
    (I : Ideal R) (netop : I ≠ ⊤) (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M] :
    I.depth M ≤ IsLocalRing.depth M := by
  show I.depth M ≤ (maximalIdeal R).depth M
  exact Ideal.depth_le_depth_of_le (le_maximalIdeal netop) M
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).lt_top'
