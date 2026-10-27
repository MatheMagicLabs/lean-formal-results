/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.ObjectProperty.hasFiniteResolutionOfLength.iff_hasProjectiveDimensionLE
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/ObjectProperty/HasFiniteResolution/Projective.lean, line 29
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem iff_hasProjectiveDimensionLE [EnoughProjectives A] :
    (isProjective A).hasFiniteResolutionOfLength n X ↔ HasProjectiveDimensionLE X n := by
  refine ⟨hasProjectiveDimensionLE, fun h => ?_⟩
  induction n generalizing X with
  | zero =>
    exact ObjectProperty.hasFiniteResolutionOfLength.zero X
      (projective_iff_hasProjectiveDimensionLT_one.2 h)
  | succ n ih =>
    let S := ShortComplex.mk (kernel.ι (Projective.π X)) (Projective.π X) (kernel.condition _)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }
    have : HasProjectiveDimensionLE S.X₁ n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n (Projective.projective_over X)).1 h
    exact ObjectProperty.hasFiniteResolutionOfLength.succ S n hS
      (Projective.projective_over X) (ih this)
