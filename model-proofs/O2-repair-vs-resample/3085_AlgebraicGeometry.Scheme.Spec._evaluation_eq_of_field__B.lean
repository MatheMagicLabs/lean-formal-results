/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Spec.Γevaluation_eq_of_field
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 328
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Spec.Γevaluation_eq_of_field {k : Type u} [Field k] (x : Spec (.of k)) :
    haveI := x.isPrime
    (Spec (.of k)).Γevaluation x = (Scheme.ΓSpecIso (.of k)).hom ≫
      (Ideal.algEquivResidueFieldOfField x.asIdeal).toRingEquiv.toCommRingCatIso.hom ≫
        (Spec.residueFieldIso (.of k) x).inv := by
  rw [← Iso.inv_comp_eq]
  dsimp only [Γevaluation, evaluation]
  rw [← Spec.algebraMap_residueFieldIso_inv]
  congr 1
