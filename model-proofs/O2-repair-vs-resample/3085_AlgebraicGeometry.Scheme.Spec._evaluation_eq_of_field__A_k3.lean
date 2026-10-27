/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Spec.Γevaluation_eq_of_field
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 328
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
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
  haveI := x.isPrime
  have this : (Ideal.algEquivResidueFieldOfField x.asIdeal).toRingEquiv.toCommRingCatIso.hom =
      CommRingCat.ofHom (algebraMap (CommRingCat.of k) x.asIdeal.ResidueField) := by
    ext a
    first
      | exact (Ideal.algEquivResidueFieldOfField x.asIdeal).commutes a
      | simpa using (Ideal.algEquivResidueFieldOfField x.asIdeal).commutes a
  rw [this]
  first
    | (rw [Spec.algebraMap_residueFieldIso_inv (.of k) x, Iso.hom_inv_id_assoc]; rfl)
    | (simp only [Spec.algebraMap_residueFieldIso_inv, Iso.hom_inv_id_assoc]; rfl)
    | simp [Spec.algebraMap_residueFieldIso_inv, germ_residue]
