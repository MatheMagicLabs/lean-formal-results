/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Spec.Γevaluation_eq_of_field
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 328
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
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
  have h := Spec.algebraMap_residueFieldIso_inv (.of k) x
  have h2 : (Ideal.algEquivResidueFieldOfField x.asIdeal).toRingEquiv.toCommRingCatIso.hom
      = CommRingCat.ofHom (algebraMap k x.asIdeal.ResidueField) := by
    ext a
    exact ((Ideal.algEquivResidueFieldOfField x.asIdeal).commutes a)
  rw [h2, h, Iso.hom_inv_id_assoc]
  rfl
