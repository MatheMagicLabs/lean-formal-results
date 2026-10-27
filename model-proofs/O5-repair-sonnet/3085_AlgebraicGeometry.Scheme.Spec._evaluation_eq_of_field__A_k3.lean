/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Spec.Γevaluation_eq_of_field
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 328
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
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
  have e : CommRingCat.ofHom (algebraMap (CommRingCat.of k) x.asIdeal.ResidueField) =
      (Ideal.algEquivResidueFieldOfField x.asIdeal).toRingEquiv.toCommRingCatIso.hom := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    first
      | rfl
      | exact ((Ideal.algEquivResidueFieldOfField x.asIdeal).commutes a).symm
  rw [e] at h
  change (Spec (.of k)).presheaf.germ ⊤ x trivial ≫ (Spec (.of k)).residue x = _
  have h2 : (Spec (.of k)).presheaf.germ ⊤ x trivial ≫ (Spec (.of k)).residue x =
      (Scheme.ΓSpecIso (.of k)).hom ≫ ((Scheme.ΓSpecIso (.of k)).inv ≫
        (Spec (.of k)).presheaf.germ ⊤ x trivial ≫ (Spec (.of k)).residue x) := by
    simp
  rw [h2, ← h]
