/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Hom.residueDegree_eq_finrank
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 377
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Hom.residueDegree_eq_finrank {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI := Algebra.compHom (X.residueField x)
      ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
    f.residueDegree x = Module.finrank k (X.residueField x) := by
  letI : Algebra k (X.residueField x) := Algebra.compHom (X.residueField x)
      ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
  letI := (f.residueFieldMap x).hom.toAlgebra
  change Module.finrank ((Spec (.of k)).residueField (f x)) (X.residueField x) = _
  have h := Hom.residueFieldIsoOfField_inv_residueFieldMap f x
  have h2 : f.residueFieldMap x = (Spec.residueFieldIsoOfField (f x)).hom ≫
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x) := by
    rw [← h, Iso.hom_inv_id_assoc]
  refine Algebra.finrank_eq_of_equiv_equiv
    (Spec.residueFieldIsoOfField (f x)).commRingCatIsoToRingEquiv (RingEquiv.refl _) ?_
  ext a
  change (X.Γevaluation x).hom (f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom
    ((Spec.residueFieldIsoOfField (f x)).hom.hom a))) = (f.residueFieldMap x).hom a
  rw [h2]
  rfl
