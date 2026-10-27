/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Hom.residueDegree_eq_finrank
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 377
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 3 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma Hom.residueDegree_eq_finrank {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI := Algebra.compHom (X.residueField x)
      ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
    f.residueDegree x = Module.finrank k (X.residueField x) := by
  letI : Algebra k (X.residueField x) :=
    Algebra.compHom (X.residueField x)
      ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
  letI : Algebra ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  dsimp only [Hom.residueDegree]
  symm
  refine Algebra.finrank_eq_of_equiv_equiv
    (Spec.residueFieldIsoOfField (f x)).symm.commRingCatIsoToRingEquiv
    (RingEquiv.refl _) ?_
  refine RingHom.ext fun a => ?_
  exact congrArg (fun g => g.hom a)
    (Hom.residueFieldIsoOfField_inv_residueFieldMap f x)
