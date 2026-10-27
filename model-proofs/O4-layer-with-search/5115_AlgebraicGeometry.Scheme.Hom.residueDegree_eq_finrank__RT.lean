/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Hom.residueDegree_eq_finrank
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 377
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

universe u
open CategoryTheory TopologicalSpace Opposite IsLocalRing
noncomputable section
namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {U : X.Opens}
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
section congr
end congr
section fromResidueField
end fromResidueField
section Spec
variable (R : CommRingCat) (x : Spec R)
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [reassoc] Spec.residueFieldIsoOfField_inv
end Spec

lemma Hom.residueDegree_eq_finrank {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI := Algebra.compHom (X.residueField x)
      ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
    f.residueDegree x = Module.finrank k (X.residueField x) := by
  letI : Algebra k (X.residueField x) := Algebra.compHom (X.residueField x)
      ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
  letI := (f.residueFieldMap x).hom.toAlgebra
  refine (Algebra.finrank_eq_of_equiv_equiv
    (Spec.residueFieldIsoOfField (f x)).symm.commRingCatIsoToRingEquiv
    (RingEquiv.refl _) ?_).symm
  ext a
  first
    | exact congr($(Hom.residueFieldIsoOfField_inv_residueFieldMap f x).hom a)
    | (have h := congr($(Hom.residueFieldIsoOfField_inv_residueFieldMap f x).hom a)
       simpa [RingHom.algebraMap_toAlgebra, Algebra.compHom] using h)
