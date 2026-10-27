/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Hom.residueDegree_eq_finrank
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 377
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  letI := Algebra.compHom (X.residueField x)
    ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
  letI := (f.residueFieldMap x).hom.toAlgebra
  change Module.finrank ((Spec (.of k)).residueField (f x)) (X.residueField x) =
    Module.finrank k (X.residueField x)
  symm
  refine Algebra.finrank_eq_of_equiv_equiv
    (Spec.residueFieldIsoOfField (f x)).symm.commRingCatIsoToRingEquiv
    (RingEquiv.refl _) ?_
  change (f.residueFieldMap x).hom.comp
      (Spec.residueFieldIsoOfField (f x)).inv.hom =
    (X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  exact congrArg (fun g => g.hom) (f.residueFieldIsoOfField_inv_residueFieldMap x)
