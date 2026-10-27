/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Spec.residueFieldIsoOfField_eq
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 354
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
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

lemma Spec.residueFieldIsoOfField_eq {k : Type u} [Field k] (x : Spec (.of k)) :
    haveI := x.isPrime
    Spec.residueFieldIsoOfField x = Spec.residueFieldIso (.of k) x ≪≫
      (Ideal.algEquivResidueFieldOfField x.asIdeal).symm.toRingEquiv.toCommRingCatIso := by
  apply Iso.ext_inv
  simp [Spec.residueFieldIsoOfField_inv, Spec.Γevaluation_eq_of_field]
  ext a
  rfl
