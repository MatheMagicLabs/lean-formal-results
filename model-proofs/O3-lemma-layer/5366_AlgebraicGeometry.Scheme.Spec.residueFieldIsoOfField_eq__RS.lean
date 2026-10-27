/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Spec.residueFieldIsoOfField_eq
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 354
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  apply Iso.ext
  rw [← cancel_epi (Spec.residueFieldIsoOfField x).inv, Iso.inv_hom_id]
  ext a
  simp [Spec.residueFieldIsoOfField_inv, Spec.Γevaluation_eq_of_field]
