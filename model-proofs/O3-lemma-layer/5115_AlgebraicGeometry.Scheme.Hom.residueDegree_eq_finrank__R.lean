/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AlgebraicGeometry.Scheme.Hom.residueDegree_eq_finrank
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicGeometry/ResidueField.lean, line 377
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
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
end Spec

lemma Hom.residueDegree_eq_finrank {X : Scheme.{u}} {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) (x : X) :
    letI := Algebra.compHom (X.residueField x)
      ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
    f.residueDegree x = Module.finrank k (X.residueField x) := by
  letI : Algebra k (X.residueField x) := Algebra.compHom (X.residueField x)
      ((X.Γevaluation x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
  letI : Algebra ((Spec (.of k)).residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  unfold Hom.residueDegree
  dsimp only
  refine Algebra.finrank_eq_of_equiv_equiv
    (Spec.residueFieldIsoOfField (f.base x)).commRingCatIsoToRingEquiv
    (RingEquiv.refl _) ?_
  have key : (Spec.residueFieldIsoOfField (f.base x)).inv ≫ f.residueFieldMap x =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ≫ X.Γevaluation x := by
    first
      | (rw [Spec.residueFieldIsoOfField_inv_assoc]
         first
           | rw [Scheme.Γevaluation_naturality]; simp only [Category.assoc]
           | rw [Scheme.Hom.Γevaluation_naturality]; simp only [Category.assoc]
           | rw [← Scheme.Γevaluation_naturality]; simp only [Category.assoc]
           | rw [← Scheme.Hom.Γevaluation_naturality]; simp only [Category.assoc]
           | simp [Scheme.Γevaluation_naturality]
           | simp [Scheme.Hom.Γevaluation_naturality])
      | simp [Spec.residueFieldIsoOfField_inv, Scheme.Γevaluation_naturality]
      | simp [Spec.residueFieldIsoOfField_inv, Scheme.Hom.Γevaluation_naturality]
  ext a
  obtain ⟨b, rfl⟩ :=
    (Spec.residueFieldIsoOfField (f.base x)).commRingCatIsoToRingEquiv.symm.surjective a
  have := congrArg (fun g => g.hom b) key
  simp only [CommRingCat.comp_apply] at this
  first
    | exact this.symm
    | (simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        RingEquiv.apply_symm_apply, RingEquiv.refl_apply]
       first
         | exact this.symm
         | (rw [RingHom.algebraMap_toAlgebra]; exact this.symm)
         | (simp only [RingHom.algebraMap_toAlgebra] at *; exact this.symm)
         | (exact this.symm.trans rfl)
         | (simpa [Algebra.compHom, RingHom.algebraMap_toAlgebra] using this.symm)
         | (simpa [Algebra.compHom, RingHom.algebraMap_toAlgebra] using this))
