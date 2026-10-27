/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.InjectiveResolution.smul_extMk
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Abelian/Injective/Ext.lean, line 188
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

universe w v u
open CategoryTheory CochainComplex HomComplex Abelian Localization
namespace CategoryTheory.InjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (X n) in

lemma smul_extMk {R₀ : Type*} [Ring R₀] [Linear R₀ C]
    (r : R₀) {n : ℕ} (f : X ⟶ R.cocomplex.X n) (m : ℕ) (hm : n + 1 = m)
    (hf : f ≫ R.cocomplex.d n m = 0) :
    r • R.extMk f m hm hf =
      R.extMk (r • f) m hm (by simp [hf]) := by
  simp only [extMk, Linear.smul_comp]
  first
  | (rw [← R.extEquivCohomologyClass_symm_smul, ← CohomologyClass.mk_smul,
      ← Cocycle.fromSingleMk_smul])
  | (rw [R.extEquivCohomologyClass_symm_smul])
  | (simp [extEquivCohomologyClass_symm_smul, CohomologyClass.mk_smul,
      Cocycle.fromSingleMk_smul])
  | (rw [Cocycle.fromSingleMk_smul, CohomologyClass.mk_smul,
      R.extEquivCohomologyClass_symm_smul])
  | (apply R.extEquivCohomologyClass.injective
     simp [CohomologyClass.mk_smul, Cocycle.fromSingleMk_smul])
