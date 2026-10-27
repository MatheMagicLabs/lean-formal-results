/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CategoryTheory.ProjectiveResolution.smul_extMk
Source:      Mathlib @ a02a63c2, Mathlib/CategoryTheory/Abelian/Projective/Ext.lean, line 188
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

universe w v u
open CategoryTheory CochainComplex HomComplex Abelian Localization
namespace CategoryTheory.ProjectiveResolution
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
variable (X n) in

lemma smul_extMk {R₀ : Type*} [Ring R₀] [Linear R₀ C]
    (r : R₀) {n : ℕ} (f : R.complex.X n ⟶ Y) (m : ℕ) (hm : n + 1 = m)
    (hf : R.complex.d m n ≫ f = 0) :
    r • R.extMk f m hm hf =
      R.extMk (r • f) m hm (by simp [hf]) := by
  rw [← R.extEquivCohomologyClass.symm_apply_apply (R.extMk f m hm hf),
    ← R.extEquivCohomologyClass.symm_apply_apply (R.extMk (r • f) m hm (by simp [hf])),
    ← extEquivCohomologyClass_symm_smul, extEquivCohomologyClass_extMk,
    extEquivCohomologyClass_extMk]
  congr 1
  simp only [Linear.comp_smul]
  first
    | (rw [Cocycle.toSingleMk_smul]
       first
         | rfl
         | exact (CohomologyClass.mk_smul _ _).symm
         | simp [CohomologyClass.mk_smul]
         | simp)
    | (erw [Cocycle.toSingleMk_smul]
       first
         | rfl
         | simp)
