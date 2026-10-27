/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ExteriorAlgebra.baseChangeEquiv_leftInverse
Source:      Mathlib @ a02a63c2, Mathlib/LinearAlgebra/ExteriorAlgebra/BaseChange.lean, line 75
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

noncomputable section
variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
open TensorProduct
namespace ExteriorAlgebra

lemma baseChangeEquiv_leftInverse :
    (baseChangeExteriorAlgebraToTensor R M S).comp (baseChangeEquivForward R M S) =
      AlgHom.id S _ := by
  ext s
  simp only [baseChangeEquivForward, baseChangeExteriorAlgebraToTensor]
  try erw [Algebra.TensorProduct.lift_tmul]
  try simp only [map_one, one_mul]
  try simp only [baseChangeEquivForwardAux]
  try erw [ExteriorAlgebra.lift_ι_apply]
  try erw [CliffordAlgebra.lift_ι_apply]
  try erw [ExteriorAlgebra.lift_ι_apply]
  try erw [CliffordAlgebra.lift_ι_apply]
  try simp [baseChangeι, baseChangeEquivForwardAux, ExteriorAlgebra.lift_ι_apply,
    CliffordAlgebra.lift_ι_apply]
  try rfl
