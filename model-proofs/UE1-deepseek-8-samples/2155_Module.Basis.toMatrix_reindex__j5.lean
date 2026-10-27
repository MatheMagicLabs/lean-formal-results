/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Module.Basis.toMatrix_reindex
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Basis.lean, line 263 (group STABLE)
Experiment:  UE1-deepseek-8-samples, arm sample 5, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem toMatrix_reindex (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
    (b.reindex e).toMatrix v = (b.toMatrix v).submatrix e.symm _root_.id := by
  ext i j
  simp [Basis.toMatrix_apply, Basis.reindex_apply, Function.comp_apply, Fin.val_zero]
  <;> aesop
