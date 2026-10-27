/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Module.Basis.toMatrix_unitsSMul
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Basis.lean, line 87 (group DRIFT)
Experiment:  D1-deepseek-16-samples, arm sample 12, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 16 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
theorem toMatrix_unitsSMul [DecidableEq ι] (e : Basis ι R₂ M₂) (w : ι → R₂ˣ) :
    e.toMatrix (e.unitsSMul w) = diagonal ((↑) ∘ w) := by
  ext i j
  by_cases h : i = j <;> simp_all [Basis.toMatrix_apply, Basis.unitsSMul_apply,
    Units.smul_def, Matrix.diagonal_apply, Function.update_apply]
  <;> aesop
