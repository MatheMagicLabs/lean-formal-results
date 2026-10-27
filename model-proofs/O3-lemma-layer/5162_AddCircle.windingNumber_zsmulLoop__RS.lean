/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AddCircle.windingNumber_zsmulLoop
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Covering/FundamentalGroupCircle.lean, line 75
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open unitInterval
namespace AddCircle
variable (p : ℝ)
variable {p} [hp : Fact (0 < p)]

theorem windingNumber_zsmulLoop (x : ℝ) (n : ℤ) :
    windingNumber (x := x) (.of (.mk (zsmulLoop p x n))) = n := by
  have hp' : p ≠ 0 := hp.out.ne'
  have h := windingNumber_eq_div (zsmulLoop p x n)
    ⟨fun t : I => n • ((t : ℝ) * p) + x, by fun_prop⟩
    (by funext t; simp [zsmulLoop_apply])
  rw [← Int.cast_inj (α := ℝ), h]
  simp [zsmul_eq_mul, hp']
