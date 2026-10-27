/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     AddCircle.windingNumber_zsmulLoop
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Covering/FundamentalGroupCircle.lean, line 75
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open unitInterval
namespace AddCircle
variable (p : ℝ)
variable {p} [hp : Fact (0 < p)]

theorem windingNumber_zsmulLoop (x : ℝ) (n : ℤ) :
    windingNumber (x := x) (.of (.mk (zsmulLoop p x n))) = n := by
  let f : C(I, ℝ) :=
    ⟨fun t => n • ((t : ℝ) * p) + x, by fun_prop⟩
  have hf : (↑) ∘ f = zsmulLoop p x n := by
    funext t
    change ((n • ((t : ℝ) * p) + x : ℝ) : AddCircle p) =
      zsmulLoop p x n t
    rw [zsmulLoop_apply, coe_add, coe_zsmul]
  have h := windingNumber_eq_div (zsmulLoop p x n) f hf
  have hp0 : p ≠ 0 := ne_of_gt hp.out
  have h' :
      (windingNumber (x := x) (.of (.mk (zsmulLoop p x n))) : ℝ) =
        (n : ℝ) := by
    simpa [f, zsmul_eq_mul, hp0] using h
  exact_mod_cast h'
