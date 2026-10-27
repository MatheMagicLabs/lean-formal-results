/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousAlternatingMap.cpolynomialAt_compContinuousLinearMapCLM
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Analytic/CPolynomial.lean, line 241
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
open scoped Topology Nat
open Set Filter ENNReal
variable {f g : E → F} {p pf pg : FormalMultilinearSeries 𝕜 E F} {x : E} {r : ℝ≥0∞} {n m : ℕ}
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
namespace ContinuousMultilinearMap
variable {ι : Type*} {Em : ι → Type*} [∀ i, NormedAddCommGroup (Em i)] [∀ i, NormedSpace 𝕜 (Em i)]
end ContinuousMultilinearMap
namespace ContinuousAlternatingMap
variable {ι : Type*} [Fintype ι] (f : E [⋀^ι]→L[𝕜] F) {x : Π (_ : ι), E} {s : Set (Π (_ : ι), E)}
variable [CharZero 𝕜]

lemma cpolynomialAt_compContinuousLinearMapCLM (f₀ : E →L[𝕜] F) :
    CPolynomialAt 𝕜
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) f₀ := by
  obtain ⟨p, n, r, hp⟩ := cpolynomialAt_smul_compContinuousLinearMapCLM (G := G) (ι := ι) f₀
  have h3 : CPolynomialAt 𝕜 ((((Fintype.card ι)! : 𝕜)⁻¹) • ((Fintype.card ι)! •
      (compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)))) f₀ :=
    ⟨(((Fintype.card ι)! : 𝕜)⁻¹) • p, n, r, hp.toHasFPowerSeriesOnBall.const_smul,
      fun m hm => by simp [hp.finite m hm]⟩
  convert h3 using 1
  ext1 g
  have hne : ((Fintype.card ι)! : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [Pi.smul_apply, Pi.smul_apply, ← Nat.cast_smul_eq_nsmul 𝕜, smul_smul,
    inv_mul_cancel₀ hne, one_smul]
