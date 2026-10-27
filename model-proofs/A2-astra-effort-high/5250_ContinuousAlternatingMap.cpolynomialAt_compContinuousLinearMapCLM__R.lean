/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousAlternatingMap.cpolynomialAt_compContinuousLinearMapCLM
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Analytic/CPolynomial.lean, line 241
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  have h :
      (compContinuousLinearMapCLM :
        (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) =
      ((Fintype.card ι)! : 𝕜)⁻¹ •
        ((Fintype.card ι)! • compContinuousLinearMapCLM) := by
    rw [← Nat.cast_smul_eq_nsmul 𝕜, smul_smul, inv_mul_cancel₀, one_smul]
    simp [Nat.factorial_ne_zero]
  rw [h]
  apply CPolynomialAt.smul
  exact cpolynomialAt_smul_compContinuousLinearMapCLM f₀
