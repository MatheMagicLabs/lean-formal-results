/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousAlternatingMap.cpolynomialAt_compContinuousLinearMapCLM
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/Analytic/CPolynomial.lean, line 241
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA2-leanstral-agent-variants, arm staffel, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent on the 29 theorems O3LA left open: neu = fresh restart, fest = fixed instruction, staffel = staged budget
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
  have hc_ne_zero : ((Fintype.card ι)! : 𝕜) ≠ 0 := by
    exact mod_cast Nat.factorial_ne_zero _
  have h_smul_raw : CPolynomialAt 𝕜 ((Fintype.card ι)! •
      compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) f₀ :=
    cpolynomialAt_smul_compContinuousLinearMapCLM (ι := ι) f₀
  have h_smul : CPolynomialAt 𝕜 (((Fintype.card ι)! : 𝕜) •
      compContinuousLinearMapCLM : (E →L[𝕜] F) → (F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G)) f₀ := by
    simpa [Nat.cast_smul_eq_nsmul] using h_smul_raw
  have h_eq : compContinuousLinearMapCLM =
      (((Fintype.card ι)! : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜
        ((F [⋀^ι]→L[𝕜] G) →L[𝕜] (E [⋀^ι]→L[𝕜] G))) ∘
      (((Fintype.card ι)! : 𝕜) • compContinuousLinearMapCLM) := by
    ext f m : 2
    simp [hc_ne_zero]
  rw [h_eq]
  apply ContinuousLinearMap.comp_cpolynomialAt
  exact h_smul
