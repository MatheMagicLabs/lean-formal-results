/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open ContinuousLinearMap InnerProductSpace Submodule Filter
open scoped ComplexConjugate Topology
namespace RKHS
variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*}
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
variable [RKHS 𝕜 H X V]
set_option synthInstance.checkSynthOrder false in
variable (H) in
variable (H) [CompleteSpace H] [CompleteSpace V]
variable {H} in
variable {H} in
variable {H} in
section continuous
variable [TopologicalSpace X]

theorem continuous_kernel_tfae : List.TFAE [
    Continuous (fun p : X × X => kernel H p.1 p.2),
    Continuous (kerFun H),
    Continuous (fun x : X => eval H x)] := by
  have hk (x y : X) :
      (kerFun H x).adjoint.comp (kerFun H y) = kernel H x y := by
    simp [kernel, kerFun]
  have he (x : X) : (kerFun H x).adjoint = eval H x := by
    simp [kerFun]
  have hke (x : X) : (eval H x).adjoint = kerFun H x := by
    rw [← he x, adjoint_adjoint]
  tfae_have 1 → 2 := by
    intro h
    rw [continuous_iff_continuousAt]
    intro a
    let B : X → V →L[𝕜] V :=
      fun x => kernel H x x - kernel H x a -
        kernel H a x + kernel H a a
    have hB : Continuous B :=
      (((h.comp (continuous_id.prodMk continuous_id)).sub
        (h.comp (continuous_id.prodMk continuous_const))).sub
        (h.comp (continuous_const.prodMk continuous_id))).add
        continuous_const
    have hBa : B a = 0 := by
      simp [B]
    have hnorm (x : X) :
        ‖B x‖ = ‖kerFun H x - kerFun H a‖ ^ 2 := by
      have hB_eq :
          B x = (kerFun H x - kerFun H a).adjoint.comp
            (kerFun H x - kerFun H a) := by
        simp only [map_sub, sub_comp, comp_sub, hk]
        dsimp [B]
        abel
      rw [hB_eq]
      simpa [pow_two] using
        norm_adjoint_comp_self (kerFun H x - kerFun H a)
    have ht' :
        Tendsto (fun x => Real.sqrt ‖B x‖) (𝓝 a)
          (𝓝 (Real.sqrt ‖B a‖)) :=
      (Real.continuous_sqrt.comp hB.norm).continuousAt.tendsto
    have ht : Tendsto (fun x => Real.sqrt ‖B x‖) (𝓝 a) (𝓝 0) := by
      simpa only [hBa, norm_zero, Real.sqrt_zero] using ht'
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    simpa only [hnorm, Real.sqrt_sq (norm_nonneg _)] using ht
  tfae_have 2 → 1 := by
    intro h
    have ha : Continuous (fun x => (kerFun H x).adjoint) :=
      ContinuousLinearMap.adjoint.continuous.comp h
    simpa only [Function.comp_apply, hk] using
      (ha.comp continuous_fst).clm_comp (h.comp continuous_snd)
  tfae_have 2 → 3 := by
    intro h
    have ha : Continuous (fun x : X => (kerFun H x).adjoint) :=
      ContinuousLinearMap.adjoint.continuous.comp h
    simpa only [he] using ha
  tfae_have 3 → 2 := by
    intro h
    have ha : Continuous (fun x : X => (eval H x).adjoint) :=
      ContinuousLinearMap.adjoint.continuous.comp h
    simpa only [hke] using ha
  tfae_finish
