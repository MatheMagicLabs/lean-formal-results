/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
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
  tfae_have 1 → 2 := by
    intro h
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    simp_rw [norm_kerFun_sub_kerFun]
    have hc : Continuous fun y : X =>
        √‖kernel H y y - kernel H x y - kernel H y x + kernel H x x‖ := by
      have h1 : Continuous fun y : X => kernel H y y :=
        h.comp (continuous_id.prodMk continuous_id)
      have h2 : Continuous fun y : X => kernel H x y :=
        h.comp (continuous_const.prodMk continuous_id)
      have h3 : Continuous fun y : X => kernel H y x :=
        h.comp (continuous_id.prodMk continuous_const)
      exact (((h1.sub h2).sub h3).add continuous_const).norm.sqrt
    have := hc.tendsto x
    simpa using this
  tfae_have 2 → 1 := by
    intro h
    have e : (fun p : X × X => kernel H p.1 p.2)
        = fun p : X × X => ContinuousLinearMap.adjoint (kerFun H p.1 : V →L[𝕜] H)
            ∘L (kerFun H p.2 : V →L[𝕜] H) := by
      funext p; exact kernel_apply (H := H) p.1 p.2
    rw [e]
    exact ((ContinuousLinearMap.adjoint :
      (V →L[𝕜] H) ≃ₗᵢ⋆[𝕜] (H →L[𝕜] V)).continuous.comp
        (h.comp continuous_fst)).clm_comp (h.comp continuous_snd)
  tfae_have 2 → 3 := by
    intro h
    have e : (fun x : X => eval H x)
        = fun x : X => ContinuousLinearMap.adjoint (kerFun H x : V →L[𝕜] H) := by
      funext x
      rw [kerFun_eq_adjoint_eval (H := H) x, ContinuousLinearMap.adjoint_adjoint]
    rw [e]
    exact (ContinuousLinearMap.adjoint :
      (V →L[𝕜] H) ≃ₗᵢ⋆[𝕜] (H →L[𝕜] V)).continuous.comp h
  tfae_have 3 → 2 := by
    intro h
    have e : (fun x : X => (kerFun H x : V →L[𝕜] H))
        = fun x : X => ContinuousLinearMap.adjoint (eval H x : H →L[𝕜] V) := by
      funext x
      rw [kerFun_eq_adjoint_eval (H := H) x]
    show Continuous (fun x : X => (kerFun H x : V →L[𝕜] H))
    rw [e]
    exact (ContinuousLinearMap.adjoint :
      (H →L[𝕜] V) ≃ₗᵢ⋆[𝕜] (V →L[𝕜] H)).continuous.comp h
  tfae_finish
