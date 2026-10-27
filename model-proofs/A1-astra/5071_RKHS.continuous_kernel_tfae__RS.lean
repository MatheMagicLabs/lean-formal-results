/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
    apply continuous_iff_continuousAt.2
    intro x
    apply tendsto_iff_norm_sub_tendsto_zero.2
    have hc : Continuous (fun y : X =>
        Real.sqrt ‖kernel H y y - kernel H x y -
          kernel H y x + kernel H x x‖) :=
      Real.continuous_sqrt.comp
        ((((h.comp (continuous_id.prodMk continuous_id)).sub
          (h.comp (continuous_const.prodMk continuous_id))).sub
          (h.comp (continuous_id.prodMk continuous_const))).add
          continuous_const).norm
    simpa only [norm_kerFun_sub_kerFun, sub_self, zero_sub,
      neg_add_cancel, norm_zero, Real.sqrt_zero] using hc.tendsto x
  tfae_have 2 → 3 := by
    intro h
    simpa only [Function.comp_def, kerFun_eq_adjoint_eval,
      ContinuousLinearMap.adjoint_adjoint] using
      (ContinuousLinearMap.adjoint.continuous.comp h)
  tfae_have 3 → 1 := by
    intro h
    have hk : Continuous (kerFun H) := by
      change Continuous (fun x : X => kerFun H x)
      simpa only [Function.comp_def, kerFun_eq_adjoint_eval] using
        (ContinuousLinearMap.adjoint.continuous.comp h)
    simpa only [Function.comp_def, kernel_apply] using
      (ContinuousLinearMap.adjoint.continuous.comp
        (hk.comp continuous_fst)).clm_comp (hk.comp continuous_snd)
  tfae_finish
