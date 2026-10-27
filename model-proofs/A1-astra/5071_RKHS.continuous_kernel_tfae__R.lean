/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
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
  tfae_have 1 → 3 := by
    intro h
    apply continuous_iff_continuousAt.mpr
    intro a
    have hG' : Continuous (fun x : X =>
        kernel H x x - kernel H x a - kernel H a x + kernel H a a) :=
      (((h.comp (continuous_id.prodMk continuous_id)).sub
        (h.comp (continuous_id.prodMk continuous_const))).sub
        (h.comp (continuous_const.prodMk continuous_id))).add continuous_const
    have hG : Continuous (fun x =>
        (eval H x - eval H a) ∘L (eval H x - eval H a).adjoint) := by
      convert hG' using 1
      funext x
      change
        (eval H x - eval H a) ∘L (eval H x - eval H a).adjoint =
          (eval H x).adjoint.adjoint ∘L (eval H x).adjoint -
          (eval H x).adjoint.adjoint ∘L (eval H a).adjoint -
          (eval H a).adjoint.adjoint ∘L (eval H x).adjoint +
          (eval H a).adjoint.adjoint ∘L (eval H a).adjoint
      simp only [ContinuousLinearMap.adjoint_adjoint,
        map_sub, comp_sub, sub_comp]
      <;> abel
    have hn (T : H →L[𝕜] V) :
        ‖T ∘L T.adjoint‖ = ‖T‖ ^ 2 := by
      first
      | simpa [pow_two] using
          ContinuousLinearMap.norm_adjoint_comp_self T.adjoint
      | simpa [pow_two] using
          ContinuousLinearMap.norm_self_comp_adjoint T
    have hc : Continuous (fun x => ‖eval H x - eval H a‖) := by
      convert Real.continuous_sqrt.comp hG.norm using 1
      funext x
      change ‖eval H x - eval H a‖ =
        Real.sqrt ‖(eval H x - eval H a) ∘L
          (eval H x - eval H a).adjoint‖
      rw [hn, Real.sqrt_sq (norm_nonneg _)]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [ContinuousAt, sub_self, norm_zero] using
      (hc.continuousAt (x := a))
  tfae_have 3 → 2 := by
    intro h
    change Continuous (fun x : X => (eval H x).adjoint)
    exact ContinuousLinearMap.adjoint.continuous.comp h
  tfae_have 2 → 1 := by
    intro h
    change Continuous (fun p : X × X =>
      (kerFun H p.1).adjoint ∘L kerFun H p.2)
    exact
      ((ContinuousLinearMap.adjoint.continuous.comp h).comp continuous_fst).clm_comp
        (h.comp continuous_snd)
  tfae_finish
