/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 1 (round 0 = first attempt)
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
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    simp_rw [norm_kerFun_sub_kerFun]
    have hc : Continuous (fun y : X =>
        √‖kernel H y y - kernel H x y - kernel H y x + kernel H x x‖) :=
      (((h.comp (continuous_id.prodMk continuous_id)).sub
        (h.comp (continuous_const.prodMk continuous_id))).sub
        (h.comp (continuous_id.prodMk continuous_const))).add
        continuous_const |>.norm.sqrt
    simpa using hc.continuousAt.tendsto (x := x)
  tfae_have 2 → 3 := by
    intro h
    have ha : Continuous (fun x : X => (kerFun H x).adjoint) :=
      ContinuousLinearMap.adjoint.continuous.comp h
    simpa only [kerFun_eq_adjoint_eval, adjoint_adjoint] using ha
  tfae_have 3 → 1 := by
    intro h
    have hk : Continuous (kerFun H) :=
      ContinuousLinearMap.adjoint.continuous.comp h
    simp_rw [kernel_apply]
    exact (ContinuousLinearMap.adjoint.continuous.comp
      (hk.comp continuous_fst)).clm_comp (hk.comp continuous_snd)
  tfae_finish
