/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
    have hsq (y : X) :
        ‖kerFun H y - kerFun H x‖ ^ 2 =
          ‖kernel H y y - kernel H y x - kernel H x y + kernel H x x‖ := by
      calc
        _ = ‖(kerFun H y - kerFun H x).adjoint.comp
            (kerFun H y - kerFun H x)‖ := by
          simpa [pow_two] using
            (ContinuousLinearMap.norm_adjoint_comp_self
              (kerFun H y - kerFun H x)).symm
        _ = _ := by
          congr 1
          simp [kernel, kerFun, map_sub, sub_comp, comp_sub] <;> abel
    have hc : Continuous (fun y : X =>
        ‖kernel H y y - kernel H y x - kernel H x y + kernel H x x‖) :=
      ((((h.comp (continuous_id.prodMk continuous_id)).sub
        (h.comp (continuous_id.prodMk continuous_const))).sub
        (h.comp (continuous_const.prodMk continuous_id))).add
        continuous_const).norm
    have ht : Tendsto (fun y : X =>
        ‖kernel H y y - kernel H y x - kernel H x y + kernel H x x‖)
        (𝓝 x) (𝓝 0) := by
      simpa [ContinuousAt] using (hc.continuousAt (x := x))
    have ht' : Tendsto (fun y : X => ‖kerFun H y - kerFun H x‖ ^ 2)
        (𝓝 x) (𝓝 0) := by
      simpa only [hsq] using ht
    simpa using ht'.sqrt
  tfae_have 2 → 3 := by
    intro h
    change Continuous (fun x : X => (eval H x).adjoint) at h
    have ha : Continuous (fun A : V →L[𝕜] H => A.adjoint) :=
      ContinuousLinearMap.adjoint.continuous
    simpa only [Function.comp_def, ContinuousLinearMap.adjoint_adjoint]
      using ha.comp h
  tfae_have 3 → 1 := by
    intro h
    have ha : Continuous (fun A : H →L[𝕜] V => A.adjoint) :=
      ContinuousLinearMap.adjoint.continuous
    have hk : Continuous (kerFun H) := by
      change Continuous (fun x : X => (eval H x).adjoint)
      exact ha.comp h
    have hb : Continuous (fun A : V →L[𝕜] H => A.adjoint) :=
      ContinuousLinearMap.adjoint.continuous
    change Continuous (fun p : X × X =>
      (kerFun H p.1).adjoint.comp (kerFun H p.2))
    exact ((hb.comp hk).comp continuous_fst).clm_comp
      (hk.comp continuous_snd)
  tfae_finish
