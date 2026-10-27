/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  have hk : ∀ x y : X, kernel H x y = (kerFun H x).adjoint ∘L kerFun H y := by
    intro x y
    rw [kernel_apply]
  have he : (fun x : X => eval H x) = fun x => (kerFun H x).adjoint := by
    funext x
    rw [kerFun_eq_adjoint_eval, adjoint_adjoint]
  tfae_have 2 → 3 := by
    intro h
    rw [he]
    exact (LinearIsometryEquiv.continuous _).comp h
  tfae_have 3 → 2 := by
    intro h
    have : (kerFun H : X → V →L[𝕜] H) = fun x => (eval H x).adjoint := by
      funext x
      rw [kerFun_eq_adjoint_eval]
    rw [this]
    exact (LinearIsometryEquiv.continuous _).comp h
  tfae_have 2 → 1 := by
    intro h
    simp_rw [hk]
    exact (((LinearIsometryEquiv.continuous _).comp h).comp continuous_fst).clm_comp
      (h.comp continuous_snd)
  tfae_have 1 → 2 := by
    intro h
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have key : ∀ y, ‖kerFun H y - kerFun H x‖ = Real.sqrt
        ‖kernel H y y - kernel H y x - kernel H x y + kernel H x x‖ := by
      intro y
      have : (kerFun H y - kerFun H x).adjoint ∘L (kerFun H y - kerFun H x)
          = kernel H y y - kernel H y x - kernel H x y + kernel H x x := by
        simp only [hk, map_sub, sub_comp, comp_sub]
        abel
      rw [← this, norm_adjoint_comp_self, Real.sqrt_mul_self (norm_nonneg _)]
    simp_rw [key]
    have h1 : Continuous (fun y : X => kernel H y y) :=
      h.comp (continuous_id.prodMk continuous_id)
    have h2 : Continuous (fun y : X => kernel H y x) :=
      h.comp (continuous_id.prodMk continuous_const)
    have h3 : Continuous (fun y : X => kernel H x y) :=
      h.comp (continuous_const.prodMk continuous_id)
    have hc : Continuous (fun y => Real.sqrt
        ‖kernel H y y - kernel H y x - kernel H x y + kernel H x x‖) :=
      (((h1.sub h2).sub h3).add continuous_const).norm.sqrt
    have := hc.tendsto x
    simpa using this
  tfae_finish
