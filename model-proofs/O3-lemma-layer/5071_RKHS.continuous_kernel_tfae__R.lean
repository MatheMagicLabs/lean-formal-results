/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
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
  have hadj : ∀ x, ContinuousLinearMap.adjoint (kerFun H x) = eval H x := by
    intro x
    first
      | simp [kerFun]
      | simp [eval]
      | rfl
      | simp
  have hk : ∀ x, kerFun H x = ContinuousLinearMap.adjoint (eval H x) := by
    intro x
    rw [← hadj, adjoint_adjoint]
  have hK : ∀ x y, kernel H x y = eval H x ∘L kerFun H y := by
    intro x y
    first
      | rfl
      | simp [kernel, hadj]
      | simp [kernel]
      | (ext; simp [kernel, kerFun, eval])
  tfae_have 2 → 3 := by
    intro h
    have := (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := V) (F := H)).continuous.comp h
    simpa [Function.comp_def, hadj] using this
  tfae_have 3 → 2 := by
    intro h
    have := (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := H) (F := V)).continuous.comp h
    have e : (fun x => kerFun H x) = fun x => ContinuousLinearMap.adjoint (eval H x) :=
      funext hk
    show Continuous (fun x => kerFun H x)
    rw [e]
    exact this
  tfae_have 2 → 1 := by
    intro h
    have h3 : Continuous (fun x : X => eval H x) := by
      have := (ContinuousLinearMap.adjoint (𝕜 := 𝕜) (E := V) (F := H)).continuous.comp h
      simpa [Function.comp_def, hadj] using this
    simp_rw [hK]
    exact (h3.comp continuous_fst).clm_comp (h.comp continuous_snd)
  tfae_have 1 → 2 := by
    intro h
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have key : ∀ y, ‖kerFun H y - kerFun H x‖ * ‖kerFun H y - kerFun H x‖
        = ‖kernel H y y - kernel H y x - kernel H x y + kernel H x x‖ := by
      intro y
      rw [← norm_adjoint_comp_self]
      congr 1
      rw [map_sub, sub_comp, comp_sub, comp_sub]
      simp only [hK, hadj]
      abel
    have c : Continuous (fun y => kernel H y y - kernel H y x - kernel H x y + kernel H x x) :=
      (((h.comp (continuous_id.prodMk continuous_id)).sub
        (h.comp (continuous_id.prodMk continuous_const))).sub
        (h.comp (continuous_const.prodMk continuous_id))).add continuous_const
    have t := (c.tendsto x).norm
    simp only [sub_self, zero_sub, neg_add_cancel, norm_zero] at t
    have h2 : Tendsto (fun y => ‖kerFun H y - kerFun H x‖ * ‖kerFun H y - kerFun H x‖)
        (𝓝 x) (𝓝 0) := by
      simp_rw [key]
      exact t
    have h3 := h2.sqrt
    simpa [Real.sqrt_mul_self (norm_nonneg _)] using h3
  tfae_finish
