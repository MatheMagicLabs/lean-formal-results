/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem continuous_kernel_tfae : List.TFAE [
    Continuous (fun p : X × X => kernel H p.1 p.2),
    Continuous (kerFun H),
    Continuous (fun x : X => eval H x)] := by
  tfae_have 2 → 3 := fun h => by
    have : (fun x : X => eval H x) = fun x => ContinuousLinearMap.adjoint (kerFun H x) := by
      funext x; simp [kerFun]
    rw [this]
    exact ContinuousLinearMap.adjoint.continuous.comp h
  tfae_have 3 → 2 := fun h => by
    show Continuous (fun x => ContinuousLinearMap.adjoint (eval H x))
    exact ContinuousLinearMap.adjoint.continuous.comp h
  tfae_have 2 → 1 := fun h => by
    simp only [kernel_apply]
    exact (ContinuousLinearMap.adjoint.continuous.comp (h.comp continuous_fst)).clm_comp
      (h.comp continuous_snd)
  tfae_have 1 → 2 := fun h => by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    simp only [norm_kerFun_sub_kerFun]
    have hc : Continuous (fun y : X =>
        √‖kernel H y y - kernel H x y - kernel H y x + kernel H x x‖) := by
      have h1 : Continuous (fun y : X => kernel H y y) :=
        h.comp (continuous_id.prodMk continuous_id)
      have h2 : Continuous (fun y : X => kernel H x y) :=
        h.comp (continuous_const.prodMk continuous_id)
      have h3 : Continuous (fun y : X => kernel H y x) :=
        h.comp (continuous_id.prodMk continuous_const)
      exact (((h1.sub h2).sub h3).add continuous_const).norm.sqrt
    have := hc.tendsto x
    simpa using this
  tfae_finish
