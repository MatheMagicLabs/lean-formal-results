/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
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
  tfae_have 1 → 2 := fun h => by
    rw [continuous_iff_continuousAt]
    intro x
    have a : Continuous fun y : X => kernel H y y :=
      h.comp (continuous_id.prodMk continuous_id)
    have b : Continuous fun y : X => kernel H x y :=
      h.comp (continuous_const.prodMk continuous_id)
    have c : Continuous fun y : X => kernel H y x :=
      h.comp (continuous_id.prodMk continuous_const)
    have hc : Continuous fun y : X =>
        √‖kernel H y y - kernel H x y - kernel H y x + kernel H x x‖ :=
      ((((a.sub b).sub c).add continuous_const).norm).sqrt
    refine (tendsto_iff_norm_sub_tendsto_zero).2 ?_
    have e : (fun y => ‖kerFun H y - kerFun H x‖) = fun y =>
        √‖kernel H y y - kernel H x y - kernel H y x + kernel H x x‖ :=
      funext fun y => norm_kerFun_sub_kerFun H y x
    rw [e]
    convert hc.tendsto x using 2
    simp
  tfae_have 2 → 3 := fun h => by
    have : (fun x : X => eval H x) = fun x => (kerFun H x).adjoint := by
      funext x; simp [kerFun_eq_adjoint_eval]
    rw [this]
    exact (ContinuousLinearMap.adjoint : (V →L[𝕜] H) ≃ₗᵢ⋆[𝕜] (H →L[𝕜] V)).continuous.comp h
  tfae_have 3 → 2 := fun h => by
    have : kerFun H = fun x : X => (eval H x).adjoint := by
      funext x; rfl
    rw [this]
    exact (ContinuousLinearMap.adjoint : (H →L[𝕜] V) ≃ₗᵢ⋆[𝕜] (V →L[𝕜] H)).continuous.comp h
  tfae_have 2 → 1 := fun h => by
    have hadj : Continuous fun x : X => (kerFun H x).adjoint :=
      (ContinuousLinearMap.adjoint : (V →L[𝕜] H) ≃ₗᵢ⋆[𝕜] (H →L[𝕜] V)).continuous.comp h
    have := (hadj.comp continuous_fst).clm_comp (h.comp continuous_snd)
    exact this.congr fun p => (kernel_apply H p.1 p.2).symm
  tfae_finish
