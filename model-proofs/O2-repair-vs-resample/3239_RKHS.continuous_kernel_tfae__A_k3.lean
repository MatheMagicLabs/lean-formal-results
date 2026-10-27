/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     RKHS.continuous_kernel_tfae
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/InnerProductSpace/Reproducing.lean, line 201
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
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
  tfae_have 1 → 2 := by
    intro h
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    simp only [norm_kerFun_sub_kerFun]
    have hk : ∀ f g : X → X, Continuous f → Continuous g →
        Continuous fun y => kernel H (f y) (g y) :=
      fun f g hf hg => h.comp (hf.prodMk hg)
    have hc : Continuous fun y =>
        √‖kernel H y y - kernel H x y - kernel H y x + kernel H x x‖ :=
      ((((hk id id continuous_id continuous_id).sub
        (hk (fun _ => x) id continuous_const continuous_id)).sub
        (hk id (fun _ => x) continuous_id continuous_const)).add
        (hk (fun _ => x) (fun _ => x) continuous_const continuous_const)).norm.sqrt
    convert hc.tendsto x using 2
    simp
  tfae_have 2 → 1 := by
    intro h
    have : (fun p : X × X => kernel H p.1 p.2)
        = fun p => (kerFun H p.1).adjoint ∘L kerFun H p.2 := by
      funext p
      exact kernel_apply H _ _
    rw [this]
    exact (ContinuousLinearMap.adjoint.continuous.comp (h.comp continuous_fst)).clm_comp
      (h.comp continuous_snd)
  tfae_have 2 → 3 := by
    intro h
    have : (fun x : X => eval H x) = fun x => (kerFun H x).adjoint := by
      funext x
      rw [kerFun_eq_adjoint_eval, ContinuousLinearMap.adjoint_adjoint]
    rw [this]
    exact ContinuousLinearMap.adjoint.continuous.comp h
  tfae_have 3 → 2 := by
    intro h
    have : kerFun H = fun x => (eval H x).adjoint := by
      funext x
      rfl
    rw [this]
    exact ContinuousLinearMap.adjoint.continuous.comp h
  tfae_finish
