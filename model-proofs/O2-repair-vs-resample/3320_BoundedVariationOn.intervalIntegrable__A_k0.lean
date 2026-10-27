/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     BoundedVariationOn.intervalIntegrable
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/BoundedVariation.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem intervalIntegrable {f : ℝ → E} {a b : ℝ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {s : Set ℝ} (hf : BoundedVariationOn f s) (hs : uIcc a b ⊆ s) : IntervalIntegrable f μ a b := by
  have hg : BoundedVariationOn (fun x => f (max (min a b) (min x (max a b)))) univ := by
    refine ne_top_of_le_ne_top (hf.mono hs) ?_
    exact eVariationOn.comp_le_of_monotoneOn f _
      (fun x _ y _ hxy => max_le_max le_rfl (min_le_min hxy le_rfl))
      (fun x _ => ⟨le_max_left _ _, max_le min_le_max (min_le_right _ _)⟩)
  rw [intervalIntegrable_iff]
  haveI : IsFiniteMeasure (μ.restrict (uIcc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_uIcc.measure_lt_top⟩
  have h1 : IntegrableOn (fun x => f (max (min a b) (min x (max a b)))) (uIcc a b) μ :=
    hg.integrable
  have h2 : IntegrableOn f (uIcc a b) μ := by
    refine h1.congr_fun ?_ measurableSet_uIcc
    intro x hx
    have hx1 : min a b ≤ x := hx.1
    have hx2 : x ≤ max a b := hx.2
    simp only
    rw [min_eq_left hx2, max_eq_right hx1]
  exact h2.mono_set Ioc_subset_Icc_self
