/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     BoundedVariationOn.intervalIntegrable
Source:      Mathlib @ a02a63c2, Mathlib/Analysis/BoundedVariation.lean, line 185
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem intervalIntegrable {f : ℝ → E} {a b : ℝ} {μ : Measure ℝ} [IsLocallyFiniteMeasure μ]
    {s : Set ℝ} (hf : BoundedVariationOn f s) (hs : uIcc a b ⊆ s) : IntervalIntegrable f μ a b := by
  have hφm : Monotone (fun x : ℝ => max (min a b) (min x (max a b))) :=
    fun x y h => max_le_max le_rfl (min_le_min h le_rfl)
  have hφs : MapsTo (fun x : ℝ => max (min a b) (min x (max a b))) univ (uIcc a b) :=
    fun x _ => ⟨le_max_left _ _, max_le min_le_max (min_le_right _ _)⟩
  have hg : BoundedVariationOn (f ∘ fun x : ℝ => max (min a b) (min x (max a b))) univ := by
    have := eVariationOn.comp_le_of_monotoneOn f _ (hφm.monotoneOn univ) hφs
    exact ne_top_of_le_ne_top (hf.mono hs) this
  rw [intervalIntegrable_iff]
  refine IntegrableOn.mono_set ?_ uIoc_subset_uIcc
  haveI : IsFiniteMeasure (μ.restrict (uIcc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_uIcc.measure_lt_top⟩
  have := hg.integrable (μ := μ.restrict (uIcc a b))
  refine (integrableOn_congr_fun ?_ measurableSet_uIcc).1 this
  intro x hx
  show f (max (min a b) (min x (max a b))) = f x
  have h1 : min x (max a b) = x := min_eq_left hx.2
  rw [h1]
  have h2 : max (min a b) x = x := max_eq_right hx.1
  rw [h2]
