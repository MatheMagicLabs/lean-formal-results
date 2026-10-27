/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/CompletelyRegular.lean, line 210
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
    [CompletelyRegularSpace X] (hX : .mk X < 𝔠) : ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.isOpen) ?_
  intro x U hxU hU
  obtain ⟨f, hf, hfx, hfU⟩ := CompletelyRegularSpace.completely_regular_isOpen x U hU hxU
  have hc : Continuous (fun y => (f y : ℝ)) := continuous_subtype_val.comp hf
  obtain ⟨r, hr, hrr⟩ : ∃ r ∈ Ioo (0:ℝ) 1, r ∉ range (fun y => (f y : ℝ)) := by
    by_contra h
    push_neg at h
    have hsub : Ioo (0:ℝ) 1 ⊆ range (fun y => (f y : ℝ)) := fun r hr => h r hr
    have h1 := Cardinal.lift_le.{u}.mpr (Cardinal.mk_le_mk_of_subset hsub)
    rw [Cardinal.mk_Ioo_real zero_lt_one, Cardinal.lift_continuum] at h1
    have h2 := Cardinal.mk_range_le_lift (f := fun y => (f y : ℝ))
    rw [Cardinal.lift_uzero] at h2
    exact absurd (h1.trans h2) (not_le.mpr hX)
  refine ⟨{y | (f y : ℝ) < r}, ?_, ?_, ?_⟩
  · have heq : {y | (f y : ℝ) < r} = {y | (f y : ℝ) ≤ r} := by
      ext y
      simp only [mem_setOf_eq]
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (fun e => hrr ⟨y, e⟩)⟩
    show IsClopen _
    refine ⟨?_, isOpen_lt hc continuous_const⟩
    rw [heq]
    exact isClosed_le hc continuous_const
  · show (f x : ℝ) < r
    simp [hfx, hr.1]
  · intro y hy
    by_contra hyU
    have h1 : f y = 1 := hfU hyU
    have h2 : (f y : ℝ) < r := hy
    rw [h1] at h2
    simp at h2
    linarith [hr.2]
