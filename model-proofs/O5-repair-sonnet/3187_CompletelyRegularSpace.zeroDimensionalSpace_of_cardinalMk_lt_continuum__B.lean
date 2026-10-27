/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/CompletelyRegular.lean, line 210
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
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
  have hg : Continuous (fun y => (f y : ℝ)) := continuous_subtype_val.comp hf
  have hex : ∃ r ∈ Ioo (0:ℝ) 1, r ∉ range (fun y => (f y : ℝ)) := by
    by_contra h
    push_neg at h
    have h1 : Ioo (0:ℝ) 1 ⊆ range (fun y => (f y : ℝ)) := h
    have h3 := (Cardinal.lift_le.mpr (Cardinal.mk_le_mk_of_subset h1)).trans
      (Cardinal.mk_range_le_lift (f := fun y => (f y : ℝ)))
    rw [Cardinal.mk_Ioo_real one_pos] at h3
    exact absurd h3 (not_le.mpr (by simpa using hX))
  obtain ⟨r, hr, hrn⟩ := hex
  have hopen : IsOpen ((fun y => (f y : ℝ)) ⁻¹' Iio r) := isOpen_Iio.preimage hg
  have hclosed : IsClosed ((fun y => (f y : ℝ)) ⁻¹' Iio r) := by
    have : (fun y => (f y : ℝ)) ⁻¹' Iio r = (fun y => (f y : ℝ)) ⁻¹' Iic r := by
      ext y
      simp only [mem_preimage, mem_Iio, mem_Iic]
      constructor
      · intro h; exact h.le
      · intro h
        refine lt_of_le_of_ne h ?_
        intro e
        exact hrn ⟨y, e⟩
    rw [this]
    exact isClosed_Iic.preimage hg
  refine ⟨(fun y => (f y : ℝ)) ⁻¹' Iio r, ?_, ?_, ?_⟩
  · first | exact ⟨hclosed, hopen⟩ | exact ⟨hopen, hclosed⟩
  · show (f x : ℝ) < r
    rw [hfx]
    simpa using hr.1
  · intro y hy
    by_contra hyU
    have h1 : f y = 1 := hfU hyU
    have h2 : (f y : ℝ) < r := hy
    rw [h1] at h2
    have := hr.2
    simp at h2
    linarith
