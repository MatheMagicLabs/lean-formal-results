/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/CompletelyRegular.lean, line 210
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
  set g : X → ℝ := fun y => (f y : ℝ) with hg_def
  have hg : Continuous g := continuous_subtype_val.comp hf
  obtain ⟨r, ⟨hr0, hr1⟩, hr⟩ : ∃ r ∈ Ioo (0:ℝ) 1, r ∉ range g := by
    by_contra h
    push_neg at h
    have h1 : lift.{u} #(Ioo (0:ℝ) 1) ≤ lift.{u} #(range g) :=
      lift_le.mpr (mk_le_mk_of_subset h)
    rw [mk_Ioo_real zero_lt_one, lift_continuum] at h1
    have h2 := mk_range_le_lift (f := g)
    rw [lift_uzero] at h2
    exact absurd (h1.trans h2) (not_le.mpr hX)
  refine ⟨g ⁻¹' Iio r, ?_, ?_, ?_⟩
  · show IsClopen _
    refine ⟨?_, isOpen_Iio.preimage hg⟩
    have : g ⁻¹' Iio r = g ⁻¹' Iic r := by
      ext y
      simp only [mem_preimage, mem_Iio, mem_Iic]
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h fun e => hr ⟨y, e⟩⟩
    rw [this]
    exact isClosed_Iic.preimage hg
  · show ((f x : I) : ℝ) < r
    rw [hfx]
    simpa using hr0
  · intro y hy
    by_contra hyU
    have h1 := hfU hyU
    simp only [Pi.one_apply] at h1
    have h2 : g y = 1 := by
      show ((f y : I) : ℝ) = 1
      rw [h1]
      simp
    have h3 : g y < r := hy
    linarith
