/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/CompletelyRegular.lean, line 210
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
    [CompletelyRegularSpace X] (hX : .mk X < 𝔠) : ZeroDimensionalSpace X := by
  rw [zeroDimensionalSpace_iff_isTopologicalBasis_isClopen]
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.isOpen) ?_
  intro x U hxU hU
  obtain ⟨f, hf, hfx, hfU⟩ := CompletelyRegularSpace.completely_regular_isOpen x U hU hxU
  let g : X → ℝ := fun y => (f y : ℝ)
  have hg : Continuous g := continuous_subtype_val.comp hf
  have hex : ∃ r ∈ Ioo (0:ℝ) 1, r ∉ range g := by
    by_contra! h
    have h1 : #(Ioo (0:ℝ) 1) ≤ #(range g) := Cardinal.mk_le_mk_of_subset h
    have h2 := Cardinal.mk_range_le_lift (f := g)
    rw [Cardinal.mk_Ioo_real zero_lt_one] at h1
    have h3 : Cardinal.lift.{u} 𝔠 ≤ Cardinal.lift.{u} #(range g) := Cardinal.lift_le.mpr h1
    rw [Cardinal.lift_continuum] at h3
    have h2' : Cardinal.lift.{u} #(range g) ≤ #X := by simpa using h2
    have h4 : (𝔠 : Cardinal.{u}) ≤ #X := le_trans h3 h2'
    exact absurd hX (not_lt.mpr h4)
  obtain ⟨r, ⟨hr0, hr1⟩, hr⟩ := hex
  refine ⟨g ⁻¹' Iio r, ⟨?_, isOpen_Iio.preimage hg⟩, ?_, ?_⟩
  · have : g ⁻¹' Iio r = g ⁻¹' Iic r := by
      ext y
      simp only [mem_preimage, mem_Iio, mem_Iic]
      exact ⟨le_of_lt, fun h => lt_of_le_of_ne h (fun e => hr ⟨y, e⟩)⟩
    rw [this]
    exact isClosed_Iic.preimage hg
  · show (f x : ℝ) < r
    rw [hfx]
    simpa using hr0
  · intro y hy
    by_contra hyU
    have h := hfU hyU
    simp only [Pi.one_apply] at h
    have h' : (f y : ℝ) < r := hy
    rw [h] at h'
    have : (1:ℝ) < r := by simpa using h'
    linarith
