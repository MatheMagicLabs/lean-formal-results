/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/CompletelyRegular.lean, line 210
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

universe u v
noncomputable section
open Cardinal Set Topology TopologicalSpace Filter unitInterval
variable {X : Type u} [TopologicalSpace X]

theorem CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
    [CompletelyRegularSpace X] (hX : .mk X < 𝔠) : ZeroDimensionalSpace X := by
  have hB : IsTopologicalBasis {s : Set X | IsClopen s} := by
    refine isTopologicalBasis_of_isOpen_of_nhds (fun u hu => hu.isOpen) ?_
    intro x U hxU hU
    obtain ⟨f, hf, hfx, hf1⟩ :=
      CompletelyRegularSpace.completely_regular x Uᶜ hU.isClosed_compl (fun h => h hxU)
    have hc : Continuous (fun y => (f y : ℝ)) := continuous_subtype_val.comp hf
    have hsub : ¬ (Ioo (0:ℝ) 1 ⊆ range (fun y => (f y : ℝ))) := by
      intro h
      have h1 := Cardinal.mk_le_mk_of_subset h
      rw [Cardinal.mk_Ioo_real (by norm_num : (0:ℝ) < 1)] at h1
      have h4 : Cardinal.lift.{u} 𝔠 ≤ Cardinal.lift.{u} #(range (fun y => (f y : ℝ))) :=
        Cardinal.lift_le.mpr h1
      have h3 := h4.trans (Cardinal.mk_range_le_lift (f := fun y => (f y : ℝ)))
      rw [Cardinal.lift_continuum, Cardinal.lift_uzero] at h3
      exact absurd h3 (not_le.mpr hX)
    obtain ⟨r, hr, hrn⟩ := Set.not_subset.mp hsub
    refine ⟨{y | (f y : ℝ) < r}, ?_, ?_, ?_⟩
    · have heq : {y | (f y : ℝ) < r} = {y | (f y : ℝ) ≤ r} := by
        ext y
        simp only [mem_setOf_eq]
        refine ⟨le_of_lt, fun h => lt_of_le_of_ne h ?_⟩
        intro h'
        exact hrn ⟨y, h'⟩
      refine ⟨?_, isOpen_lt hc continuous_const⟩
      rw [heq]
      exact isClosed_le hc continuous_const
    · show ((f x : ℝ)) < r
      simpa [hfx] using hr.1
    · intro y hy
      by_contra hyU
      have h1 : f y = 1 := hf1 hyU
      have : (1:ℝ) < r := by simpa [h1] using hy
      linarith [hr.2]
  have hE : ∀ U ∈ {s : Set X | IsClopen s},
      HasSmallInductiveDimensionLT (↑(frontier U)) 0 := by
    intro U hU
    have hU' : IsClopen U := hU
    rw [hU'.frontier_eq]
    first
      | infer_instance
      | simp
      | (constructor <;> simp)
      | aesop
  first
    | exact ⟨⟨_, hB, hE⟩⟩
    | exact ⟨_, hB, hE⟩
    | (constructor <;> first | exact hB | exact hE)
