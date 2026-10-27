/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/CompletelyRegular.lean, line 210
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 1 (round 0 = first attempt)
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
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro s hs
      exact hs.2
    · intro a u hau hu
      obtain ⟨f, hf, hfa, hf1⟩ :=
        CompletelyRegularSpace.completely_regular a uᶜ hu.isClosed_compl (fun h => h hau)
      set g : X → ℝ := fun y => ((f y : I) : ℝ) with hgdef
      have hg : Continuous g := continuous_subtype_val.comp hf
      obtain ⟨r, hr, hrg⟩ : ∃ r, r ∈ Ioo (0:ℝ) 1 ∧ r ∉ range g := by
        by_contra hcon
        push_neg at hcon
        have hsub : Ioo (0:ℝ) 1 ⊆ range g := fun r hr => hcon r hr
        have h1 : Cardinal.lift.{u} #(Ioo (0:ℝ) 1) ≤ Cardinal.lift.{u} #(range g) :=
          Cardinal.lift_le.2 (Cardinal.mk_le_mk_of_subset hsub)
        have h2 : Cardinal.lift.{u} #(range g) ≤ Cardinal.lift.{0} #X :=
          Cardinal.mk_range_le_lift
        rw [Cardinal.mk_Ioo_real (by norm_num), Cardinal.lift_continuum] at h1
        have h3 : Cardinal.lift.{0} #X < 𝔠 := Cardinal.lift_lt_continuum.2 hX
        exact absurd (h1.trans h2) (not_le.2 h3)
      have heq : g ⁻¹' Iio r = g ⁻¹' Iic r := by
        ext y
        simp only [mem_preimage, mem_Iio, mem_Iic]
        constructor
        · exact le_of_lt
        · intro h
          exact lt_of_le_of_ne h (fun e => hrg ⟨y, e⟩)
      refine ⟨g ⁻¹' Iio r, ?_, ?_, ?_⟩
      · show IsClopen (g ⁻¹' Iio r)
        refine ⟨?_, isOpen_Iio.preimage hg⟩
        rw [heq]
        exact isClosed_Iic.preimage hg
      · show g a < r
        simpa [g, hfa] using hr.1
      · intro y hy
        by_contra hyu
        have h1 : g y = 1 := by
          show ((f y : I) : ℝ) = 1
          rw [hf1 hyu]
          first | rfl | simp
        have h2 : g y < r := hy
        linarith [hr.2]
  first
  | exact ZeroDimensionalSpace.of_isTopologicalBasis hB
  | exact hB.zeroDimensionalSpace
  | exact ZeroDimensionalSpace.of_isTopologicalBasis_isClopen hB
  | exact (zeroDimensionalSpace_iff_isTopologicalBasis_isClopen).2 hB
  | exact (zeroDimensionalSpace_iff_isTopologicalBasis).2 hB
  | exact zeroDimensionalSpace_iff.2 hB
  | exact (zeroDimensionalSpace_iff (X := X)).2 hB
  | exact ZeroDimensionalSpace.mk' hB
  | exact ZeroDimensionalSpace.of_clopen_basis hB
  | exact ZeroDimensionalSpace.of_isClopen_basis hB
  | exact hB.zeroDimensionalSpace_of_isClopen (fun s hs => hs)
  | exact ZeroDimensionalSpace.of_isTopologicalBasis hB (fun s hs => hs)
  | exact (zeroDimensionalSpace_iff_exists_isTopologicalBasis).2 ⟨_, hB, fun s hs => hs⟩
  | exact zeroDimensionalSpace_iff.2 ⟨_, hB, fun s hs => hs⟩
