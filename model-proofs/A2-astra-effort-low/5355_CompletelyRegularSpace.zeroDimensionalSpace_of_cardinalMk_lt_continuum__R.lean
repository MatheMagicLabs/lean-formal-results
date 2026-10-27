/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/CompletelyRegular.lean, line 210
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

universe u v
noncomputable section
open Cardinal Set Topology TopologicalSpace Filter unitInterval
variable {X : Type u} [TopologicalSpace X]

theorem CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
    [CompletelyRegularSpace X] (hX : .mk X < 𝔠) : ZeroDimensionalSpace X := by
  classical
  constructor
  case s =>
    exact {U : Set X | IsClopen U}
  case h =>
    intro U hU
    rw [hU.frontier_eq]
    infer_instance
  · apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U hU
      exact hU.isOpen
    · intro x U hx hU
      have hc : IsClosed Uᶜ := hU.isClosed_compl
      have hn : x ∉ Uᶜ := by simpa using hx
      have hsep :
          ∃ f : C(X, I), f x = 0 ∧ ∀ y ∈ Uᶜ, f y = 1 := by
        cases ‹CompletelyRegularSpace X› with
        | mk completely_regular =>
          obtain ⟨f, hf, hfx, hfU⟩ := completely_regular x Uᶜ hc hn
          exact ⟨⟨f, hf⟩, hfx, hfU⟩
      obtain ⟨f, hfx, hfU⟩ := hsep
      have hmissing :
          ∃ t ∈ Set.Ioo (0 : ℝ) 1,
            t ∉ Set.range (fun y => (f y : ℝ)) := by
        by_contra! h
        let g : Set.Ioo (0 : ℝ) 1 → X :=
          fun t => Classical.choose (h t t.property)
        have hg : Function.Injective g := by
          intro a b hab
          apply Subtype.ext
          have ha := Classical.choose_spec (h a a.property)
          have hb := Classical.choose_spec (h b b.property)
          change (f (g a) : ℝ) = a at ha
          change (f (g b) : ℝ) = b at hb
          exact ha.symm.trans
            ((congrArg (fun y => (f y : ℝ)) hab).trans hb)
        have hc := Cardinal.lift_mk_le_lift_mk_of_injective hg
        have hi := Cardinal.mk_Ioo_real (show (0 : ℝ) < 1 by norm_num)
        simp only [hi, Cardinal.lift_continuum, Cardinal.lift_id] at hc
        exact (not_le_of_gt hX) (by simpa using hc)
      obtain ⟨t, ht, htf⟩ := hmissing
      let V : Set X := {y | (f y : ℝ) < t}
      have hcont : Continuous (fun y => (f y : ℝ)) :=
        continuous_subtype_val.comp f.continuous
      have hV : IsClopen V := by
        constructor
        · have heq : V = {y | (f y : ℝ) ≤ t} := by
            ext y
            change (f y : ℝ) < t ↔ (f y : ℝ) ≤ t
            exact lt_iff_le_and_ne.trans
              (and_iff_left (fun he => htf ⟨y, he⟩))
          rw [heq]
          exact isClosed_le hcont continuous_const
        · exact isOpen_lt hcont continuous_const
      refine ⟨V, hV, ?_, ?_⟩
      · change (f x : ℝ) < t
        simpa [hfx] using ht.1
      · intro y hy
        by_contra hyU
        have hfy := hfU y hyU
        have : (1 : ℝ) < t := by
          simpa [V, hfy] using hy
        exact (not_lt_of_ge ht.2.le) this
