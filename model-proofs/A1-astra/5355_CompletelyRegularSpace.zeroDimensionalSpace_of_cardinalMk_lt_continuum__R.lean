/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CompletelyRegularSpace.zeroDimensionalSpace_of_cardinalMk_lt_continuum
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/CompletelyRegular.lean, line 210
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  have sep (s : Set X) (hs : IsClosed s) (x : X) (hx : x ∉ s) :
      ∃ f : X → ℝ, Continuous f ∧ f x = 0 ∧ ∀ y ∈ s, f y = 1 := by
    obtain ⟨f, hf, hf₀, hf₁⟩ :=
      CompletelyRegularSpace.completely_regular x s hs hx
    refine ⟨fun y => (f y : ℝ), continuous_subtype_val.comp hf, ?_, ?_⟩
    · simpa using congrArg (fun t : I => (t : ℝ)) hf₀
    · intro y hy
      simpa using congrArg (fun t : I => (t : ℝ)) (hf₁ hy)
  constructor
  · change IsTopologicalBasis {s : Set X | IsClopen s}
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro s hs
      exact hs.isOpen
    · intro x U hx hU
      obtain ⟨f, hf, hfx, hfU⟩ := sep Uᶜ hU.isClosed_compl x (by simpa)
      have hmiss : ∃ r ∈ Ioo (0 : ℝ) 1, r ∉ range f := by
        by_contra! h
        let g : Ioo (0 : ℝ) 1 → X :=
          fun r => Classical.choose (h r r.property)
        have hg (r : Ioo (0 : ℝ) 1) : f (g r) = r :=
          Classical.choose_spec (h r r.property)
        have hgi : Function.Injective g := by
          intro a b hab
          apply Subtype.ext
          calc
            (a : ℝ) = f (g a) := (hg a).symm
            _ = f (g b) := congrArg f hab
            _ = b := hg b
        have hc : Cardinal.mk (Ioo (0 : ℝ) 1) = 𝔠 := by
          first
          | exact Cardinal.mk_Ioo_real (by norm_num : (0 : ℝ) < 1)
          | exact Cardinal.mk_Ioo_real 0 1 (by norm_num)
        have hle := Cardinal.lift_mk_le_lift_mk_of_injective hgi
        exact (not_le_of_gt hX) (by simpa [hc] using hle)
      obtain ⟨r, hr, hrf⟩ := hmiss
      have hne (y : X) : f y ≠ r := by
        intro h
        exact hrf ⟨y, h⟩
      have heq : {y | f y < r} = {y | f y ≤ r} := by
        ext y
        change f y < r ↔ f y ≤ r
        exact ⟨fun h => h.le, fun h => lt_of_le_of_ne h (hne y)⟩
      refine ⟨{y | f y < r}, ?_, ?_, ?_⟩
      · exact ⟨heq ▸ isClosed_le hf continuous_const,
          isOpen_lt hf continuous_const⟩
      · show f x < r
        simpa [hfx] using hr.1
      · intro y hy
        by_contra hyU
        have hfy := hfU y hyU
        have : (1 : ℝ) < r := by simpa [hfy] using hy
        exact (not_lt_of_ge hr.2.le) this
  · intro U hU
    haveI : IsEmpty (↥(frontier U)) :=
      ⟨fun x => by simpa [hU.frontier_eq] using x.property⟩
    first
    | infer_instance
    | simpa [HasSmallInductiveDimensionLT] using
        (inferInstance : IsEmpty (↥(frontier U)))
