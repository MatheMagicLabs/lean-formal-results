/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.prod_extend
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean, line 497
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive]
theorem prod_extend [DecidableEq κ] {t : Finset κ} {f : ι → κ} {g : ι → M} (j : κ → M)
    (hfg : FactorsThrough g f) (hf : Set.BijOn f s (t ∩ Set.range f)) :
    ∏ i ∈ t, extend f g j i = (∏ i ∈ t \ s.image f, j i) * ∏ i ∈ s, g i := by
  have hsub : s.image f ⊆ t := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hx
    exact (hf.mapsTo ha).1
  rw [← prod_sdiff hsub, prod_image hf.injOn]
  congr 1
  · refine prod_congr rfl fun i hi => ?_
    rw [mem_sdiff] at hi
    apply extend_apply'
    rintro ⟨a, rfl⟩
    obtain ⟨b, hb, hba⟩ :=
      hf.surjOn (show f a ∈ (t : Set κ) ∩ Set.range f from ⟨hi.1, a, rfl⟩)
    exact hi.2 (mem_image.2 ⟨b, hb, hba⟩)
  · exact prod_congr rfl fun a _ => hfg.extend_apply j a
