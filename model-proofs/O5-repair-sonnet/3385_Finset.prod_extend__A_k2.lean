/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.prod_extend
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean, line 497
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive]
theorem prod_extend [DecidableEq κ] {t : Finset κ} {f : ι → κ} {g : ι → M} (j : κ → M)
    (hfg : FactorsThrough g f) (hf : Set.BijOn f s (t ∩ Set.range f)) :
    ∏ i ∈ t, extend f g j i = (∏ i ∈ t \ s.image f, j i) * ∏ i ∈ s, g i := by
  classical
  have hsub : s.image f ⊆ t := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hx
    exact (hf.mapsTo ha).1
  rw [← prod_sdiff hsub, prod_image hf.injOn]
  congr 1
  · refine prod_congr rfl fun i hi => ?_
    have hni : i ∉ Set.range f := by
      intro hr
      rw [mem_sdiff] at hi
      obtain ⟨a, ha, rfl⟩ := hf.surjOn ⟨hi.1, hr⟩
      exact hi.2 (mem_image_of_mem _ ha)
    exact Function.extend_apply' _ _ _ hni
  · refine prod_congr rfl fun i hi => ?_
    exact hfg.extend_apply _ _
