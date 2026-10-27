/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Finset.prod_extend_one_of_injective
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean, line 515
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
@[to_additive]
theorem prod_extend_one_of_injective [Fintype ι] {t : Finset κ} {f : ι → κ} (g : ι → M)
    (hf : Injective f) (ht : ∀ i, f i ∈ t) :
    ∏ i ∈ t, extend f g 1 i = ∏ i, g i := by
  have hfg : FactorsThrough g f := hf.factorsThrough g
  have hbij : Set.BijOn f (Finset.univ : Finset ι) ((t : Set κ) ∩ Set.range f) := by
    refine ⟨?_, hf.injOn, ?_⟩
    · intro x _
      exact ⟨Finset.mem_coe.2 (ht x), ⟨x, rfl⟩⟩
    · intro y hy
      obtain ⟨_, x, rfl⟩ := hy
      exact ⟨x, by simp, rfl⟩
  exact prod_extend_one hfg hbij
