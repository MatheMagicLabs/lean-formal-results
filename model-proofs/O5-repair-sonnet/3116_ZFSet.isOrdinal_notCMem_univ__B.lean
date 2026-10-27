/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.isOrdinal_notCMem_univ
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 559
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isOrdinal_notCMem_univ : {x | IsOrdinal x} ᶜ∉ (.univ : ZFClass.{u}) := by
  rintro ⟨S, hS, -⟩
  have hmem : ∀ y, y ∈ S ↔ IsOrdinal y := fun y => by
    have := Set.ext_iff.mp hS y
    simpa using this
  have hO : IsOrdinal S := by
    refine ⟨?_, ?_⟩
    · intro y hy z hz
      have hy' : IsOrdinal y := (hmem y).1 hy
      have hz' : IsOrdinal z := by
        first
          | exact hy'.of_mem hz
          | exact hy'.mem hz
      exact (hmem z).2 hz'
    · intro y z w hyz hzw hw
      have hw' : IsOrdinal w := (hmem w).1 hw
      exact hw'.isTransitive z hzw hyz
  exact ZFSet.mem_irrefl S ((hmem S).2 hO)
