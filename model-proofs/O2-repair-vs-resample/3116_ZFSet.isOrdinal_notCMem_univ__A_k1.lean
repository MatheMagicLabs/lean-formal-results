/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.isOrdinal_notCMem_univ
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 559
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isOrdinal_notCMem_univ : {x | IsOrdinal x} ᶜ∉ (.univ : ZFClass.{u}) := by
  rintro ⟨x, hx, -⟩
  have hmem : ∀ y, y ∈ x ↔ IsOrdinal y := fun y => by
    rw [← SetLike.mem_coe, hx, Set.mem_setOf_eq]
  suffices h : IsOrdinal x from mem_irrefl x ((hmem x).2 h)
  refine ⟨fun y hy z hz => ?_, fun hyz hzw hwx => ?_⟩
  · exact (hmem z).2 (((hmem y).1 hy).mem hz)
  · exact ((hmem _).1 hwx).mem_trans hyz hzw
