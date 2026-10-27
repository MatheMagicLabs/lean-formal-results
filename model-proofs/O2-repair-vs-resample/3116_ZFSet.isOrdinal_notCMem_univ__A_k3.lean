/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.isOrdinal_notCMem_univ
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 559
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isOrdinal_notCMem_univ : {x | IsOrdinal x} ᶜ∉ (.univ : ZFClass.{u}) := by
  rintro ⟨x, hx, -⟩
  have key : ∀ y, y ∈ x ↔ IsOrdinal y := fun y => by
    have := Set.ext_iff.1 hx y
    simpa using this
  have hxo : IsOrdinal x := by
    refine ⟨?_, fun hyz hzw hw => ?_⟩
    · intro y hy z hz
      exact (key z).2 (((key y).1 hy).mem hz)
    · exact ((key _).1 hw).mem_trans hyz hzw
  exact mem_irrefl x ((key x).2 hxo)
