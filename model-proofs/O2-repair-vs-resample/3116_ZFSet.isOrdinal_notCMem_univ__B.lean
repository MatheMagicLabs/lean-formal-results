/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ZFSet.isOrdinal_notCMem_univ
Source:      Mathlib @ a02a63c2, Mathlib/SetTheory/ZFC/Class.lean, line 559
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem isOrdinal_notCMem_univ : {x | IsOrdinal x} ᶜ∉ (.univ : ZFClass.{u}) := by
  rintro ⟨x, hx, -⟩
  have h : ∀ y, y ∈ x ↔ IsOrdinal y := fun y => by
    show y ∈ x ↔ y ∈ {x : ZFSet.{u} | IsOrdinal x}
    rw [← hx]
    exact SetLike.mem_coe.symm
  have hord : IsOrdinal x :=
    ⟨fun y hy z hz => (h z).2 (((h y).1 hy).mem hz),
     fun hyz hzw hwx => ((h _).1 hwx).mem_trans hyz hzw⟩
  exact mem_irrefl x ((h x).2 hord)
