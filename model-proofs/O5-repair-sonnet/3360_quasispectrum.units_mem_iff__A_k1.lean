/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum.units_mem_iff
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 258
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma quasispectrum.units_mem_iff (u : Rˣ) (a : A) :
    (u : R) ∈ quasispectrum R a ↔ ¬ IsQuasiregular (-((u⁻¹ : Rˣ) • a)) := by
  have e : ∀ hr : IsUnit (u : R), hr.unit = u := fun hr => IsUnit.unit_of_val_units hr
  show (∀ hr : IsUnit (u : R), ¬ IsQuasiregular (-(hr.unit⁻¹ • a))) ↔ _
  simp only [e]
  exact ⟨fun h => h u.isUnit, fun h _ => h⟩
