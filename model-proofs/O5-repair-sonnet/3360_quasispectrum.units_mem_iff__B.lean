/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum.units_mem_iff
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 258
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma quasispectrum.units_mem_iff (u : Rˣ) (a : A) :
    (u : R) ∈ quasispectrum R a ↔ ¬ IsQuasiregular (-((u⁻¹ : Rˣ) • a)) := by
  constructor
  · intro h
    have := h u.isUnit
    have e : u.isUnit.unit = u := Units.ext u.isUnit.unit_spec
    rw [e] at this
    exact this
  · intro h hr
    have e : hr.unit = u := Units.ext hr.unit_spec
    rw [e]
    exact h
