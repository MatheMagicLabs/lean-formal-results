/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     quasispectrum.units_mem_iff
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Algebra/Spectrum/Quasispectrum.lean, line 258
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma quasispectrum.units_mem_iff (u : Rˣ) (a : A) :
    (u : R) ∈ quasispectrum R a ↔ ¬ IsQuasiregular (-((u⁻¹ : Rˣ) • a)) := by
  first
  | simp [quasispectrum]; done
  | show (∀ hr : IsUnit (u : R), ¬ IsQuasiregular (-(hr.unit⁻¹ • a))) ↔ _
    constructor
    · intro h
      have := h u.isUnit
      rwa [show u.isUnit.unit = u from Units.ext u.isUnit.unit_spec] at this
    · intro h hr
      rwa [show hr.unit = u from Units.ext hr.unit_spec]
