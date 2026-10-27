/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.degreeOf_varChange_ne_of_ne
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 118
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
private lemma degreeOf_varChange_ne_of_ne (hv : v ∈ f.support) (hw : w ∈ f.support) (ne : v ≠ w) :
    (varChange f <| monomial v <| f.coeff v).degreeOf 0 ≠
    (varChange f <| monomial w <| f.coeff w).degreeOf 0 := by
  have vlt : ∀ i, v i < 2 + f.totalDegree := fun i ↦ by
    have := (monomial_le_degreeOf i hv).trans (degreeOf_le_totalDegree f i)
    omega
  have wlt : ∀ i, w i < 2 + f.totalDegree := fun i ↦ by
    have := (monomial_le_degreeOf i hw).trans (degreeOf_le_totalDegree f i)
    omega
  rw [degreeOf_zero_varChange f v (mem_support_iff.mp hv),
    degreeOf_zero_varChange f w (mem_support_iff.mp hw)]
  exact sum_r_mul_ne f v w vlt wlt ne
