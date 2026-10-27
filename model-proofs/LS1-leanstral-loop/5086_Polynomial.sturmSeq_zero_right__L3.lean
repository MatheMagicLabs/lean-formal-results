/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_zero_right
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 98
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  LS1-leanstral-loop, arm L3, verified in round 0 (round 0 = first attempt)
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 in a fixed check-and-repair loop: L1 = 1 candidate per round, L3 = up to 3
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

@[simp]
lemma sturmSeq_zero_right (p : K[X]) :
    sturmSeq p 0 = if p = 0 then [] else [p] := by
  by_cases hp : p = 0
  · rw [hp, sturmSeq_zero_left, if_pos rfl]
  · rw [sturmSeq_cons hp, sturmSeq_zero_left, if_neg hp]
