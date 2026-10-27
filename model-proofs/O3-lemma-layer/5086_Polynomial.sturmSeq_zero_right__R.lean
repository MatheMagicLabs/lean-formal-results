/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_zero_right
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 98
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

@[simp]
lemma sturmSeq_zero_right (p : K[X]) :
    sturmSeq p 0 = if p = 0 then [] else [p] := by
  rw [sturmSeq]
  split_ifs <;> first
    | rfl
    | (simp_all; done)
    | (rw [sturmSeq]; simp_all; done)
    | (simp_all [sturmSeq]; done)
