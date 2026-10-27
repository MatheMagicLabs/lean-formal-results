/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_zero_right
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 98
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA-leanstral-agent, arm -, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 as a tool-using agent (Mistral Vibe)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

@[simp]
lemma sturmSeq_zero_right (p : K[X]) :
    sturmSeq p 0 = if p = 0 then [] else [p] := by
  by_cases hp : p = 0
  · simp [hp, sturmSeq]
  · simp [hp, sturmSeq, sturmSeq_zero_left]
