/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_eq_nil_iff
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 87
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
lemma sturmSeq_eq_nil_iff {p q : K[X]} :
    sturmSeq p q = [] ↔ p = 0 := by
  constructor
  · intro h
    by_contra hp
    have hcons := sturmSeq_cons (q := q) hp
    rw [hcons] at h
    exact List.cons_ne_nil p _ h
  · intro h
    rw [h]
    exact sturmSeq_zero_left q
