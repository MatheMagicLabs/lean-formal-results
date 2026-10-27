/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.zero_notMem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 109
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma zero_notMem_sturmSeq (p q : K[X]) : 0 ∉ sturmSeq p q := by
  fun_induction sturmSeq p q <;> (try simp_all)
  all_goals first
    | exact Ne.symm ‹_›
    | (intro h; subst h; simp_all)
