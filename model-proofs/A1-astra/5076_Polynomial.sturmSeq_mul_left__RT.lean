/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_mul_left
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RT, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma sturmSeq_mul_left {r : K[X]} (hr : r ≠ 0) (p q : K[X]) :
    sturmSeq (r * p) (r * q) = (sturmSeq p q).map (r * ·) := by
  induction p, q using sturmSeq.induct
  next q => simp
  next p q hp ih =>
    rw [sturmSeq_cons (mul_ne_zero hr hp), sturmSeq_cons hp,
      ← mul_neg, mul_mod_mul_left, ih, List.map_cons]
