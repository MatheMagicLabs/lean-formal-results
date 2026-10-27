/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.sturmSeq_mul_left
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 139
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3LA3-leanstral-agent-feedback, arm rueck, verified in final
Prover:      labs-leanstral-1-5
Setup:       Leanstral 1.5 agent with goal-state feedback (arm rueck)
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
    have hrp : r * p ≠ 0 := mul_ne_zero hr hp
    rw [sturmSeq_cons hrp, sturmSeq_cons hp]
    have hmod : (-(r * p)) % (r * q) = r * ((-p) % q) := by
      calc
        (-(r * p)) % (r * q) = (r * (-p)) % (r * q) := by ring
        _ = r * ((-p) % q) := by rw [mul_mod_mul_left]
    rw [hmod, ih]
    rfl
