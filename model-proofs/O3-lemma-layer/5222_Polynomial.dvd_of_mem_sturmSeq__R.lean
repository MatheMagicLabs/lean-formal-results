/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.dvd_of_mem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma dvd_of_mem_sturmSeq {d p q s : K[X]} (hp : d ∣ p) (hq : d ∣ q)
    (hs : s ∈ sturmSeq p q) : d ∣ s := by
  have key : ∀ a b : K[X], d ∣ a → d ∣ b → d ∣ a % b := fun a b ha hb => by
    rw [EuclideanDomain.mod_eq_sub_mul_div]
    exact dvd_sub ha (dvd_mul_of_dvd_left hb _)
  induction p, q using sturmSeq.induct <;> rw [sturmSeq] at hs <;>
    simp_all [key, dvd_neg]
  all_goals first
    | done
    | (rcases hs with rfl | hs
       · assumption
       · simp_all [key, dvd_neg])
