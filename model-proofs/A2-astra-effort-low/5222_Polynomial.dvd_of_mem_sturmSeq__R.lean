/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.dvd_of_mem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 3 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma dvd_of_mem_sturmSeq {d p q s : K[X]} (hp : d ∣ p) (hq : d ∣ q)
    (hs : s ∈ sturmSeq p q) : d ∣ s := by
  have hmod (a b : K[X]) (ha : d ∣ a) (hb : d ∣ b) :
      d ∣ -a % b := by
    have he : -a % b = -a - b * (-a / b) :=
      eq_sub_iff_add_eq.mpr (EuclideanDomain.mod_add_div (-a) b)
    rw [he]
    exact dvd_sub (dvd_neg.mpr ha) (dvd_mul_of_dvd_left hb _)
  fun_induction sturmSeq p q generalizing s
  all_goals
    simp_all only [List.mem_cons, List.mem_nil_iff, or_false] <;> grind
