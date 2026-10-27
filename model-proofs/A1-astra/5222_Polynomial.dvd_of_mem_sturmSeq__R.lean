/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.dvd_of_mem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 127
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma dvd_of_mem_sturmSeq {d p q s : K[X]} (hp : d ∣ p) (hq : d ∣ q)
    (hs : s ∈ sturmSeq p q) : d ∣ s := by
  revert hp hq hs
  fun_induction sturmSeq p q <;> intro hp hq hs
  all_goals
    have hm := (EuclideanDomain.dvd_mod_iff hq).2 (dvd_neg.mpr hp)
    simp_all only [List.mem_cons, List.not_mem_nil]
  all_goals
    rcases hs with rfl | hs
    · exact hp
    · simp_all
