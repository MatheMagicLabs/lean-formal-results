/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.zero_notMem_sturmSeq
Source:      Mathlib @ a02a63c2, Mathlib/Algebra/Polynomial/Sturm/Sequence.lean, line 109
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Polynomial
variable {K : Type*} [Field K] [DecidableEq K]

lemma zero_notMem_sturmSeq (p q : K[X]) : 0 ∉ sturmSeq p q := by
  generalize hn : (sturmSeq p q).length = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
    by_cases hp : p = 0
    · simp [hp, sturmSeq_zero_left]
    · rw [sturmSeq_cons hp]
      simp only [List.mem_cons, not_or]
      constructor
      · exact fun h => hp h.symm
      · apply ih (sturmSeq q (-p % q)).length
        · rw [sturmSeq_cons hp, List.length_cons] at hn
          omega
        · rfl
