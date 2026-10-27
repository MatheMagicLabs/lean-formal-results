/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     trace_restrict
Source:      Mathlib @ a02a63c2, Mathlib/NumberTheory/ModularForms/NormTrace.lean, line 291
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma trace_restrict (hGH : 𝒢 ≤ ℋ) :
    .trace ℋ (f.restrict hGH) = 𝒢.relIndex ℋ • f := by
  ext τ
  let := Fintype.ofFinite 𝒬
  show (∑ q : 𝒬, quotientFunc (f.restrict hGH) q) τ = _
  rw [Finset.sum_apply]
  simp only [quotientFunc_restrict]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
  simp [Subgroup.relIndex, Subgroup.index]
