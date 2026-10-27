/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     trace_restrict
Source:      Mathlib @ a02a63c2, Mathlib/NumberTheory/ModularForms/NormTrace.lean, line 291
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma trace_restrict (hGH : 𝒢 ≤ ℋ) :
    .trace ℋ (f.restrict hGH) = 𝒢.relIndex ℋ • f := by
  ext τ
  have h := quotientFunc_restrict f hGH
  let := Fintype.ofFinite (ℋ ⧸ 𝒢.subgroupOf ℋ)
  simp [ModularForm.coe_trace, h, Finset.sum_const, Subgroup.relIndex,
    Nat.card_eq_fintype_card, nsmul_eq_mul]
  left
  exact Nat.card_eq_fintype_card.symm
