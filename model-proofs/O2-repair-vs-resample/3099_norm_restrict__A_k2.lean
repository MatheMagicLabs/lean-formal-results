/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     norm_restrict
Source:      Mathlib @ a02a63c2, Mathlib/NumberTheory/ModularForms/NormTrace.lean, line 300
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma norm_restrict (hGH : 𝒢 ≤ ℋ) [ℋ.HasDetPlusMinusOne] :
    ModularForm.norm ℋ (f.restrict hGH) = (f : ℍ → ℂ) ^ 𝒢.relIndex ℋ := by
  let : Fintype 𝒬 := Fintype.ofFinite _
  ext τ
  rw [ModularForm.coe_norm, Finset.prod_apply]
  simp [quotientFunc_restrict, Subgroup.index_eq_card, Subgroup.relIndex,
    Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card, Pi.pow_apply]
