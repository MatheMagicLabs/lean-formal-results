/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ContinuousAlternatingMap.alternatization_toContinuousMultilinearMap
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Module/Alternating/Basic.lean, line 659
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem _root_.ContinuousAlternatingMap.alternatization_toContinuousMultilinearMap
    (f : M [⋀^ι]→L[R] N) :
    f.toContinuousMultilinearMap.alternatization = (Fintype.card ι)! • f := by
  ext v
  rw [alternatization_apply_apply]
  have key : ∀ σ : Equiv.Perm ι,
      Equiv.Perm.sign σ • (f.toContinuousMultilinearMap) (v ∘ σ) = f v := by
    intro σ
    rw [ContinuousAlternatingMap.coe_toContinuousMultilinearMap,
      ← ContinuousAlternatingMap.coe_toAlternatingMap, AlternatingMap.map_perm, smul_smul,
      Int.units_mul_self, one_smul]
  rw [Finset.sum_congr rfl fun σ _ => key σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm]
  rfl
