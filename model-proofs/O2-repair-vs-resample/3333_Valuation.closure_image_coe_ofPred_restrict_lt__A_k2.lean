/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_restrict_lt
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 420
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem closure_image_coe_ofPred_restrict_lt (γ : v.ValueGroup₀ˣ) :
    closure ((↑) '' {x : K | v.restrict x < γ.1}) =
      {x : Completion K | v.extension x < embedding γ.1} := by
  have h : embedding γ.1 ≠ 0 := fun h ↦
    γ.ne_zero (embedding_injective (h.trans (map_zero _).symm))
  rw [← v.closure_image_coe_ofPred_map_lt h]
  congr 2
  ext x
  show v.restrict x < γ.1 ↔ v x < embedding γ.1
  first
  | rw [← v.embedding_restrict]; exact embedding_strictMono.lt_iff_lt.symm
  | exact restrict_lt_iff_lt_embedding
  | simp [restrict_lt_iff_lt_embedding]
