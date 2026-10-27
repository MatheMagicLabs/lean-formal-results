/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.closure_image_coe_ofPred_restrict_lt
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 420
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-haiku, arm B, verified in round 3 (round 0 = first attempt)
Prover:      claude-haiku-4-5
Setup:       Haiku 4.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem closure_image_coe_ofPred_restrict_lt (γ : v.ValueGroup₀ˣ) :
    closure ((↑) '' {x : K | v.restrict x < γ.1}) =
      {x : Completion K | v.extension x < embedding γ.1} := by
  have h : (embedding (γ : v.ValueGroup₀) : Γ₀) ≠ 0 := by
    simp only [ne_eq, map_eq_zero]
    exact Units.ne_zero γ
  convert v.closure_image_coe_ofPred_map_lt h using 2
  ext x
  simp only [mem_ofPred_eq, mem_setOf, extension_le_iff_extensionFun_le,
    restrict_lt_iff_lt_embedding]
