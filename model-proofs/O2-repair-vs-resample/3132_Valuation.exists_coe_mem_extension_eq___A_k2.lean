/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Valuation.exists_coe_mem_extension_eq₂
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 321
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma exists_coe_mem_extension_eq₂ {x y : Completion K} {U : Set (Completion K × Completion K)}
    (hU : U ∈ 𝓝 (x, y)) : ∃ r s : K, ((r : Completion K), (s : Completion K)) ∈ U ∧
      v.extension x = v r ∧ v.extension y = v s := by
  obtain ⟨t₁, ht₁, t₂, ht₂, hU'⟩ := mem_nhds_prod_iff.1 hU
  obtain ⟨r, hr, hr'⟩ := v.exists_coe_mem_extension_eq ht₁
  obtain ⟨s, hs, hs'⟩ := v.exists_coe_mem_extension_eq ht₂
  exact ⟨r, s, hU' (Set.mk_mem_prod hr hs), hr', hs'⟩
