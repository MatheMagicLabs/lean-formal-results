/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsValuativeTopology.isClosedMap_restrict
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/ValuativeRel/Completion.lean, line 157
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma isClosedMap_restrict :
    IsClosedMap (v.restrict : K → v.ValueGroup₀) := by
  intro F hF
  rw [WithZeroTopology.isClosed_iff]
  by_cases h0 : (0 : K) ∈ F
  · left
    exact ⟨0, h0, map_zero _⟩
  · right
    have hn : Fᶜ ∈ 𝓝 (0 : K) := hF.isOpen_compl.mem_nhds h0
    obtain ⟨γ, hγ⟩ := (v.mem_nhds_zero_iff _).1 hn
    refine ⟨γ, γ.ne_zero, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    by_contra hlt
    simp only [mem_Ici, not_le] at hlt
    exact hγ hlt hx
