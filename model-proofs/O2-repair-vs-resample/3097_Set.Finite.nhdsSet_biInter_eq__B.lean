/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Set.Finite.nhdsSet_biInter_eq
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Separation/Regular.lean, line 559
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem Set.Finite.nhdsSet_biInter_eq [NormalSpace X] {ι : Type*} {s : Set ι} {K : ι → Set X}
    (hs : s.Finite) (hK : ∀ i ∈ s, IsClosed (K i)) : 𝓝ˢ (⋂ i ∈ s, K i) = ⨅ i ∈ s, 𝓝ˢ (K i) := by
  classical
  obtain ⟨t, rfl⟩ := hs.exists_finset_coe
  clear hs
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    have hKa : IsClosed (K a) := hK a (by simp)
    have hKt : ∀ i ∈ (t : Set ι), IsClosed (K i) := fun i hi => hK i (by simp_all)
    simp only [Finset.coe_insert, Set.biInter_insert, iInf_insert]
    rw [hKa.nhdsSet_inter_eq (isClosed_biInter hKt), ih hKt]
