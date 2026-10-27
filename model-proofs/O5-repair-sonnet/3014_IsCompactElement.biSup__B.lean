/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsCompactElement.biSup
Source:      Mathlib @ a02a63c2, Mathlib/Order/CompactlyGenerated/Basic.lean, line 245
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
protected lemma IsCompactElement.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) {f : ι → α}
    (h : ∀ i ∈ s, IsCompactElement (f i)) : IsCompactElement (⨆ i ∈ s, f i) := by
  haveI := hs.to_subtype
  have e : (⨆ i : s, f i) = ⨆ i ∈ s, f i := iSup_subtype
  rw [← e]
  exact IsCompactElement.iSup (fun i => h i i.2)
