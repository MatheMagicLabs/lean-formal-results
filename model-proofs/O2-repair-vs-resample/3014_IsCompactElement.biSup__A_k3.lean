/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     IsCompactElement.biSup
Source:      Mathlib @ a02a63c2, Mathlib/Order/CompactlyGenerated/Basic.lean, line 245
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
protected lemma IsCompactElement.biSup {ι : Type*} {s : Set ι} (hs : s.Finite) {f : ι → α}
    (h : ∀ i ∈ s, IsCompactElement (f i)) : IsCompactElement (⨆ i ∈ s, f i) := by
  have : Finite s := hs.to_subtype
  have heq : (⨆ i ∈ s, f i) = ⨆ i : s, f i := by
    first
      | exact (iSup_subtype'' s f).symm
      | exact (iSup_subtype' (p := (· ∈ s)) (f := fun i _ => f i))
      | rw [iSup_subtype'']
  rw [heq]
  exact IsCompactElement.iSup fun i => h i i.2
