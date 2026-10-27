/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimplexCategory.Truncated.mono_iff
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicTopology/SimplexCategory/Truncated.lean, line 113
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma mono_iff {d : ℕ} {a b : Truncated d} {f : a ⟶ b} : Mono f ↔ Mono f.hom := by
  constructor
  · intro hf
    rw [SimplexCategory.mono_iff_injective]
    intro x y h
    let z : Truncated d := ⟨⦋0⦌, by simp⟩
    have := hf.right_cancellation (Z := z)
      ⟨SimplexCategory.const _ _ x⟩ ⟨SimplexCategory.const _ _ y⟩
      (ObjectProperty.hom_ext _ (by simp [SimplexCategory.const_comp, h]))
    have := congrArg (fun g => g.hom.toOrderHom 0) this
    simpa using this
  · intro hf
    constructor
    intro Z g h e
    apply ObjectProperty.hom_ext
    exact hf.right_cancellation _ _ (congrArg (fun k => k.hom) e)
