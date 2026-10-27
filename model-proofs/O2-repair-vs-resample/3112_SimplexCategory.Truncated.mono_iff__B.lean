/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimplexCategory.Truncated.mono_iff
Source:      Mathlib @ a02a63c2, Mathlib/AlgebraicTopology/SimplexCategory/Truncated.lean, line 113
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
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
    intro x y hxy
    let z : Truncated d := ⟨⦋0⦌, Nat.zero_le _⟩
    let g : z ⟶ a := (inclusion d).preimage (X := z) (Y := a) (⦋0⦌.const a.obj x)
    let h : z ⟶ a := (inclusion d).preimage (X := z) (Y := a) (⦋0⦌.const a.obj y)
    have e : g = h := by
      rw [← cancel_mono f]
      apply (inclusion d).map_injective
      simp only [Functor.map_comp, g, h, Functor.map_preimage]
      change SimplexCategory.const _ _ x ≫ f.hom = SimplexCategory.const _ _ y ≫ f.hom
      rw [SimplexCategory.const_comp, SimplexCategory.const_comp, hxy]
    have := congrArg (fun k => ((inclusion d).map k)) e
    simp only [g, h, Functor.map_preimage] at this
    have := congrArg (fun k => k.toOrderHom 0) this
    exact this
  · intro h
    exact (inclusion d).mono_of_mono_map (f := f) h
