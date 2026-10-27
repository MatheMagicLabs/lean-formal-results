/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_zero_iff_nontrivial_linearMap
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 200
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_eq_zero_iff_nontrivial_linearMap (N M : ModuleCat.{v} R) :
    N.depth M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  have e : Ext N M 0 ≃ (N →ₗ[R] M) := Ext.homEquiv₀.trans
    { toFun := fun f => f.hom
      invFun := fun f => ModuleCat.ofHom f
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h0 := depth_eq_iff N M 0
  rw [Nat.cast_zero] at h0
  rw [h0]
  exact ⟨fun h => @Equiv.nontrivial _ _ e.symm h.1,
    fun h => ⟨@Equiv.nontrivial _ _ e h, fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩
