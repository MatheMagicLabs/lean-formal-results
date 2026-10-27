/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_eq_zero_iff_nontrivial_linearMap
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 200
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_eq_zero_iff_nontrivial_linearMap (N M : ModuleCat.{v} R) :
    N.depth M = 0 ↔ Nontrivial (N →ₗ[R] M) := by
  have h := depth_eq_iff N M 0
  simp only [Nat.cast_zero] at h
  rw [h]
  let e : Ext N M 0 ≃+ (N →ₗ[R] M) :=
    (Abelian.Ext.addEquiv₀).trans (ModuleCat.homAddEquiv)
  refine ⟨fun ⟨h1, _⟩ => ?_, fun h1 => ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩⟩
  · exact e.toEquiv.nontrivial_congr.mp h1
  · exact e.toEquiv.nontrivial_congr.mpr h1
