/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_min_fst_trd_le_snd_left
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 216
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_min_fst_trd_le_snd_left
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact) (N : ModuleCat.{v} R) :
    S.X₁.depth N ⊓ S.X₃.depth N ≤ S.X₂.depth N := by
  show _ ≤ sSup _
  apply le_sSup
  simp only [Set.mem_setOf_eq]
  intro i hi
  have h1 := subsingleton_ext_of_lt_depth (lt_of_lt_of_le hi inf_le_left)
  have h3 := subsingleton_ext_of_lt_depth (lt_of_lt_of_le hi inf_le_right)
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ z : Ext S.X₂ N i, z = 0 by rw [h x, h y]
  intro z
  obtain ⟨x₃, hx₃⟩ := Ext.contravariant_sequence_exact₂ hS N z (Subsingleton.elim _ _)
  rw [← hx₃, Subsingleton.elim x₃ 0, Ext.comp_zero]
