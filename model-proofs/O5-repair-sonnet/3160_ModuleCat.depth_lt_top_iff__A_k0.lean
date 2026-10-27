/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ModuleCat.depth_lt_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/Depth/Basic.lean, line 118
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma depth_lt_top_iff (N M : ModuleCat.{v} R) :
    N.depth M < ⊤ ↔ ∃ n, Nontrivial (Ext N M n) := by
  rw [lt_top_iff_ne_top, Ne, depth_eq_top_iff]
  constructor
  · intro h
    by_contra hne
    apply h
    intro i
    by_contra hi
    exact hne ⟨i, not_subsingleton_iff_nontrivial.mp hi⟩
  · rintro ⟨n, hn⟩ h
    have := h n
    exact not_nontrivial_iff_subsingleton.mpr this hn
