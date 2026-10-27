/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  rw [← Equiv.sigmaSubtypeFiberEquivSubtype Sym2.mk.uncurry (q := (· ∈ fromRel sym)) (by simp)
    |>.cardinal_eq, Cardinal.mk_sigma, mul_comm]
  have key : ∀ z : fromRel sym,
      #{x : α × α // Sym2.mk.uncurry x = (z : Sym2 α)} = 2 := by
    intro z
    obtain ⟨z, hz⟩ := z
    rw [← Set.coe_ofPred, ← Set.preimage_singleton]
    induction z using Sym2.ind
    rename_i a b
    have hab : a ≠ b := by
      rintro rfl
      exact Std.Irrefl.irrefl a (by simpa using hz)
    rw [← Set.cast_ncard (finite_mk_fiber _),
      ncard_mk_fiber_of_not_isDiag (by simpa using hab)]
    norm_cast
  simp only [key, Cardinal.sum_const']
