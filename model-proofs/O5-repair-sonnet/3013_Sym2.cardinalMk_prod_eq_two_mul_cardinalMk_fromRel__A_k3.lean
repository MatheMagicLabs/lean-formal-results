/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  rw [← Equiv.sigmaSubtypeFiberEquivSubtype Sym2.mk.uncurry (q := (· ∈ fromRel sym)) (by simp)
    |>.cardinal_eq, Cardinal.mk_sigma, mul_comm]
  rw [← Cardinal.sum_const']
  congr 1
  funext z
  rw [← Set.coe_ofPred, ← Set.preimage_singleton]
  rcases z with ⟨⟨a, b⟩, hz⟩
  have hz' : r a b := hz
  have hab : a ≠ b := by
    rintro rfl
    exact (Std.Irrefl.irrefl (r := r) a) hz'
  rw [mk_fiber]
  rw [Cardinal.mk_insert (by simp [hab]), Cardinal.mk_singleton, one_add_one_eq_two]
