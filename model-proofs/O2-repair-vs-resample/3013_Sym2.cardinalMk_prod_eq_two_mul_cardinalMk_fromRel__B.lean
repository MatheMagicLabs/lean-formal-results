/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  rw [← Equiv.sigmaSubtypeFiberEquivSubtype Sym2.mk.uncurry (q := (· ∈ fromRel sym)) (by simp)
    |>.cardinal_eq, Cardinal.mk_sigma, mul_comm, ← Cardinal.sum_const']
  congr 1
  funext y
  obtain ⟨z, hz⟩ := y
  have hd : ¬ z.IsDiag := by
    revert hz
    refine Sym2.ind (fun a b hz hd => ?_) z
    rw [mk_isDiag_iff] at hd
    subst hd
    exact absurd (fromRel_prop.mp hz) (Std.Irrefl.irrefl a)
  have h2 : #(Sym2.mk.uncurry ⁻¹' {z}) = 2 := by
    rw [← Set.cast_ncard (finite_mk_fiber z), ncard_mk_fiber_of_not_isDiag hd]
    simp
  exact h2
