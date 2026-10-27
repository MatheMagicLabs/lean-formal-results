/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  have h : ∀ z : fromRel sym, #{p : α × α // Sym2.mk.uncurry p = z.1} = 2 := by
    rintro ⟨z, hz⟩
    have hnd : ¬ z.IsDiag := by
      induction z using Sym2.ind with
      | _ x y =>
        intro hd
        rw [mk_isDiag_iff] at hd
        subst hd
        exact Std.Irrefl.irrefl x (by simpa using hz)
    show #(Sym2.mk.uncurry ⁻¹' {z} : Set (α × α)) = 2
    rw [← Set.cast_ncard (finite_mk_fiber z), ncard_mk_fiber_of_not_isDiag hnd]
    simp
  rw [← Equiv.sigmaSubtypeFiberEquivSubtype Sym2.mk.uncurry (q := (· ∈ fromRel sym)) (by simp)
    |>.cardinal_eq, Cardinal.mk_sigma]
  simp only [h]
  rw [Cardinal.sum_const', mul_comm]
