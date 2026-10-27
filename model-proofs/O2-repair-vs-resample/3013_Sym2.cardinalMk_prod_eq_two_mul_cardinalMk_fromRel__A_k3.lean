/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  classical
  have hr : ∀ z ∈ fromRel sym, r z.out.1 z.out.2 := by
    intro z hz
    have h : s(z.out.1, z.out.2) ∈ fromRel sym := by
      rw [mk_fst_out_snd_out]; exact hz
    simpa using h
  let e : Bool × fromRel sym ≃ {p : α × α // r p.1 p.2} :=
    { toFun := fun x => if x.1 then ⟨(x.2.1.out.1, x.2.1.out.2), hr x.2.1 x.2.2⟩
        else ⟨(x.2.1.out.2, x.2.1.out.1), sym.symm _ _ (hr x.2.1 x.2.2)⟩
      invFun := fun p => (decide (s(p.1.1, p.1.2).out.1 = p.1.1),
        ⟨s(p.1.1, p.1.2), by simpa using p.2⟩)
      left_inv := by
        rintro ⟨b, z, hz⟩
        have hr' := hr z hz
        have hs : s(z.out.1, z.out.2) = z := by rw [mk_fst_out_snd_out]
        cases b
        · have hs' : s(z.out.2, z.out.1) = z := by rw [Sym2.eq_swap, mk_fst_out_snd_out]
          have hne : z.out.1 ≠ z.out.2 := by
            intro h
            have := hr'
            rw [h] at this
            exact Std.Irrefl.irrefl _ this
          simp [hs', hne]
        · simp [hs]
      right_inv := by
        rintro ⟨⟨a, b⟩, h⟩
        have h2 : s(s(a, b).out.1, s(a, b).out.2) = s(a, b) := by rw [mk_fst_out_snd_out]
        rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · simp [h3, h4]
        · have hne : b ≠ a := by
            rintro rfl
            exact Std.Irrefl.irrefl _ h
          simp [h3, h4, hne] }
  simpa using e.cardinal_eq.symm
