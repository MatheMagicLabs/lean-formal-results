/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 3, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  let f : { p : α × α // r p.fst p.snd } → Bool × fromRel sym := fun p =>
    (decide (s(p.1.1, p.1.2).out.1 = p.1.1), ⟨s(p.1.1, p.1.2), by simpa using p.2⟩)
  have hf : Function.Injective f := by
    rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun x => (x.2 : Sym2 α)) h
    simp only [f, decide_eq_decide] at h1 h2
    rw [← h2] at h1
    have hz : s((s(a, b)).out.1, (s(a, b)).out.2) = s(a, b) := by
      first
        | exact mk_fst_out_snd_out _
        | exact Quot.out_eq _
        | simp [mk_fst_out_snd_out]
    have hz' := Sym2.eq_iff.mp hz
    rcases Sym2.eq_iff.mp h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · subst h3 h4
      rfl
    · subst h3 h4
      have hab' : a = b := by
        rcases hz' with ⟨e1, -⟩ | ⟨e1, -⟩
        · first | grind | simp_all
        · first | grind | simp_all
      subst hab'
      rfl
  simpa using Cardinal.mk_le_of_injective hf
