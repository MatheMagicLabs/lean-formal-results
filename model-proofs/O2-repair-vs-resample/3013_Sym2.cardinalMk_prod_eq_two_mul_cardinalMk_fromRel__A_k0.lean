/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
    rw [← mk_fst_out_snd_out z, fromRel_prop] at hz
    exact hz
  have hne : ∀ z ∈ fromRel sym, z.out.1 ≠ z.out.2 := by
    intro z hz h
    have := hr z hz
    rw [h] at this
    exact Std.Irrefl.irrefl _ this
  let e : Bool × fromRel sym ≃ {p : α × α // r p.fst p.snd} := {
    toFun
      | ⟨true, z, hz⟩ => ⟨(z.out.fst, z.out.snd), hr z hz⟩
      | ⟨false, z, hz⟩ => ⟨(z.out.snd, z.out.fst), sym.symm _ _ (hr z hz)⟩
    invFun
      | ⟨(a, b), h⟩ => ⟨s(a, b).out.fst = a, s(a, b), by simpa using h⟩
    left_inv := by grind [mk_fst_out_snd_out]
    right_inv _ := by grind [mk_fst_out_snd_out] }
  simpa using e.cardinal_eq.symm
