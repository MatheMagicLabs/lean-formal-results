/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     NoetherNormalization.varChange_leadingCoeff_isUnit
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/NoetherNormalization.lean, line 147
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
lemma varChange_leadingCoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (varChange f f)).leadingCoeff := by
  obtain ⟨v, vin, vs⟩ := Finset.exists_max_image f.support
    (fun v ↦ (varChange f (monomial v (f.coeff v))).degreeOf 0)
    (by
      obtain ⟨d, hd⟩ := MvPolynomial.exists_coeff_ne_zero fne
      exact ⟨d, mem_support_iff.mpr hd⟩)
  have vs' : ∀ x ∈ f.support \ {v},
      (finSuccEquiv k n (varChange f (monomial x (f.coeff x)))).degree <
      (finSuccEquiv k n (varChange f (monomial v (f.coeff v)))).degree := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_sdiff.mp hx
    apply degree_lt_degree
    rw [natDegree_finSuccEquiv, natDegree_finSuccEquiv]
    exact lt_of_le_of_ne (vs x h1)
      (degreeOf_varChange_ne_of_ne _ _ _ h1 vin (Finset.notMem_singleton.mp h2))
  have hc : (finSuccEquiv k n (varChange f (monomial v (f.coeff v) +
      ∑ x ∈ f.support \ {v}, monomial x (f.coeff x)))).leadingCoeff =
      (finSuccEquiv k n (varChange f (monomial v (f.coeff v)))).leadingCoeff := by
    simp only [map_add, map_sum]
    rw [add_comm]
    apply leadingCoeff_add_of_degree_lt <| (lt_of_le_of_lt <| degree_sum_le _ _) ?_
    have h2 : monomial v (f.coeff v) ≠ 0 := by simpa using mem_support_iff.mp vin
    have h3 : (finSuccEquiv k n (varChange f (monomial v (f.coeff v)))) ≠ 0 := fun eq ↦ h2 <|
      (map_eq_zero_iff _ (varChange f).injective).mp
        ((map_eq_zero_iff _ (finSuccEquiv k n).injective).mp eq)
    exact (Finset.sup_lt_iff <| Ne.bot_lt (fun x ↦ h3 <| degree_eq_bot.mp x)).mpr vs'
  have key : f = monomial v (f.coeff v) +
      ∑ x ∈ f.support \ {v}, monomial x (f.coeff x) := by
    conv_lhs => rw [← f.support_sum_monomial_coeff]
    rw [← Finset.add_sum_erase f.support _ vin, Finset.sdiff_singleton_eq_erase]
  have key2 : varChange f f = varChange f (monomial v (f.coeff v) +
      ∑ x ∈ f.support \ {v}, monomial x (f.coeff x)) := congrArg (varChange f) key
  rw [key2, hc, leadingCoeff_finSuccEquiv_varChange]
  exact (mem_support_iff.mp vin).isUnit.map (algebraMap k _)
