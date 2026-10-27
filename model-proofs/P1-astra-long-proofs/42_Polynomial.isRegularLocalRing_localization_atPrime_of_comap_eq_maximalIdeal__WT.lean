/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/RegularLocalRing/Polynomial.lean, line 35
             (added after the model's training data; human proof 32 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal
    [IsRegularLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  classical
  let m := maximalIdeal R
  let q : Ideal R[X] := m.map C
  have hq : q ≤ p := by
    simpa [q, m, ← max] using (Ideal.map_comap_le (f := C) (K := p))
  have hmap : q.spanFinrank ≤ m.spanFinrank :=
    Ideal.spanFinrank_map_le_of_fg C m.fg_of_isNoetherianRing
  have hdim : (m.spanFinrank : WithBot ℕ∞) = q.height := by
    rw [IsRegularLocalRing.spanFinrank_maximalIdeal]
    rw [show q.height = m.height from Polynomial.height_map_C m]
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
  have hpbound : (p.spanFinrank : WithBot ℕ∞) ≤ p.height := by
    by_cases heq : p = q
    · subst p
      exact (show (q.spanFinrank : WithBot ℕ∞) ≤ m.spanFinrank by
        exact_mod_cast hmap).trans hdim.le
    · have hmax : (p.comap C).IsMaximal := by
        rw [max]
        infer_instance
      obtain ⟨f, hf, hspan⟩ :=
        Polynomial.exists_monic_span_sup_map_eq R p hmax (by simpa [max] using heq)
      have hspan' : p = q ⊔ Ideal.span {f} := by
        simpa [max, q, m] using hspan
      have hsup :
          (q ⊔ Ideal.span {f}).spanFinrank ≤
            q.spanFinrank + (Ideal.span {f}).spanFinrank := by
        have h := Submodule.spanRank_sup_le_sum_spanRank
          (p := q) (q := Ideal.span {f})
        rw [Submodule.FG.spanRank_eq_spanFinrank
              (q ⊔ Ideal.span {f}).fg_of_isNoetherianRing,
            Submodule.FG.spanRank_eq_spanFinrank q.fg_of_isNoetherianRing,
            Submodule.FG.spanRank_eq_spanFinrank
              (Ideal.span {f}).fg_of_isNoetherianRing] at h
        exact_mod_cast h
      have hfbound : (Ideal.span {f}).spanFinrank ≤ 1 := by
        simpa using
          (Submodule.spanFinrank_span_le_ncard_of_finite
            (R := R[X]) (Set.finite_singleton f))
      have hnat : p.spanFinrank ≤ m.spanFinrank + 1 := by
        rw [hspan']
        exact hsup.trans (Nat.add_le_add hmap hfbound)
      have hheight := Ideal.height_add_one_le_of_lt_of_isPrime
        (lt_of_le_of_ne hq (Ne.symm heq))
      calc
        (p.spanFinrank : WithBot ℕ∞) ≤
            (m.spanFinrank : WithBot ℕ∞) + 1 := by exact_mod_cast hnat
        _ = (q.height : WithBot ℕ∞) + 1 := by rw [hdim]
        _ ≤ p.height := by exact_mod_cast hheight
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← Localization.AtPrime.map_eq_maximalIdeal,
    IsLocalization.AtPrime.ringKrullDim_eq_height p]
  exact (show
    ((p.map (algebraMap R[X] (Localization.AtPrime p))).spanFinrank : WithBot ℕ∞) ≤
      p.spanFinrank by
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg
          (algebraMap R[X] (Localization.AtPrime p)) p.fg_of_isNoetherianRing).trans hpbound
