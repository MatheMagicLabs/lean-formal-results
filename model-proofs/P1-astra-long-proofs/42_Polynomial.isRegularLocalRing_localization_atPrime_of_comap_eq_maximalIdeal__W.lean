/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/RegularLocalRing/Polynomial.lean, line 35
             (added after the model's training data; human proof 32 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 5 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma Polynomial.isRegularLocalRing_localization_atPrime_of_comap_eq_maximalIdeal
    [IsRegularLocalRing R] (p : Ideal R[X]) [p.IsPrime] (max : p.comap C = maximalIdeal R) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  let q := (maximalIdeal R).map C
  have qle : q ≤ p := by simpa [q, ← max] using map_comap_le
  have reg := (isRegularLocalRing_iff R).mp ‹_›
  have fg' := (maximalIdeal R).fg_of_isNoetherianRing
  have fg := Submodule.FG.finite_generators fg'
  have ht : (maximalIdeal R).height ≤ q.height := le_of_eq (height_map_C (maximalIdeal R)).symm
  by_cases eq : p = q
  · {
  have ht1 : (maximalIdeal R).height ≤ p.height := by simpa [eq];
  have hspan : Ideal.span ((algebraMap R (Localization.AtPrime p)) '' (maximalIdeal R).generators) = maximalIdeal (Localization.AtPrime p) := by {
  rw [IsScalarTower.algebraMap_eq R R[X] (Localization.AtPrime p), RingHom.coe_comp, Set.image_comp, ← Ideal.map_span, ← Ideal.map_span];
  simp only [Ideal.span, (maximalIdeal R).span_generators, algebraMap_eq, q, ← eq, Localization.AtPrime.map_eq_maximalIdeal] };
  simp only [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl, IsLocalization.AtPrime.under_maximalIdeal _ p, ge_iff_le];
  apply le_trans _ (WithBot.coe_le_coe.mpr ht1);
  simp only [maximalIdeal_height_eq_ringKrullDim, ← reg, Nat.cast_le, ← hspan, ← Submodule.FG.generators_ncard fg'];
  exact (Submodule.spanFinrank_span_le_ncard_of_finite (fg.image _)).trans (Set.ncard_image_le fg)
  }
  · {
  have lt : q < p := lt_of_le_of_ne qle (Ne.symm eq);
  have hm : (comap C p).IsMaximal := by simpa [max] using maximalIdeal.isMaximal R;
  obtain ⟨y, _, hy⟩ := Polynomial.exists_monic_span_sup_map_eq R p hm (by simpa [max]);
  have peq : p = Ideal.span (((algebraMap R R[X]) '' (maximalIdeal R).generators) ∪ {y}) := by {
  simp only [Set.union_comm, Ideal.span_union, ← Ideal.map_span, algebraMap_eq, sup_comm];
  nth_rw 1 [hy, max, ← (maximalIdeal R).span_generators] };
  simp only [← Localization.AtPrime.map_eq_maximalIdeal, peq, Ideal.map_span];
  rw [← maximalIdeal_height_eq_ringKrullDim, ← IsLocalization.height_under p.primeCompl, IsLocalization.AtPrime.under_maximalIdeal _ p];
  apply le_trans _ (WithBot.coe_le_coe.mpr (Ideal.height_add_one_le_of_lt_of_isPrime lt));
  apply le_trans _ (WithBot.coe_le_coe.mpr (add_le_add_left ht 1));
  rw [WithBot.coe_add, maximalIdeal_height_eq_ringKrullDim, WithBot.coe_one, ← reg, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le];
  have fin := (fg.image (algebraMap R R[X])).union (Set.finite_singleton y);
  apply le_trans (Submodule.spanFinrank_span_le_ncard_of_finite (fin.image _));
  apply le_trans (Set.ncard_image_le fin) (le_trans (Set.ncard_union_le _ _) _);
  rw [Set.ncard_singleton, add_le_add_iff_right, ← Submodule.FG.generators_ncard fg'];
  exact Set.ncard_image_le fg
  }
