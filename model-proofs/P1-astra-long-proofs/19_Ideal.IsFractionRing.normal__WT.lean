/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.IsFractionRing.normal
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/Invariant/Galois.lean, line 84
             (added after the model's training data; human proof 32 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma normal : Normal K L := by
  classical
  letI := Fintype.ofFinite G
  let f : A →+* K := (algebraMap (A ⧸ P) K).comp (Ideal.Quotient.mk P)
  let g : B →+* L := (algebraMap (B ⧸ Q) L).comp (Ideal.Quotient.mk Q)
  have hcomm : (algebraMap K L).comp f = g.comp (algebraMap A B) := by {
  ext a
  change algebraMap K L (algebraMap (A ⧸ P) K (Ideal.Quotient.mk P a)) = algebraMap (B ⧸ Q) L (Ideal.Quotient.mk Q (algebraMap A B a))
  rw [← IsScalarTower.algebraMap_apply (A ⧸ P) K L, IsScalarTower.algebraMap_apply (A ⧸ P) (B ⧸ Q) L, Ideal.Quotient.algebraMap_mk_of_liesOver]
  }
  have hgen : ∀ x : B ⧸ Q, IsIntegral K (algebraMap (B ⧸ Q) L x) ∧ ((minpoly K (algebraMap (B ⧸ Q) L x)).map (algebraMap K L)).Splits := by {
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change IsIntegral K (g x) ∧ ((minpoly K (g x)).map (algebraMap K L)).Splits
  obtain ⟨p, hp, -, hm⟩ := lifts_and_natDegree_eq_and_monic (Algebra.IsInvariant.charpoly_mem_lifts A B G x) (MulSemiringAction.monic_charpoly G x)
  have hmap : (p.map f).map (algebraMap K L) = (MulSemiringAction.charpoly G x).map g := by {
  rw [Polynomial.map_map, hcomm, ← Polynomial.map_map, hp]
  }
  have heval : aeval (g x) (p.map f) = 0 := by {
  rw [aeval_def, ← eval_map, hmap, eval_map_apply, MulSemiringAction.eval_charpoly, map_zero]
  }
  refine ⟨⟨p.map f, hm.map f, heval⟩, ?_⟩
  have hs := (MulSemiringAction.splits_charpoly G x).map g
  rw [← hmap] at hs
  exact hs.of_dvd ((hm.map f).map (algebraMap K L)).ne_zero (Polynomial.map_dvd (algebraMap K L) (minpoly.dvd K (g x) heval))
  }
  rw [normal_iff]
  intro z
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) z
  refine ⟨?_, ?_⟩
  { simpa only [div_eq_mul_inv] using (hgen x).1.mul (hgen y).1.inv }
  apply IntermediateField.splits_of_mem_adjoin K L (S := Set.range (algebraMap (B ⧸ Q) L)) (fun z hz ↦ by { obtain ⟨a, rfl⟩ := hz; exact hgen a })
  exact (IntermediateField.adjoin K (Set.range (algebraMap (B ⧸ Q) L))).div_mem (IntermediateField.subset_adjoin K _ ⟨x, rfl⟩) (IntermediateField.subset_adjoin K _ ⟨y, rfl⟩)
