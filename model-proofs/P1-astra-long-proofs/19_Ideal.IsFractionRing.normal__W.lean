/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.IsFractionRing.normal
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/Invariant/Galois.lean, line 84
             (added after the model's training data; human proof 32 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma normal : Normal K L := by
  have := Algebra.IsInvariant.isIntegral A B G
  have := isAlgebraic_of_isFractionRing (A ⧸ P) (B ⧸ Q) K L
  constructor
  intro x
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (B ⧸ Q) x
  obtain ⟨b, a, ha, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A ⧸ P) y).exists_smul_eq_mul x hy
  obtain ⟨a, rfl⟩ := Quotient.mk_surjective a
  obtain ⟨b, rfl⟩ := Quotient.mk_surjective b
  simp_rw [← Quotient.algebraMap_eq] at *
  cases nonempty_fintype G
  obtain ⟨p, hp, -, h_monic⟩ := lifts_and_natDegree_eq_and_monic (Algebra.IsInvariant.charpoly_mem_lifts A B G b) (MulSemiringAction.monic_charpoly ..)
  have h_eval : p.aeval b = 0 := by rw [← eval_map_algebraMap, hp, MulSemiringAction.eval_charpoly]
  let q := p.comp (C a * X)
  let d := (algebraMap (B ⧸ Q) L) x / (algebraMap (B ⧸ Q) L) y
  have comm₁ : (algebraMap K L).comp (algebraMap (A ⧸ P) K) = (algebraMap (B ⧸ Q) L).comp (algebraMap (A ⧸ P) (B ⧸ Q)) := by simp_rw [← IsScalarTower.algebraMap_eq]
  have comm₂ : (algebraMap (A ⧸ P) (B ⧸ Q)).comp (algebraMap A (A ⧸ P)) = (algebraMap B (B ⧸ Q)).comp (algebraMap A B) := by simp_rw [← IsScalarTower.algebraMap_eq]
  replace h_eval : ((q.map (algebraMap A (A ⧸ P))).map (algebraMap (A ⧸ P) K)).aeval d = 0 := by { simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, aeval_comp, aeval_mul, aeval_C, aeval_X, ← RingHom.comp_apply, ← RingHom.comp_assoc, comm₁, RingHom.comp_apply, d, mul_div, ← map_mul]; rw [← Algebra.smul_def, h, map_mul, mul_div_cancel_left₀ _ (by simpa using hy), aeval_map_algebraMap, aeval_algebraMap_apply, aeval_map_algebraMap, aeval_algebraMap_apply, h_eval, map_zero, map_zero] }
  have h_splits : (p.map (algebraMap A B)).Splits := by { rw [hp]; exact MulSemiringAction.splits_charpoly G b }
  refine .of_dvd ?_ ?_ (map_dvd (algebraMap K L) (minpoly.dvd K d h_eval))
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X]; refine .comp_of_degree_le_one ?_ (degree_C_mul_X_le _); rw [Polynomial.map_map, Polynomial.map_map, comm₁, RingHom.comp_assoc, comm₂, ← RingHom.comp_assoc, ← Polynomial.map_map]; apply h_splits.map
  · simp_rw [q, map_comp, Polynomial.map_mul, map_C, map_X, Polynomial.map_map]; exact mt (comp_C_mul_X_eq_zero_iff (by simpa)).mp (map_monic_ne_zero h_monic)
