/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ
Source:      Mathlib @ d0a050ad6, Mathlib/Algebra/Homology/Embedding/Connect.lean, line 237 (group DRIFT)
Experiment:  UE1-deepseek-8-samples, arm sample 4, single attempt
Prover:      DeepSeek-Prover-V2-7B (4-bit)
Setup:       DeepSeek-Prover-V2-7B (4-bit, local), 8 independent samples per theorem, no Lean feedback;
             160 theorems: 80 DRIFT (human proof cites a lemma added after the 2025-05 snapshot) and 80 STABLE
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

-- (context: the Mathlib file above this declaration)
lemma homologyMap_map_of_eq_neg_succ (n : ℕ) [NeZero n] (m : ℤ) (hmn : m = -↑(n + 1))
    [HasHomology h.cochainComplex m] [HasHomology K n]
    [HasHomology h'.cochainComplex m] [HasHomology K' n] :
    homologyMap (h.map h' fK fL f_comm) m =
      (h.homologyIsoNeg n m hmn).hom ≫ homologyMap fK n ≫ (h'.homologyIsoNeg n m hmn).inv := by
  rw [← cancel_mono (HomologicalComplex.homologyι ..)]
  dsimp [homologyIsoNeg]
  simp only [homologyι_naturality, Category.assoc, restrictionHomologyIso_hom_homologyι,
    homologyι_naturality_assoc, restrictionHomologyIso_inv_homologyι_assoc]
  congr 1
  rw [← cancel_epi (HomologicalComplex.pOpcycles ..)]
  subst hmn
  simp
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
  <;> aesop_cat
