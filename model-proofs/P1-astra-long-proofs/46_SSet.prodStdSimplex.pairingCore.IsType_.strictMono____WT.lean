/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SSet.prodStdSimplex.pairingCore.IsType₂.strictMono_φ
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/SimplicialSet/AnodyneExtensions/UnionProd.lean, line 342
             (added after the model's training data; human proof 34 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma strictMono_φ : StrictMono (φ x hd) := by
  classical
  let f := objEquiv (x.cast hd).simplex
  let v : Fin (m + 2) × Fin (n + 1) :=
  (k.castSucc, (x.cast hd).simplex.2 (min x hd))
  have hf : StrictMono f :=
  (nonDegenerate_iff_strictMono_objEquiv _).1 (x.cast hd).nonDegenerate
  have hleft : ∀ i, i < min x hd → f i < v := by
  {
  intro i hi
  have hle : f i ≤ v :=
  ⟨(pairingCore.simplex_fst_le_castSucc_iff x hd i).2 hi,
  stdSimplex.monotone_apply _ hi.le⟩
  apply lt_of_le_of_ne hle
  intro heq
  obtain ⟨j, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hi)
  have hmin : min x hd = j.succ := by
  {
  have hn : ¬ j.succ < min x hd := by
  {
  intro hj
  have hle' : f j.succ ≤ v :=
  ⟨(pairingCore.simplex_fst_le_castSucc_iff x hd j.succ).2 hj,
  stdSimplex.monotone_apply _ hj.le⟩
  rw [← heq] at hle'
  exact (not_le_of_gt (hf j.castSucc_lt_succ)) hle'
  }
  apply Fin.ext
  have := Fin.lt_def.mp hi
  have := Fin.le_def.mp (le_of_not_gt hn)
  simp only [Fin.val_castSucc, Fin.val_succ] at *
  omega
  }
  apply hx d hd j.succ
  rw [isIndex_succ]
  refine ⟨congrArg Prod.fst heq, ?_, ?_⟩
  { simpa only [hmin] using! simplex_fst_min x hd }
  {
  have hs : (x.cast hd).simplex.2 j.castSucc =
  (x.cast hd).simplex.2 (min x hd) := congrArg Prod.snd heq
  rw [hmin] at hs
  exact hs.symm
  }
  }
  have hright : ∀ i, min x hd ≤ i → v < f i := by
  {
  intro i hi
  apply lt_of_lt_of_le (b := f (min x hd))
  {
  apply lt_of_le_of_ne
  {
  change k.castSucc ≤ (x.cast hd).simplex.1 (min x hd) ∧
  (x.cast hd).simplex.2 (min x hd) ≤ (x.cast hd).simplex.2 (min x hd)
  rw [simplex_fst_min]
  exact ⟨k.castSucc_le_succ, le_rfl⟩
  }
  {
  intro h
  have h' := congrArg Prod.fst h
  change k.castSucc = (x.cast hd).simplex.1 (min x hd) at h'
  rw [simplex_fst_min] at h'
  exact (ne_of_lt k.castSucc_lt_succ) h'
  }
  }
  { exact hf.monotone hi }
  }
  intro a b hab
  obtain rfl | ⟨a, rfl⟩ := Fin.eq_self_or_eq_succAbove (min x hd).castSucc a
  {
  obtain rfl | ⟨b, rfl⟩ := Fin.eq_self_or_eq_succAbove (min x hd).castSucc b
  { exact (lt_irrefl _ hab).elim }
  {
  rw [φ_castSucc, φ_succAbove]
  apply hright
  simpa only [Fin.lt_succAbove_iff_le_castSucc,
  Fin.castSucc_le_castSucc_iff] using hab
  }
  }
  {
  obtain rfl | ⟨b, rfl⟩ := Fin.eq_self_or_eq_succAbove (min x hd).castSucc b
  {
  rw [φ_succAbove, φ_castSucc]
  apply hleft
  simpa only [Fin.succAbove_lt_iff_castSucc_lt,
  Fin.castSucc_lt_castSucc_iff] using hab
  }
  {
  rw [φ_succAbove, φ_succAbove]
  exact hf ((Fin.strictMono_succAbove _).lt_iff_lt.mp hab)
  }
  }
