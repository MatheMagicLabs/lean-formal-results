/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SSet.prodStdSimplex.exists_nonDegenerate_max_dim_aux
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean, line 204
             (added after the model's training data; human proof 26 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

private lemma exists_nonDegenerate_max_dim_aux {d : ℕ}
    (x : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate d) (hd : d < p + q) :
    ∃ (y : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (d + 1)),
      x.1 ∈ (Subcomplex.ofSimplex y.1).obj _ := by
  let f := objEquiv x.1
  let s : Fin (d + 1) → ℕ := fun i ↦ (f i).1.val + (f i).2.val
  have hf : StrictMono f := (nonDegenerate_iff_strictMono_objEquiv x.1).1 x.2
  have extend (i : Fin (d + 2)) (a : Fin (p + 1) × Fin (q + 1)) (ha : StrictMono (Fin.insertNth i a f)) : ∃ (y : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (d + 1)), x.1 ∈ (Subcomplex.ofSimplex y.1).obj _ := by
  { let g : Fin (d + 2) →o Fin (p + 1) × Fin (q + 1) := ⟨Fin.insertNth i a f, ha.monotone⟩
  ; have hg : objEquiv.{u}.symm g ∈ (Δ[p] ⊗ Δ[q]).nonDegenerate (d + 1) := (nonDegenerate_iff_strictMono_objEquiv _).2 ha
  ; refine ⟨⟨objEquiv.symm g, hg⟩, ?_⟩
  ; rw [← Subcomplex.ofSimplex_le_iff]
  ; apply (ofSimplex_le_ofSimplex_iff _ _).2
  ; rintro _ ⟨j, rfl⟩
  ; exact ⟨i.succAbove j, by simp [g, f]⟩ }
  by_cases h₀ : 0 < s 0
  · exact extend 0 (0, 0) (Fin.strictMono_insertNth_zero hf _ ((Fin.prod_zero_zero_lt_iff _).2 h₀))
  by_cases hlast : s (Fin.last d) < p + q
  · exact extend (Fin.last (d + 1)) (Fin.last p, Fin.last q) (Fin.strictMono_insertNth_last hf _ ((Fin.prod_lt_last_last_iff _).2 hlast))
  have hgap : ∃ i : Fin d, s i.castSucc + 2 ≤ s i.succ := by
  { by_contra h
  ; push_neg at h
  ; have hs : ∀ i : Fin (d + 1), s i ≤ i.val := by
  { intro i
  ; induction i using Fin.induction with
  | zero => omega
  | succ i hi => have hstep := h i; simp only [Fin.val_castSucc, Fin.val_succ] at hi ⊢; omega }
  ; have hend := hs (Fin.last d)
  ; simp only [Fin.val_last] at hend
  ; omega }
  obtain ⟨i, hi⟩ := hgap
  obtain ⟨a, ha₁, ha₂⟩ := Fin.prod_exists_lt_lt_of_le_of_le (f i.castSucc) (f i.succ) (hf.monotone i.castSucc_le_succ) hi
  exact extend i.castSucc.succ a (Fin.strictMono_insertNth hf i a ha₁ ha₂)
