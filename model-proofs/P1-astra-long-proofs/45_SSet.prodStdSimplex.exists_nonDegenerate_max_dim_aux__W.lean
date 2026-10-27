/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SSet.prodStdSimplex.exists_nonDegenerate_max_dim_aux
Source:      Mathlib @ d0a050ad6, Mathlib/AlgebraicTopology/SimplicialSet/ProdStdSimplex.lean, line 204
             (added after the model's training data; human proof 26 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 6 call(s)
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
  classical
  let f := objEquiv x.1
  let s : Fin (p + 1) × Fin (q + 1) → ℕ := fun a ↦ (a.1 : ℕ) + a.2
  have hf : StrictMono f := (nonDegenerate_iff_strictMono_objEquiv x.1).1 x.2
  have hlt {a b : Fin (p + 1) × Fin (q + 1)} (hab : a ≤ b) (hs : s a < s b) : a < b := by { apply lt_of_le_of_ne hab; intro h; have he := congrArg s h; omega }
  have bump (a b : Fin (p + 1) × Fin (q + 1)) (hab : a ≤ b) (hs : s a < s b) : ∃ c, a < c ∧ c ≤ b ∧ s c = s a + 1 := by { obtain ⟨h₁, h₂⟩ := hab; exact if h : a.1 < b.1 then (by { let c : Fin (p + 1) × Fin (q + 1) := (⟨a.1.val + 1, by { have := b.1.isLt; omega }⟩, a.2); refine ⟨c, hlt ⟨by { change a.1.val ≤ a.1.val + 1; omega }, le_rfl⟩ (by { dsimp [s, c]; omega }), ⟨by { change a.1.val + 1 ≤ b.1.val; omega }, h₂⟩, ?_⟩; dsimp [s, c]; omega }) else (by { have h' : a.2 < b.2 := by { dsimp [s] at hs; omega }; let c : Fin (p + 1) × Fin (q + 1) := (a.1, ⟨a.2.val + 1, by { have := b.2.isLt; omega }⟩); refine ⟨c, hlt ⟨le_rfl, by { change a.2.val ≤ a.2.val + 1; omega }⟩ (by { dsimp [s, c]; omega }), ⟨h₁, by { change a.2.val + 1 ≤ b.2.val; omega }⟩, ?_⟩; dsimp [s, c]; omega }) }
  have extend (k : ℕ) (hk : k ≤ d + 1) (a : Fin (p + 1) × Fin (q + 1)) (hl : ∀ j : Fin (d + 1), j.val < k → f j < a) (hr : ∀ j : Fin (d + 1), k ≤ j.val → a < f j) : ∃ y : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (d + 1), x.1 ∈ (Subcomplex.ofSimplex y.1).obj _ := by {
  let g : Fin (d + 2) → Fin (p + 1) × Fin (q + 1) := fun j ↦ if h : j.val < k then f ⟨j.val, by omega⟩ else if h' : j.val = k then a else f ⟨j.val - 1, by { have := j.isLt; omega }⟩;
  have hg : StrictMono g := by { intro i j hij; have hij' : i.val < j.val := hij; dsimp only [g]; split_ifs <;> (first | omega | (apply hf; change (↑_ : ℕ) < ↑_; try dsimp only; omega) | (apply hl; try dsimp only; omega) | (apply hr; try dsimp only; omega)) };
  let y : (Δ[p] ⊗ Δ[q] : SSet.{u}).nonDegenerate (d + 1) := ⟨objEquiv.symm ⟨g, hg.monotone⟩, (nonDegenerate_iff_strictMono_objEquiv _).2 (by { change StrictMono g; exact hg })⟩;
  refine ⟨y, ?_⟩;
  have hxy : Subcomplex.ofSimplex x.1 ≤ Subcomplex.ofSimplex y.1 := (ofSimplex_le_ofSimplex_iff _ _).2 (by { change Set.range f ⊆ Set.range g; rintro _ ⟨i, rfl⟩; exact if hi : i.val < k then ⟨⟨i.val, by omega⟩, by { simp only [g, dif_pos hi] }⟩ else (by { have h₁ : ¬ i.val + 1 < k := by { omega }; have h₂ : ¬ i.val + 1 = k := by { omega }; exact ⟨⟨i.val + 1, by omega⟩, by { simp only [g, dif_neg h₁, dif_neg h₂]; apply congrArg f; apply Fin.ext; simp }⟩ }) });
  exact hxy _ ⟨𝟙 _, by { simp; rfl }⟩ }
  by_cases hz : s (f 0) = 0
  swap
  · have ha : (0, 0) < f 0 := hlt ⟨Fin.zero_le _, Fin.zero_le _⟩ (by { simpa [s] using Nat.pos_of_ne_zero hz }); exact extend 0 (by omega) (0, 0) (fun j hj ↦ by omega) (fun j _ ↦ lt_of_lt_of_le ha (hf.monotone (Fin.zero_le j)))
  by_cases ht : s (f (Fin.last d)) = p + q
  swap
  · have hs : s (f (Fin.last d)) < s (Fin.last p, Fin.last q) := by { have h₁ := (f (Fin.last d)).1.isLt; have h₂ := (f (Fin.last d)).2.isLt; dsimp [s] at ht ⊢; omega }; obtain ⟨a, ha, _, _⟩ := bump (f (Fin.last d)) (Fin.last p, Fin.last q) ⟨Fin.le_last _, Fin.le_last _⟩ hs; exact extend (d + 1) le_rfl a (fun j _ ↦ lt_of_le_of_lt (hf.monotone (Fin.le_last j)) ha) (fun j hj ↦ by { have := j.isLt; omega })
  have hgap : ∃ i : Fin d, s (f i.castSucc) + 1 < s (f i.succ) := by {
  by_contra hn;
  have hstep (i : Fin d) : s (f i.succ) ≤ s (f i.castSucc) + 1 := by { have h : ¬ s (f i.castSucc) + 1 < s (f i.succ) := fun h ↦ hn ⟨i, h⟩; omega };
  have hb (i : Fin (d + 1)) : s (f i) ≤ i.val := by { induction i using Fin.induction with | zero => simpa using le_of_eq hz | succ i hi => have := hstep i; simp only [Fin.val_castSucc, Fin.val_succ] at *; omega };
  have hb' := hb (Fin.last d);
  simp only [Fin.val_last] at hb';
  omega }
  obtain ⟨i, hi⟩ := hgap
  obtain ⟨a, ha, hb, hs⟩ := bump (f i.castSucc) (f i.succ) (hf.monotone i.castSucc_le_succ) (by omega)
  have ha' : a < f i.succ := hlt hb (by omega)
  exact extend (i.val + 1) (by { have := i.isLt; omega }) a (fun j hj ↦ lt_of_le_of_lt (hf.monotone (by { change j.val ≤ i.val; omega })) ha) (fun j hj ↦ lt_of_lt_of_le ha' (hf.monotone (by { change i.val + 1 ≤ j.val; omega })))
