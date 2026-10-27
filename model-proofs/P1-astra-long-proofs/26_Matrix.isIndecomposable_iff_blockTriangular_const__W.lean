/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.isIndecomposable_iff_blockTriangular_const
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Block.lean, line 247
             (added after the model's training data; human proof 39 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma isIndecomposable_iff_blockTriangular_const [Nontrivial α] [Finite m] [Zero R]
    (M : Matrix m m R) :
    M.IsIndecomposable ↔ ∀ b : m → α, M.BlockTriangular b → ∃ a, b = const m a := by
  classical
  letI := Fintype.ofFinite m
  constructor
  · intro h b ht; have hn : ∀ x y : m, ¬ b x < b y := (by intro x y hxy; let S := {z : m // b z ≤ b x}; let T := {z : m // ¬ b z ≤ b x}; let f := (Fintype.equivFin S).symm; let g := (Fintype.equivFin T).symm; let q : S ⊕ T ≃ m := { toFun := Sum.elim Subtype.val Subtype.val, invFun := fun z => if hz : b z ≤ b x then Sum.inl ⟨z, hz⟩ else Sum.inr ⟨z, hz⟩, left_inv := by rintro (⟨z, hz⟩ | ⟨z, hz⟩) <;> simp [hz], right_inv := by intro z; dsimp; split <;> rfl }; let e := (Equiv.sumCongr f g).trans q; let A : Matrix (Fin (Fintype.card S)) (Fin (Fintype.card S)) R := fun k l => M (e (Sum.inl k)) (e (Sum.inl l)); let B : Matrix (Fin (Fintype.card S)) (Fin (Fintype.card T)) R := fun k l => M (e (Sum.inl k)) (e (Sum.inr l)); let D : Matrix (Fin (Fintype.card T)) (Fin (Fintype.card T)) R := fun k l => M (e (Sum.inr k)) (e (Sum.inr l)); have hz : ∀ k l, M (e (Sum.inr k)) (e (Sum.inl l)) = 0 := (by intro k l; apply ht; exact lt_of_le_of_lt (f l).property (lt_of_not_ge (g k).property)); have he : M = (fromBlocks A B 0 D).reindex e e := (by ext r s; obtain ⟨r, rfl⟩ := e.surjective r; obtain ⟨s, rfl⟩ := e.surjective s; cases r <;> cases s <;> simp [Matrix.reindex_apply, Matrix.fromBlocks, A, B, D, hz]); have hs : 0 < Fintype.card S := Fintype.card_pos_iff.mpr ⟨⟨x, le_rfl⟩⟩; have ht' : 0 < Fintype.card T := Fintype.card_pos_iff.mpr ⟨⟨y, not_le_of_gt hxy⟩⟩; exact (h _ _ A B D e he).elim (fun hc => (Nat.ne_of_gt hs) hc) (fun hc => (Nat.ne_of_gt ht') hc)); exact Classical.byCases (fun hm : Nonempty m => (by let x := Classical.choice hm; refine ⟨b x, funext fun y => ?_⟩; exact le_antisymm (le_of_not_gt (hn x y)) (le_of_not_gt (hn y x)))) (fun hm => ⟨Classical.choice (inferInstance : Nonempty α), funext fun y => False.elim (hm ⟨y⟩)⟩)
  · intro h i j A B D e hM; by_contra hzero; have hi : i ≠ 0 := fun hi => hzero (Or.inl hi); have hj : j ≠ 0 := fun hj => hzero (Or.inr hj); obtain ⟨a, c, hac⟩ : ∃ a c : α, a < c := (by obtain ⟨a, c, hac⟩ := exists_pair_ne α; exact (lt_or_gt_of_ne hac).elim (fun h => ⟨a, c, h⟩) (fun h => ⟨c, a, h⟩)); have hca : ¬ c < a := not_lt_of_ge (le_of_lt hac); let b : m → α := fun k => Sum.elim (fun _ => a) (fun _ => c) (e.symm k); have ht : M.BlockTriangular b := (by intro r s hrs; rw [hM]; obtain ⟨r, rfl⟩ := e.surjective r; obtain ⟨s, rfl⟩ := e.surjective s; cases r <;> cases s <;> simp_all [b, Matrix.reindex_apply, Matrix.fromBlocks] <;> exact False.elim ((not_lt_of_ge (le_of_lt hac)) hrs)); obtain ⟨d, hb⟩ := h b ht; have h₁ := congr_fun hb (e (Sum.inl (⟨0, Nat.pos_of_ne_zero hi⟩ : Fin i))); have h₂ := congr_fun hb (e (Sum.inr (⟨0, Nat.pos_of_ne_zero hj⟩ : Fin j))); have heq : a = c := (by simpa [b, Function.const] using h₁.trans h₂.symm); exact (ne_of_lt hac) heq
