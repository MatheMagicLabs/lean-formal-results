/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Matrix.isIndecomposable_iff_blockTriangular_const
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Block.lean, line 247
             (added after the model's training data; human proof 39 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
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
  · intro hM b hb
    have hlt : ∀ x y : m, ¬ b x < b y := by
      intro x y hxy
      let P := {z : m // b z ≤ b x}
      let Q := {z : m // ¬ b z ≤ b x}
      let e : Fin (card P) ⊕ Fin (card Q) ≃ m :=
        (Equiv.sumCongr (equivFin P).symm (equivFin Q).symm).trans
          (Equiv.sumCompl fun z => b z ≤ b x)
      have hz : ∀ u v, M (e (Sum.inr u)) (e (Sum.inl v)) = 0 := by
        intro u v
        apply hb
        change b ((equivFin P).symm v).val < b ((equivFin Q).symm u).val
        exact lt_of_le_of_lt ((equivFin P).symm v).property
          (lt_of_not_ge ((equivFin Q).symm u).property)
      have he :
          M = (fromBlocks
            (M.submatrix (e ∘ Sum.inl) (e ∘ Sum.inl))
            (M.submatrix (e ∘ Sum.inl) (e ∘ Sum.inr))
            0
            (M.submatrix (e ∘ Sum.inr) (e ∘ Sum.inr))).reindex e e := by
        ext u v
        obtain ⟨u, rfl⟩ := e.surjective u
        obtain ⟨v, rfl⟩ := e.surjective v
        cases u <;> cases v <;>
          simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply,
            fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
            fromBlocks_apply₂₂, Function.comp_apply, zero_apply] <;>
          first | rfl | exact hz _ _
      rcases hM _ _ _ _ _ e he with hp | hq
      · have hp' : 0 < card P := card_pos_iff.mpr ⟨⟨x, le_rfl⟩⟩
        exact (Nat.ne_of_gt hp') hp
      · have hq' : 0 < card Q := card_pos_iff.mpr ⟨⟨y, not_le_of_gt hxy⟩⟩
        exact (Nat.ne_of_gt hq') hq
    cases isEmpty_or_nonempty m with
    | inl hm =>
      exact ⟨Classical.choice (inferInstance : Nonempty α),
        funext fun x => isEmptyElim x⟩
    | inr hm =>
      let x : m := Classical.choice hm
      refine ⟨b x, funext fun y => ?_⟩
      exact le_antisymm (le_of_not_gt (hlt x y)) (le_of_not_gt (hlt y x))
  · intro h i j A B D e hM
    by_cases hi : i = 0
    · exact Or.inl hi
    by_cases hj : j = 0
    · exact Or.inr hj
    exfalso
    obtain ⟨a, c, hac⟩ := exists_pair_lt α
    let b : m → α := fun x => Sum.elim (fun _ => a) (fun _ => c) (e.symm x)
    have hb : M.BlockTriangular b := by
      intro u v huv
      obtain ⟨u, rfl⟩ := e.surjective u
      obtain ⟨v, rfl⟩ := e.surjective v
      cases u with
      | inl u =>
        cases v with
        | inl v =>
          simp [b] at huv
        | inr v =>
          have hca : c < a := by simpa [b] using huv
          exact False.elim ((not_lt_of_ge hac.le) hca)
      | inr u =>
        cases v with
        | inl v =>
          simp [hM, reindex_apply, submatrix_apply]
        | inr v =>
          simp [b] at huv
    obtain ⟨d, hd⟩ := h b hb
    have ha : a = d := by
      simpa [b, Function.const] using
        congrFun hd (e (Sum.inl ⟨0, Nat.pos_of_ne_zero hi⟩))
    have hc : c = d := by
      simpa [b, Function.const] using
        congrFun hd (e (Sum.inr ⟨0, Nat.pos_of_ne_zero hj⟩))
    exact (ne_of_lt hac) (ha.trans hc.symm)
