/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     String.lt_iff_ltb
Source:      Mathlib @ d0a050ad6, Mathlib/Data/String/Basic.lean, line 88
             (added after the model's training data; human proof 32 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 5 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem lt_iff_ltb {s₁ s₂ : String} :
    s₁ < s₂ ↔ ltb (String.Legacy.iter s₁) (String.Legacy.iter s₂) := by
  have hp (c : Char) : 0 < c.utf8Size := by unfold Char.utf8Size; dsimp only; split_ifs <;> decide
  have hg (c : Char) (cs : List Char) : Pos.Raw.get (ofList (c :: cs)) 0 = c := by simp [Pos.Raw.get, Pos.Raw.utf8GetAux, -ofList_cons]
  suffices h : ∀ l₁ l₂ : List Char, l₁ < l₂ ↔ ltb ⟨ofList l₁, 0⟩ ⟨ofList l₂, 0⟩ by simpa [lt_iff_toList_lt, Legacy.iter, Legacy.mkIterator] using h s₁.toList s₂.toList
  intro l₁
  induction l₁ with
  | nil => intro l₂; cases l₂ <;> rw [ltb] <;> simp [Legacy.Iterator.hasNext, hp]
  | cons a l₁ ih => intro l₂; cases l₂ with
  | nil => rw [ltb]; simp [Legacy.Iterator.hasNext]
  | cons b l₂ => by_cases hab : a = b <;> rw [ltb] <;> simp only [Legacy.Iterator.curr, Legacy.Iterator.next, Pos.Raw.next, hg, hab, ltb_cons_addChar] <;> simp [Legacy.Iterator.hasNext, hp, hab, ← ih]; exact ⟨(by intro h; cases h with | rel h => exact h | cons h => exact (hab rfl).elim), fun h => List.Lex.rel h⟩
