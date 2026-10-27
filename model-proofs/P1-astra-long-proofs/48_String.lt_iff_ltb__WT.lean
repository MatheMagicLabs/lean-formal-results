/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     String.lt_iff_ltb
Source:      Mathlib @ d0a050ad6, Mathlib/Data/String/Basic.lean, line 88
             (added after the model's training data; human proof 32 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 6 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem lt_iff_ltb {s₁ s₂ : String} :
    s₁ < s₂ ↔ ltb (String.Legacy.iter s₁) (String.Legacy.iter s₂) := by
  have hp (c : Char) : 0 < c.utf8Size := by {
  unfold Char.utf8Size
  dsimp only
  split_ifs <;> decide
  }
  have hn (c : Char) (l : List Char) : (Legacy.iter (ofList (c :: l))).hasNext = true := by {
  simp [Legacy.iter, Legacy.mkIterator, Legacy.Iterator.hasNext, -ofList_cons, hp]
  }
  have hc (c : Char) (l : List Char) : (Legacy.iter (ofList (c :: l))).curr = c := by {
  simp [Legacy.iter, Legacy.mkIterator, Legacy.Iterator.curr, Pos.Raw.get, Pos.Raw.utf8GetAux, -ofList_cons]
  }
  have ht (c : Char) (l : List Char) : (Legacy.iter (ofList (c :: l))).next = ⟨ofList (c :: l), (0 : Pos.Raw) + c⟩ := by {
  have h := hc c l
  change Pos.Raw.get (ofList (c :: l)) 0 = c at h
  simp only [Legacy.iter, Legacy.mkIterator, Legacy.Iterator.next, Pos.Raw.next, h]
  }
  suffices H : ∀ l₁ l₂ : List Char, List.Lex (· < ·) l₁ l₂ ↔ ltb (Legacy.iter (ofList l₁)) (Legacy.iter (ofList l₂)) by { simpa [lt_iff_toList_lt] using H s₁.toList s₂.toList }
  intro l₁
  induction l₁ with
  | nil => {
  intro l₂
  cases l₂ with
  | nil => simp [ltb, Legacy.iter, Legacy.mkIterator, Legacy.Iterator.hasNext]
  | cons b l₂ => simp [ltb, hn, Legacy.iter, Legacy.mkIterator, Legacy.Iterator.hasNext, hp]
  }
  | cons a l₁ ih => {
  intro l₂
  cases l₂ with
  | nil => simp [ltb, Legacy.iter, Legacy.mkIterator, Legacy.Iterator.hasNext]
  | cons b l₂ => {
  rw [ltb]
  simp only [hn, Bool.true_eq, ↓reduceIte, hc]
  by_cases h : a = b
  · {
  subst b
  simp only [↓reduceIte, ht, ltb_cons_addChar]
  exact List.lex_cons_iff.trans (ih l₂)
  }
  · {
  simp only [h, ↓reduceIte, Bool.decide_eq_true]
  constructor
  · {
  intro hlex
  cases hlex with
  | rel hab => simpa using hab
  | cons _ => exact (h rfl).elim
  }
  · {
  intro hab
  apply List.Lex.rel
  simpa using hab
  }
  }
  }
  }
