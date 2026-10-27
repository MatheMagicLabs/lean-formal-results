/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.turanNumber_eq
Source:      Mathlib @ d0a050ad6, Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean, line 373
             (added after the model's training data; human proof 31 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem turanNumber_eq {n r : ℕ} :
    turanNumber n r = (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  classical
  have top_card : ∀ (m : ℕ) (J : SimpleGraph (Fin m)) [DecidableRel J.Adj], J = ⊤ → #J.edgeFinset = m.choose 2 := by {
  intro m J inst hJ
  subst J
  have hc := card_edgeFinset_top_eq_card_choose_two (V := Fin m)
  rw [Fintype.card_fin] at hc
  simpa only [edgeFinset_card, Fintype.card_eq_nat_card] using hc
  }
  by_cases hr : r = 0
  · { subst r; change #(turanGraph n 0).edgeFinset = _; rw [top_card n _ turanGraph_zero]; simp }
  have hrpos : 0 < r := Nat.pos_of_ne_zero hr
  have aux : ∀ m : ℕ, ∃ k : ℕ, turanNumber m r = k + (m % r).choose 2 ∧ (m ^ 2 - (m % r) ^ 2) * (r - 1) = k * (2 * r) := by {
  intro m
  induction m using Nat.strong_induction_on with | h m ih =>
  by_cases hm : m < r
  · {
  have ht : turanGraph m r = ⊤ := turanGraph_eq_top.mpr (Or.inr hm.le)
  refine ⟨0, ?_, ?_⟩
  · { change #(turanGraph m r).edgeFinset = _; rw [top_card m _ ht]; simp [Nat.mod_eq_of_lt hm] }
  · simp [Nat.mod_eq_of_lt hm]
  }
  · {
  let a := m - r
  have ha : a < m := by dsimp [a]; omega
  have ham : a + r = m := by dsimp [a]; omega
  obtain ⟨k, hk, he⟩ := ih a ha
  have hmod : (a + r) % r = a % r := by simp [Nat.add_mod]
  rw [← ham, hmod, turanNumber_add]
  refine ⟨k + a * (r - 1) + r.choose 2, ?_, ?_⟩
  · omega
  · {
  have hs : (a % r) ^ 2 ≤ a ^ 2 := by simpa only [pow_two] using Nat.mul_self_le_mul_self (Nat.mod_le a r)
  have hp : (a + r) ^ 2 = a ^ 2 + 2 * a * r + r ^ 2 := add_sq a r
  have hd : (a + r) ^ 2 - (a % r) ^ 2 = (a ^ 2 - (a % r) ^ 2) + (2 * a * r + r ^ 2) := by omega
  have hc : r.choose 2 * 2 = r * (r - 1) := by rw [Nat.choose_two_right, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)]
  have hc' : r ^ 2 * (r - 1) = r.choose 2 * (2 * r) := by {
  calc
  r ^ 2 * (r - 1) = (r * (r - 1)) * r := by simp [pow_two, mul_assoc, mul_comm, mul_left_comm]
  _ = r.choose 2 * (2 * r) := by rw [← hc, mul_assoc]
  }
  rw [hd, Nat.add_mul, he, Nat.add_mul, hc']
  simp only [add_mul]
  ac_rfl
  }
  }
  }
  obtain ⟨k, hk, he⟩ := aux n
  rw [he, Nat.mul_div_cancel k (by omega : 0 < 2 * r)]
  exact hk
