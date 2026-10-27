/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.turanNumber_eq
Source:      Mathlib @ d0a050ad6, Mathlib/Combinatorics/SimpleGraph/Extremal/Turan.lean, line 373
             (added after the model's training data; human proof 31 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem turanNumber_eq {n r : ℕ} :
    turanNumber n r = (n ^ 2 - (n % r) ^ 2) * (r - 1) / (2 * r) + (n % r).choose 2 := by
  classical
  have choose_double (k : ℕ) : 2 * k.choose 2 = k * (k - 1) := by
  { rw [Nat.choose_two_right, mul_comm 2,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self k)] }
  have base (k : ℕ) (hk : r = 0 ∨ k ≤ r) :
      turanNumber k r = k.choose 2 := by
  { have hg : turanGraph k r = ⊤ := by
    { rcases hk with hr | hk
      · subst r; simp
      · ext v w
        change (v.val % r ≠ w.val % r) ↔ v ≠ w
        rw [Nat.mod_eq_of_lt (v.isLt.trans_le hk),
          Nat.mod_eq_of_lt (w.isLt.trans_le hk)]
        exact ⟨fun h e => h (congrArg Fin.val e), fun h e => h (Fin.ext e)⟩ }
    have hv (v : Fin k) : (turanGraph k r).degree v = k - 1 := by
    { have hn : (turanGraph k r).neighborFinset v = univ.erase v := by
      { ext w
        simp only [mem_neighborFinset, mem_erase, mem_univ, and_true]
        rw [hg]
        change (v ≠ w) ↔ w ≠ v
        exact ne_comm }
      change #((turanGraph k r).neighborFinset v) = k - 1
      rw [hn]
      simp }
    have hd : (∑ v : Fin k, (turanGraph k r).degree v) =
        2 * turanNumber k r :=
      (turanGraph k r).sum_degrees_eq_twice_card_edges
    simp only [hv, sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hd
    have hc := choose_double k
    omega }
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst r
    simpa using base n (Or.inl rfl)
  · have identity (k : ℕ) :
        2 * r * turanNumber k r + (k % r) ^ 2 * (r - 1) =
          k ^ 2 * (r - 1) + 2 * r * (k % r).choose 2 := by
    { induction k using Nat.strong_induction_on with
      | h k ih =>
        by_cases hk : k < r
        · rw [Nat.mod_eq_of_lt hk, base k (Or.inr hk.le)]
          exact add_comm _ _
        · have hle : r ≤ k := Nat.le_of_not_gt hk
          have hlt : k - r < k := by omega
          have hi := ih (k - r) hlt
          have he : k - r + r = k := Nat.sub_add_cancel hle
          have hm : (k - r) % r = k % r := by
          { conv_rhs => rw [← he]
            simp }
          rw [hm] at hi
          have ht := turanNumber_add (n := k - r) (r := r)
          rw [he] at ht
          have hc := congrArg (fun x : ℕ => r * x) (choose_double r)
          have hp : r - 1 + 1 = r := by omega
          grind }
    let a := (n ^ 2 - (n % r) ^ 2) * (r - 1)
    let d := 2 * r
    let c := (n % r).choose 2
    have hd : 0 < d := by dsimp [d]; omega
    have hm : n % r ≤ n := Nat.mod_le n r
    have hs : (n % r) ^ 2 ≤ n ^ 2 := by
    { simpa only [pow_two] using Nat.mul_le_mul hm hm }
    have he := congrArg (fun x : ℕ => x * (r - 1)) (Nat.sub_add_cancel hs)
    have hi := identity n
    have ha : a + d * c = d * turanNumber n r := by
    { dsimp [a, d, c]; grind }
    have hdiv := Nat.mod_add_div a d
    have hmod := Nat.mod_lt a hd
    change turanNumber n r = a / d + c
    apply Nat.le_antisymm
    · by_contra! h
      have hh := Nat.mul_le_mul_left d (show a / d + c + 1 ≤ turanNumber n r from h)
      simp only [Nat.mul_add, Nat.mul_one] at hh
      omega
    · by_contra! h
      have hh := Nat.mul_le_mul_left d (show turanNumber n r + 1 ≤ a / d + c from h)
      simp only [Nat.mul_add, Nat.mul_one] at hh
      omega
