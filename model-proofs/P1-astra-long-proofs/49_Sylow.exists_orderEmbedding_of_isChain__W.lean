/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sylow.exists_orderEmbedding_of_isChain
Source:      Mathlib @ d0a050ad6, Mathlib/GroupTheory/Sylow.lean, line 724
             (added after the model's training data; human proof 35 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 2 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem exists_orderEmbedding_of_isChain [Finite G] {p n : ℕ} (hp : p.Prime)
    (hdvd : p ^ n ∣ Nat.card G) {s : Set (Subgroup G)} (hchain : IsChain (· ≤ ·) s)
    (hcard : ∀ H ∈ s, Nat.card H ∣ p ^ n) :
    ∃ f : Fin (n + 1) ↪o Subgroup G, s ⊆ Set.range f ∧ ∀ k, Nat.card (f k) = p ^ k.val := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  induction n generalizing G with
  | zero => {
  let f : Fin 1 ↪o Subgroup G := OrderEmbedding.ofStrictMono (fun _ => ⊥) (by {
  intro a b hab
  have he : a = b := Subsingleton.elim _ _
  subst b
  exact (lt_irrefl _ hab).elim
  })
  refine ⟨f, ?_, ?_⟩
  · {
  intro H hHs
  have hH : Nat.card H = 1 := Nat.dvd_one.mp (by simpa using hcard H hHs)
  refine ⟨0, ?_⟩
  change (⊥ : Subgroup G) = H
  apply Subgroup.eq_of_le_of_card_ge bot_le
  simpa only [Subgroup.card_bot] using hH.le
  }
  · {
  intro k
  have hk : k.val = 0 := by omega
  change Nat.card (⊥ : Subgroup G) = p ^ k.val
  simp [hk]
  }
  }
  | succ n ih => {
  have htotal : ∀ A ∈ s, ∀ B ∈ s, A ≤ B ∨ B ≤ A := by {
  intro A hA B hB
  by_cases h : A = B
  · subst B; exact Or.inl le_rfl
  · exact hchain hA hB h
  }
  have hmax : ∀ t : Finset (Subgroup G), (↑t : Set (Subgroup G)) ⊆ s → ∃ M : Subgroup G, (M = ⊥ ∨ M ∈ t) ∧ ∀ H ∈ t, H ≤ M := by {
  intro t
  induction t using Finset.induction_on with
  | empty => {
  intro _
  exact ⟨⊥, Or.inl rfl, by simp⟩
  }
  | @insert A t hAt iht => {
  intro hts
  obtain ⟨M, hM, htM⟩ := iht (fun H hH => hts (Finset.mem_insert_of_mem hH))
  by_cases hMA : M ≤ A
  · {
  refine ⟨A, Or.inr (Finset.mem_insert_self _ _), ?_⟩
  intro H hH
  rcases Finset.mem_insert.mp hH with rfl | hH
  · exact le_rfl
  · exact (htM H hH).trans hMA
  }
  · {
  have hAM : A ≤ M := by {
  rcases hM with hM | hM
  · subst M; exact (hMA bot_le).elim
  · exact (htotal A (hts (Finset.mem_insert_self _ _)) M (hts (Finset.mem_insert_of_mem hM))).resolve_right hMA
  }
  refine ⟨M, ?_, ?_⟩
  · exact hM.imp id (Finset.mem_insert_of_mem)
  · {
  intro H hH
  rcases Finset.mem_insert.mp hH with rfl | hH
  · exact hAM
  · exact htM H hH
  }
  }
  }
  }
  obtain ⟨M, hM, hsM⟩ := hmax s.toFinite.toFinset (by simp)
  have hMdvd : Nat.card M ∣ p ^ (n + 1) := by {
  rcases hM with rfl | hM
  · simp
  · exact hcard M (by simpa using hM)
  }
  obtain ⟨k, hk, hMk⟩ := (Nat.dvd_prime_pow hp).mp hMdvd
  obtain ⟨L, hL, hML⟩ := exists_subgroup_card_pow_prime_le p hdvd M hMk hk
  have hsL : ∀ H ∈ s, H ≤ L := by {
  intro H hH
  exact (hsM H (by simpa using hH)).trans hML
  }
  let t : Set (Subgroup L) := {J | ∃ H ∈ s, H ≠ L ∧ J = H.subgroupOf L}
  have htchain : IsChain (· ≤ ·) t := by {
  rintro A ⟨H, hH, hHL, rfl⟩ B ⟨K, hK, hKL, rfl⟩ _
  rcases htotal H hH K hK with h | h
  · exact Or.inl (fun x hx => h hx)
  · exact Or.inr (fun x hx => h hx)
  }
  have htcard : ∀ J ∈ t, Nat.card J ∣ p ^ n := by {
  rintro J ⟨H, hH, hHL, rfl⟩
  obtain ⟨j, hj, hHj⟩ := (Nat.dvd_prime_pow hp).mp (hcard H hH)
  have hjn : j ≤ n := by {
  by_contra hn
  have he : j = n + 1 := by omega
  apply hHL
  apply Subgroup.eq_of_le_of_card_ge (hsL H hH)
  rw [hL, hHj, he]
  }
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hsL H hH)).toEquiv, hHj]
  exact Nat.pow_dvd_of_le_of_pow_dvd hjn (dvd_refl _)
  }
  have hdvdL : p ^ n ∣ Nat.card L := by {
  rw [hL]
  exact ⟨p, by rw [pow_succ]⟩
  }
  obtain ⟨f, htf, hfcard⟩ := ih (G := L) hdvdL htchain htcard
  let g : Fin (n + 1 + 1) → Subgroup G := fun k => if h : k.val < n + 1 then (f ⟨k.val, h⟩).map L.subtype else L
  have hgcard : ∀ k, Nat.card (g k) = p ^ k.val := by {
  intro k
  dsimp only [g]
  split_ifs with h
  · rw [Subgroup.card_map_of_injective L.subtype_injective, hfcard]
  · {
  have hk : k.val = n + 1 := by omega
  simpa only [hk] using hL
  }
  }
  have hgmono : Monotone g := by {
  intro a b hab
  dsimp only [g]
  split_ifs with ha hb hb
  · exact Subgroup.map_mono (f.monotone (show (⟨a.val, ha⟩ : Fin (n + 1)) ≤ ⟨b.val, hb⟩ from hab))
  · exact Subgroup.map_subtype_le _
  · omega
  · exact le_rfl
  }
  have hgstrict : StrictMono g := by {
  intro a b hab
  refine lt_of_le_of_ne (hgmono hab.le) ?_
  intro he
  have hc := congrArg (fun H : Subgroup G => Nat.card H) he
  rw [hgcard, hgcard] at hc
  exact (ne_of_lt (Nat.pow_lt_pow_right hp.one_lt (show a.val < b.val from hab))) hc
  }
  refine ⟨OrderEmbedding.ofStrictMono g hgstrict, ?_, hgcard⟩
  intro H hH
  change ∃ k, g k = H
  by_cases hHL : H = L
  · {
  refine ⟨Fin.last (n + 1), ?_⟩
  simp [g, hHL]
  }
  · {
  have hHt : H.subgroupOf L ∈ t := ⟨H, hH, hHL, rfl⟩
  obtain ⟨i, hi⟩ := htf hHt
  refine ⟨i.castSucc, ?_⟩
  have hgi : g i.castSucc = (f i).map L.subtype := by {
  change (if h : i.val < n + 1 then (f ⟨i.val, h⟩).map L.subtype else L) = (f i).map L.subtype
  exact dif_pos i.isLt
  }
  rw [hgi, hi, Subgroup.map_subgroupOf_eq_of_le (hsL H hH)]
  }
  }
