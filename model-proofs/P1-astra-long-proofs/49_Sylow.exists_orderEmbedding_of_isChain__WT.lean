/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sylow.exists_orderEmbedding_of_isChain
Source:      Mathlib @ d0a050ad6, Mathlib/GroupTheory/Sylow.lean, line 724
             (added after the model's training data; human proof 35 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 2 call(s)
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
  haveI : Fact p.Prime := ⟨hp⟩
  have extend : ∀ (m : ℕ) (L : Subgroup G) (t : Set (Subgroup G)),
      IsChain (· ≤ ·) t → (∀ H ∈ t, Nat.card H ∣ p ^ m) →
      (∀ H ∈ t, H ≤ L) → p ^ m ∣ Nat.card L →
      ∃ K : Subgroup G, Nat.card K = p ^ m ∧ (∀ H ∈ t, H ≤ K) ∧ K ≤ L := by {
  intro m L t ht hc hL hd;
  by_cases hn : t.Nonempty;
  · letI : Nonempty t := ⟨⟨hn.choose, hn.choose_spec⟩⟩;
    obtain ⟨H, hH⟩ := Finite.exists_max (fun H : t => Nat.card H.val);
    obtain ⟨K, hK, hHK, hKL⟩ :=
      exists_subgroup_card_pow_prime_le_le hp (hc H H.property) hd (hL H H.property);
    refine ⟨K, hK, ?_, hKL⟩;
    intro J hJ;
    rcases ht.total hJ H.property with h | h;
    · exact h.trans hHK;
    · have he : H.val = J := Subgroup.eq_of_le_of_card_ge h (hH ⟨J, hJ⟩);
      exact he ▸ hHK;
  · obtain ⟨K, hK, _, hKL⟩ :=
      exists_subgroup_card_pow_prime_le_le (H := (⊥ : Subgroup G)) hp
        (by simp) hd bot_le;
    exact ⟨K, hK, fun H hH => (hn ⟨H, hH⟩).elim, hKL⟩ }
  have tower : ∀ m (L : Subgroup G) (t : Set (Subgroup G)),
      IsChain (· ≤ ·) t → (∀ H ∈ t, Nat.card H ∣ p ^ m) →
      (∀ H ∈ t, H ≤ L) → p ^ m ∣ Nat.card L →
      ∃ f : Fin (m + 1) → Subgroup G,
        Monotone f ∧ t ⊆ Set.range f ∧
        (∀ i, Nat.card (f i) = p ^ i.val) ∧ (∀ i, f i ≤ L) := by {
  intro m;
  induction m with
  | zero =>
    intro L t ht hc hL hd;
    obtain ⟨K, hK, htK, hKL⟩ := extend 0 L t ht hc hL hd;
    refine ⟨fun _ => K, fun _ _ _ => le_rfl, ?_, ?_, fun _ => hKL⟩;
    · intro H hH;
      have he : H = K := Subgroup.eq_of_le_of_card_ge (htK H hH)
        (by { rw [hK, pow_zero]; exact Nat.succ_le_of_lt Nat.card_pos });
      exact ⟨0, he.symm⟩;
    · intro i;
      have hi : i.val = 0 := by omega;
      simpa [hi] using hK
  | succ m ih =>
    intro L t ht hc hL hd;
    obtain ⟨K, hK, htK, hKL⟩ := extend (m + 1) L t ht hc hL hd;
    let u : Set (Subgroup G) := {H | H ∈ t ∧ Nat.card H ≠ p ^ (m + 1)};
    have hu : IsChain (· ≤ ·) u := ht.mono (fun H hH => hH.1);
    have huc : ∀ H ∈ u, Nat.card H ∣ p ^ m := by {
    intro H hH;
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow hp).mp (hc H hH.1);
    have hkm : k ≤ m := by {
    have hne : k ≠ m + 1 := by {
    intro h;
    exact hH.2 (he.trans (congrArg (fun j => p ^ j) h)) };
    omega };
    rw [he];
    exact pow_dvd_pow p hkm };
    have hdK : p ^ m ∣ Nat.card K := by {
    rw [hK];
    exact pow_dvd_pow p (Nat.le_succ m) };
    obtain ⟨f, hmono, huf, hfcard, hfK⟩ :=
      ih K u hu huc (fun H hH => htK H hH.1) hdK;
    let g : Fin (m + 1 + 1) → Subgroup G :=
      fun i => if hi : i.val < m + 1 then f ⟨i.val, hi⟩ else K;
    have hgmono : Monotone g := by {
    intro i j hij;
    have hv : i.val ≤ j.val := hij;
    dsimp only [g];
    split_ifs with hi hj hj;
    · exact hmono hv;
    · exact hfK _;
    · omega;
    · exact le_rfl };
    refine ⟨g, hgmono, ?_, ?_, ?_⟩;
    · intro H hH;
      by_cases he : Nat.card H = p ^ (m + 1);
      · have hHK : H = K :=
          Subgroup.eq_of_le_of_card_ge (htK H hH) (by rw [hK, he]);
        refine ⟨⟨m + 1, by omega⟩, ?_⟩;
        simp [g, hHK];
      · obtain ⟨i, hi⟩ := huf ⟨hH, he⟩;
        refine ⟨⟨i.val, by omega⟩, ?_⟩;
        dsimp only [g];
        rw [dif_pos i.isLt];
        exact hi;
    · intro i;
      dsimp only [g];
      split_ifs with hi;
      · exact hfcard _;
      · have he : i.val = m + 1 := by omega;
        simpa [he] using hK;
    · intro i;
      dsimp only [g];
      split_ifs;
      · exact (hfK _).trans hKL;
      · exact hKL }
  obtain ⟨f, hmono, hsf, hfcard, _⟩ :=
    tower n ⊤ s hchain hcard (fun _ _ => le_top)
      (by simpa only [Subgroup.card_top] using hdvd)
  have hstrict : StrictMono f := by {
  intro i j hij;
  refine lt_of_le_of_ne (hmono hij.le) ?_;
  intro he;
  have hc : p ^ i.val = p ^ j.val := by {
  rw [← hfcard i, ← hfcard j, he] };
  have hlt : p ^ i.val < p ^ j.val :=
    Nat.pow_lt_pow_right hp.one_lt hij;
  exact (ne_of_lt hlt) hc }
  exact ⟨OrderEmbedding.ofStrictMono f hstrict, hsf, hfcard⟩
