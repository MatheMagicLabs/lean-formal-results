/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     LowerHemicontinuous.exists_continuous_selection
Source:      Mathlib @ d0a050ad6, Mathlib/Topology/Semicontinuity/Michael.lean, line 107
             (added after the model's training data; human proof 35 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 7 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem LowerHemicontinuous.exists_continuous_selection (hf : LowerHemicontinuous f)
    (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x))
    (hf_isClosed : ∀ x, IsClosed (f x)) : ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
  classical
  obtain ⟨U, hU⟩ := (𝓝 (0 : β)).exists_antitone_basis
  have hU_mem (n : ℕ) : U n ∈ 𝓝 (0 : β) := hU.toHasBasis.mem_of_mem trivial
  let P := {V : Set β // IsOpen V ∧ Convex ℝ V ∧ (0 : β) ∈ V ∧ V = -V}
  have hex (s : Set β) (hs : s ∈ 𝓝 (0 : β)) : ∃ V : P, V.val + V.val ⊆ s := by { obtain ⟨T, hT, hTT⟩ := exists_nhds_zero_half hs; obtain ⟨C, hC, hCc, hCT⟩ := (locallyConvexSpace_iff_exists_convex_subset_zero ℝ β).mp inferInstance T hT; let V : Set β := interior C ∩ -interior C; have hC0 : (0 : β) ∈ interior C := mem_interior_iff_mem_nhds.mpr hC; have hV0 : (0 : β) ∈ V := ⟨hC0, by simpa using hC0⟩; have hVs : V = -V := by { ext y; simp [V, and_comm] }; have hVT : V ⊆ T := fun y hy => hCT (interior_subset hy.1); have hTT' : T + T ⊆ s := by { rintro y ⟨v, hv, w, hw, rfl⟩; exact hTT v hv w hw }; exact ⟨⟨V, isOpen_interior.inter isOpen_interior.neg, hCc.interior.inter hCc.interior.neg, hV0, hVs⟩, (add_subset_add hVT hVT).trans hTT'⟩ }
  let shrink (s : Set β) (hs : s ∈ 𝓝 (0 : β)) : P := Classical.choose (hex s hs)
  have hshrink (s : Set β) (hs : s ∈ 𝓝 (0 : β)) : (shrink s hs).val + (shrink s hs).val ⊆ s := Classical.choose_spec (hex s hs)
  let W : ℕ → P := Nat.rec (shrink (U 0) (hU_mem 0)) (fun n V => shrink (V.val ∩ U (n + 1)) (Filter.inter_mem (V.property.1.mem_nhds V.property.2.2.1) (hU_mem (n + 1))))
  have hWsum (n : ℕ) : (W (n + 1)).val + (W (n + 1)).val ⊆ (W n).val := (hshrink ((W n).val ∩ U (n + 1)) (Filter.inter_mem ((W n).property.1.mem_nhds (W n).property.2.2.1) (hU_mem (n + 1)))).trans inter_subset_left
  have hWU : ∀ n : ℕ, (W n).val ⊆ U n := by { intro n; cases n with | zero => intro y hy; exact hshrink (U 0) (hU_mem 0) ⟨y, hy, 0, (W 0).property.2.2.1, add_zero y⟩ | succ n => intro y hy; exact (hshrink ((W n).val ∩ U (n + 1)) (Filter.inter_mem ((W n).property.1.mem_nhds (W n).property.2.2.1) (hU_mem (n + 1))) ⟨y, hy, 0, (W (n + 1)).property.2.2.1, add_zero y⟩).2 }
  let Q (n : ℕ) := {v : α → β // Continuous v ∧ ∀ x, v x ∈ f x + (W n).val}
  have hstart : Nonempty (Q 0) := by { have ho : HasOpenLowerSections (fun x : α => f x + (W 0).val) := (hf.hasOpenCGraph_of_add_hasOpenCGraph (.const (W 0).property.1)).hasOpenLowerSections; have hn (x : α) : (f x + (W 0).val).Nonempty := by { obtain ⟨a, ha⟩ := hf_nonempty x; exact ⟨a, a, ha, 0, (W 0).property.2.2.1, add_zero a⟩ }; obtain ⟨v, hv, hvm⟩ := ho.exists_continuous_selection hn (fun x => (hf_convex x).add (W 0).property.2.1); exact ⟨⟨v, hv, hvm⟩⟩ }
  have hexnext (n : ℕ) (v : Q n) : ∃ w : Q (n + 1), ∀ x, w.val x ∈ {v.val x} + (W n).val := by { obtain ⟨w, hw, hwf, hwv⟩ := hf.exists_continuous_selection_refine hf_convex v.property.1 (W (n + 1)).property.1 (W (n + 1)).property.2.1 (W n).property.1 (W n).property.2.1 (W (n + 1)).property.2.2.1 (W n).property.2.2.2 v.property.2; exact ⟨⟨w, hw, hwf⟩, hwv⟩ }
  let next (n : ℕ) (v : Q n) : Q (n + 1) := Classical.choose (hexnext n v)
  let G : (n : ℕ) → Q n := Nat.rec (motive := fun n => Q n) (Classical.choice hstart) (fun n v => next n v)
  let g : ℕ → α → β := fun n => (G n).val
  have hg_cont (n : ℕ) : Continuous (g n) := (G n).property.1
  have hg_step (n : ℕ) (x : α) : g (n + 1) x - g n x ∈ (W n).val := by { have h := Classical.choose_spec (hexnext n (G n)) x; change g (n + 1) x ∈ {g n x} + (W n).val at h; obtain ⟨a, ha, b, hb, hab⟩ := h; have ha' : a = g n x := ha; subst a; rw [← hab]; simpa using hb }
  have htail : ∀ d n : ℕ, ∀ x : α, g (n + 1 + d) x - g (n + 1) x ∈ (W n).val := Nat.rec (fun n x => by simpa using (W n).property.2.2.1) (fun d ih n x => by { have hsum : (g (n + 1 + 1 + d) x - g (n + 1 + 1) x) + (g (n + 1 + 1) x - g (n + 1) x) ∈ (W n).val := hWsum n ⟨_, ih (n + 1) x, _, hg_step (n + 1) x, rfl⟩; have he : n + 1 + 1 + d = n + 1 + Nat.succ d := by { omega }; simpa only [sub_add_sub_cancel, he] using hsum })
  have hclose (k i j : ℕ) (hi : k + 2 ≤ i) (hj : k + 2 ≤ j) (x : α) : g i x - g j x ∈ (W k).val := by { have hk : k + 1 + 1 = k + 2 := by { omega }; have hik : k + 1 + 1 + (i - (k + 2)) = i := by { omega }; have hjk : k + 1 + 1 + (j - (k + 2)) = j := by { omega }; have ha : g i x - g (k + 2) x ∈ (W (k + 1)).val := by { simpa only [hik, hk] using htail (i - (k + 2)) (k + 1) x }; have hb : g j x - g (k + 2) x ∈ (W (k + 1)).val := by { simpa only [hjk, hk] using htail (j - (k + 2)) (k + 1) x }; have hb' : -(g j x - g (k + 2) x) ∈ (W (k + 1)).val := by { rw [(W (k + 1)).property.2.2.2]; simpa using hb }; have hab := hWsum k ⟨_, ha, _, hb', rfl⟩; simpa only [neg_sub, sub_add_sub_cancel] using hab }
  have hent (D : Set (β × β)) (hD : D ∈ uniformity β) : ∃ N : ℕ, ∀ x i, N ≤ i → ∀ j, N ≤ j → (g i x, g j x) ∈ D := by { rw [_root_.uniformity_eq_comap_nhds_zero β] at hD; obtain ⟨S, hS, hSD⟩ := Filter.mem_comap.mp hD; obtain ⟨k, _, hkS⟩ := hU.toHasBasis.mem_iff.mp hS; refine ⟨k + 2, ?_⟩; intro x i hi j hj; exact hSD (hkS (hWU k (hclose k j i hj hi x))) }
  have hCauchy (x : α) : CauchySeq (fun n => g n x) := by { refine ⟨inferInstance, ?_⟩; intro D hD; obtain ⟨N, hN⟩ := hent D hD; let T : Set β := (fun n => g n x) '' Set.Ici N; have hT : T ∈ Filter.map (fun n => g n x) Filter.atTop := by { change ∀ᶠ n : ℕ in Filter.atTop, g n x ∈ T; filter_upwards [Filter.eventually_ge_atTop N] with n hn; exact ⟨n, hn, rfl⟩ }; apply Filter.mem_of_superset (Filter.prod_mem_prod hT hT); rintro ⟨a, b⟩ ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩; exact hN x i hi j hj }
  have hlimit (x : α) : ∃ y : β, Filter.Tendsto (fun n => g n x) Filter.atTop (𝓝 y) := cauchySeq_tendsto_of_complete (hCauchy x)
  choose h hh using hlimit
  have hu : TendstoUniformly g h Filter.atTop := by { intro D hD; obtain ⟨E, ⟨hE, hEc⟩, hED⟩ := uniformity_hasBasis_closed.mem_iff.mp hD; obtain ⟨N, hN⟩ := hent E hE; refine Filter.eventually_atTop.2 ⟨N, ?_⟩; intro n hn x; have ht : Filter.Tendsto (fun m => (g m x, g n x)) Filter.atTop (𝓝 (h x, g n x)) := (hh x).prodMk_nhds tendsto_const_nhds; exact hED (hEc.mem_of_tendsto ht (Filter.eventually_atTop.2 ⟨N, fun m hm => hN x m hm n hn⟩)) }
  refine ⟨h, hu.continuous (Filter.Eventually.of_forall hg_cont).frequently, ?_⟩
  intro x
  have hm (n : ℕ) : g n x ∈ f x + (W n).val := (G n).property.2 x
  choose a ha b hb hab using hm
  have htb : Filter.Tendsto b Filter.atTop (𝓝 (0 : β)) := by { apply hU.toHasBasis.tendsto_right_iff.mpr; intro n hn; exact (Filter.eventually_ge_atTop n).mono (fun m hm => hU.antitone hm (hWU m (hb m))) }
  have hta : Filter.Tendsto a Filter.atTop (𝓝 (h x)) := by simpa [← hab] using (hh x).sub htb
  exact (hf_isClosed x).mem_of_tendsto hta (Filter.Eventually.of_forall ha)
