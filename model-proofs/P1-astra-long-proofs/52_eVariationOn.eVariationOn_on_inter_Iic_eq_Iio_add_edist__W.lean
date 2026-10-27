/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
Source:      Mathlib @ d0a050ad6, Mathlib/Topology/EMetricSpace/BoundedVariation.lean, line 601
             (added after the model's training data; human proof 44 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem eVariationOn_on_inter_Iic_eq_Iio_add_edist
    [TopologicalSpace α] [OrderTopology α] {f : α → M} {s : Set α} {a : α} {l : M}
    (h : (𝓝[s ∩ Iio a] a).NeBot) (ha : a ∈ s)
    (h'f : Tendsto f (𝓝[s ∩ Iio a] a) (𝓝 l)) :
    eVariationOn f (s ∩ Iic a) = eVariationOn f (s ∩ Iio a) + edist (f a) l := by
  classical
  letI := h
  have mono {v w : Set α} (hvw : v ⊆ w) :
      eVariationOn f v ≤ eVariationOn f w := by
    refine iSup_le ?_
    rintro ⟨n, u, hu, hv⟩
    exact le_iSup_of_le ⟨n, u, hu, fun i ↦ hvw (hv i)⟩ le_rfl
  have append {v : Set α} {u : ℕ → α} {n : ℕ}
      (hu : MonotoneOn u (Icc 0 n))
      (hv : ∀ i ∈ Icc 0 n, u i ∈ v)
      {b : α} (hub : u n ≤ b) (hb : b ∈ v) :
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        edist (f b) (f (u n)) ≤ eVariationOn f v := by
    let w : ℕ → α := fun i ↦ if i ≤ n then u i else b
    have hw : MonotoneOn w (Icc 0 (n + 1)) := by
      intro i hi j hj hij
      dsimp only [w]
      split_ifs <;> grind [MonotoneOn]
    have hmem : ∀ i ∈ Icc 0 (n + 1), w i ∈ v := by
      intro i hi
      dsimp only [w]
      split_ifs <;> grind
    calc
      _ = ∑ i ∈ Finset.range (n + 1),
          edist (f (w (i + 1))) (f (w i)) := by
        rw [Finset.sum_range_succ]
        congr 1
        · apply Finset.sum_congr rfl
          intro i hi
          have hin : i < n := Finset.mem_range.mp hi
          simp [w, show i ≤ n by omega, show i + 1 ≤ n by omega]
        · simp [w]
      _ ≤ eVariationOn f v := by
        simpa only [Finset.range_eq_Ico] using
          (sum_le_of_monotoneOn_Icc hw hmem)
  have toward {u : ℕ → α} {n : ℕ}
      (hu : MonotoneOn u (Icc 0 n))
      (huv : ∀ i ∈ Icc 0 n, u i ∈ s ∩ Iio a) :
      (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        edist l (f (u n)) ≤ eVariationOn f (s ∩ Iio a) := by
    have hun : u n < a := (huv n (by simp)).2
    have hev : ∀ᶠ b in 𝓝[s ∩ Iio a] a, u n < b :=
      nhdsWithin_le_nhds (Ioi_mem_nhds hun)
    apply le_of_tendsto
      (tendsto_const_nhds.add (h'f.edist tendsto_const_nhds))
    filter_upwards [self_mem_nhdsWithin, hev] with b hb hub
    exact append hu huv hub.le hb
  apply le_antisymm
  · rw [eVariationOn_eq_strictMonoOn]
    refine iSup_le ?_
    rintro ⟨n, u, hu, huv⟩
    change (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
      eVariationOn f (s ∩ Iio a) + edist (f a) l
    cases n with
    | zero => simp
    | succ n =>
      have hmem : ∀ i ∈ Icc 0 (n + 1), u i ∈ s ∩ Iic a := by
        intro i hi
        apply huv
        grind
      have hmono : MonotoneOn u (Icc 0 (n + 1)) := by
        intro i hi j hj hij
        apply hu.monotoneOn <;> grind
      have hlast := hmem (n + 1) (by simp)
      by_cases heq : u (n + 1) = a
      · have hprefix : ∀ i ∈ Icc 0 n, u i ∈ s ∩ Iio a := by
          intro i hi
          refine ⟨(hmem i (by grind)).1, ?_⟩
          rw [← heq]
          apply hu <;> grind
        have hpmono : MonotoneOn u (Icc 0 n) :=
          hmono.mono (by intro i hi; grind)
        have ht := toward hpmono hprefix
        rw [Finset.sum_range_succ, heq]
        calc
          _ ≤ (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
              (edist (f a) l + edist l (f (u n))) :=
            add_le_add le_rfl (edist_triangle (f a) l (f (u n)))
          _ = ((∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
              edist l (f (u n))) + edist (f a) l := by ac_rfl
          _ ≤ _ := add_le_add ht le_rfl
      · have hlt : u (n + 1) < a := lt_of_le_of_ne hlast.2 heq
        have hopen : ∀ i ∈ Icc 0 (n + 1), u i ∈ s ∩ Iio a := by
          intro i hi
          exact ⟨(hmem i hi).1,
            (hmono hi (by simp) hi.2).trans_lt hlt⟩
        have hs :
            (∑ i ∈ Finset.range (n + 1),
              edist (f (u (i + 1))) (f (u i))) ≤
              eVariationOn f (s ∩ Iio a) := by
          simpa only [Finset.range_eq_Ico] using
            (sum_le_of_monotoneOn_Icc hmono hopen)
        exact hs.trans (le_add_right le_rfl)
  · obtain ⟨c, hc⟩ :=
      (show ∀ᶠ c in 𝓝[s ∩ Iio a] a, c ∈ s ∩ Iio a from
        self_mem_nhdsWithin).exists
    letI : Nonempty {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s ∩ Iio a} :=
      ⟨⟨fun _ ↦ c, monotone_const, fun _ ↦ hc⟩⟩
    change (⨆ p : ℕ × {u : ℕ → α // Monotone u ∧ ∀ i, u i ∈ s ∩ Iio a},
        ∑ i ∈ Finset.range p.1,
          edist (f (p.2.1 (i + 1))) (f (p.2.1 i))) +
        edist (f a) l ≤ _
    rw [ENNReal.iSup_add]
    refine iSup_le ?_
    rintro ⟨n, u, hu, huv⟩
    have hlim :
        Tendsto
          (fun b ↦ (∑ i ∈ Finset.range n,
            edist (f (u (i + 1))) (f (u i))) + edist (f a) (f b))
          (𝓝[s ∩ Iio a] a)
          (𝓝 ((∑ i ∈ Finset.range n,
            edist (f (u (i + 1))) (f (u i))) + edist (f a) l)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.edist h'f)
    have hev : ∀ᶠ b in 𝓝[s ∩ Iio a] a, u n < b :=
      nhdsWithin_le_nhds (Ioi_mem_nhds (huv n).2)
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, hev] with b hb hub
    let v : Set α := u '' Icc 0 n
    have hs :
        (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤
          eVariationOn f v := by
      simpa only [Finset.range_eq_Ico] using
        (sum_le_of_monotoneOn_Icc (hu.monotoneOn (Icc 0 n))
          (fun i hi ↦ show u i ∈ v from ⟨i, hi, rfl⟩))
    have horder : ∀ x ∈ v, ∀ y ∈ ({b, a} : Set α), x ≤ y := by
      rintro x ⟨i, hi, rfl⟩ y hy
      have hib : u i ≤ b := (hu hi.2).trans hub.le
      simp only [mem_insert_iff, mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hib
      · exact hib.trans hb.2.le
    calc
      _ ≤ eVariationOn f v + eVariationOn f {b, a} := by
        simpa only [pair, edist_comm] using
          (add_le_add hs (le_rfl : edist (f a) (f b) ≤ edist (f a) (f b)))
      _ ≤ eVariationOn f (v ∪ {b, a}) := add_le_union f horder
      _ ≤ eVariationOn f (s ∩ Iic a) := by
        apply mono
        rintro x (hx | hx)
        · rcases hx with ⟨i, hi, rfl⟩
          exact ⟨(huv i).1, (huv i).2.le⟩
        · simp only [mem_insert_iff, mem_singleton_iff] at hx
          rcases hx with rfl | rfl
          · exact ⟨hb.1, hb.2.le⟩
          · exact ⟨ha, le_rfl⟩
