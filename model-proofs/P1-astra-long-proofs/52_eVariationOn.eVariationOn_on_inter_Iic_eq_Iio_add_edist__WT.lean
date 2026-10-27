/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
Source:      Mathlib @ d0a050ad6, Mathlib/Topology/EMetricSpace/BoundedVariation.lean, line 601
             (added after the model's training data; human proof 44 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 4 call(s)
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
  letI := h
  have hleft (b : α) (hb : b ∈ s) (hba : b < a) :
  eVariationOn f (s ∩ Iic b) + edist (f b) l ≤ eVariationOn f (s ∩ Iio a) := by {
  apply le_of_tendsto (tendsto_const_nhds.add (tendsto_const_nhds.edist h'f))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hba)] with x hx hbx
  have hg : IsGreatest (s ∩ Iic b) b := ⟨⟨hb, le_rfl⟩, fun z hz => hz.2⟩
  have hl : IsLeast ({b, x} : Set α) b := by {
  refine ⟨by simp, ?_⟩
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact le_rfl
  · exact hbx.le
  }
  rw [← pair f b x, ← union f hg hl]
  exact mono f (by {
  intro z hz
  simp only [mem_union, mem_inter_iff, mem_Iic, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | rfl | rfl
  · exact ⟨hz.1, hz.2.trans_lt hba⟩
  · exact ⟨hb, hba⟩
  · exact hx
  })
  }
  have hright (b : α) (hba : b < a) :
  eVariationOn f (s ∩ Iic b) + edist (f a) l ≤ eVariationOn f (s ∩ Iic a) := by {
  apply le_of_tendsto (tendsto_const_nhds.add (tendsto_const_nhds.edist h'f))
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds hba)] with x hx hbx
  have H := add_le_union f (s := s ∩ Iic b) (t := {x, a}) (by {
  intro y hy z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl
  · exact hy.2.trans hbx.le
  · exact hy.2.trans hba.le
  })
  rw [pair, edist_comm (f x) (f a)] at H
  exact H.trans (mono f (by {
  intro z hz
  simp only [mem_union, Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | rfl | rfl
  · exact ⟨hz.1, hz.2.trans hba.le⟩
  · exact ⟨hx.1, hx.2.le⟩
  · exact ⟨ha, le_rfl⟩
  }))
  }
  apply le_antisymm
  · {
  rw [eVariationOn_eq_strictMonoOn]
  refine iSup_le ?_
  rintro ⟨n, u, hu, hus⟩
  change (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f (s ∩ Iio a) + edist (f a) l
  by_cases hn : n = 0
  · subst n; simp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  by_cases hlast : u (n + 1) < a
  · {
  apply le_trans (sum_le_of_monotoneOn_Iic hu.monotoneOn ?_) (le_add_right le_rfl)
  intro i hi
  exact ⟨(hus i hi).1, (hu.monotoneOn hi (by simp) hi).trans_lt hlast⟩
  }
  have hlast' : u (n + 1) = a := le_antisymm (hus _ (by simp)).2 (le_of_not_gt hlast)
  have hna : u n < a := by {
  rw [← hlast']
  exact hu (by simp) (by simp) (Nat.lt_succ_self n)
  }
  have hp :
  (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f (s ∩ Iic (u n)) := by {
  apply sum_le_of_monotoneOn_Iic (hu.monotoneOn.mono (by {
  intro i hi
  exact hi.trans (Nat.le_succ n)
  }))
  intro i hi
  exact ⟨(hus i (hi.trans (Nat.le_succ n))).1, hu.monotoneOn (hi.trans (Nat.le_succ n)) (Nat.le_succ n) hi⟩
  }
  have hp' := (add_le_add hp (le_refl (edist (f (u n)) l))).trans (hleft (u n) (hus n (Nat.le_succ n)).1 hna)
  rw [Finset.sum_range_succ, hlast']
  have ht := add_le_add (le_refl (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i)))) (edist_triangle (f a) l (f (u n)))
  apply le_trans _ (add_le_add hp' (le_refl (edist (f a) l)))
  simpa only [edist_comm l (f (u n)), add_assoc, add_comm, add_left_comm] using ht
  }
  · {
  have hs : (s ∩ Iio a).Nonempty := Filter.nonempty_of_mem (self_mem_nhdsWithin : s ∩ Iio a ∈ 𝓝[s ∩ Iio a] a)
  haveI := nonempty_monotone_mem hs
  rw [eVariationOn, ENNReal.iSup_add]
  refine iSup_le ?_
  rintro ⟨n, u, hu, hus⟩
  have hp :
  (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) ≤ eVariationOn f (s ∩ Iic (u n)) := by {
  apply sum_le_of_monotoneOn_Iic (hu.monotoneOn _)
  intro i hi
  exact ⟨(hus i).1, hu hi⟩
  }
  exact (add_le_add hp (le_refl (edist (f a) l))).trans (hright (u n) (hus n).2)
  }
