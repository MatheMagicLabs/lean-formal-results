/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.dense_xor_isCyclic
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Order/ArchimedeanDiscrete.lean, line 77
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem dense_xor_isCyclic [Nontrivial G] [DenselyOrdered G] (H : Subgroup G) :
    Xor (Dense (H : Set G)) (IsCyclic H) := by
  have key : IsCyclic H → ¬ Dense (H : Set G) := by
    intro hc hd
    obtain ⟨⟨g, hgH⟩, hg⟩ := IsCyclic.exists_generator (α := H)
    have hH : H = zpowers g := by
      apply le_antisymm
      · intro x hx
        obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
        have := congrArg Subtype.val hk
        simp only [SubgroupClass.coe_zpow] at this
        exact mem_zpowers_iff.mpr ⟨k, this⟩
      · exact (zpowers_le).mpr hgH
    have hdisc : DiscreteTopology H := by rw [hH]; infer_instance
    rw [discreteTopology_iff_isOpen_singleton_one, isOpen_induced_iff] at hdisc
    obtain ⟨U, hU, hUeq⟩ := hdisc
    have h1 : (1 : G) ∈ U := by
      have : (1 : H) ∈ Subtype.val ⁻¹' U := by
        rw [hUeq]; exact Set.mem_singleton _
      exact this
    obtain ⟨x, hx1, hxU⟩ := Filter.nonempty_of_mem (f := nhdsWithin (1 : G) (Set.Ioi 1))
      (inter_mem_nhdsWithin (Set.Ioi (1 : G)) (hU.mem_nhds h1))
    obtain ⟨y, ⟨hyU, hy1⟩, hyH⟩ :=
      hd.inter_open_nonempty (U ∩ Set.Ioi 1) (hU.inter isOpen_Ioi) ⟨x, hxU, hx1⟩
    have hmem : (⟨y, hyH⟩ : H) ∈ Subtype.val ⁻¹' U := hyU
    rw [hUeq] at hmem
    have := congrArg Subtype.val (Set.mem_singleton_iff.mp hmem)
    exact absurd this (ne_of_gt hy1)
  exact H.dense_or_isCyclic.elim (fun hd => Or.inl ⟨hd, fun hc => key hc hd⟩)
    (fun hc => Or.inr ⟨hc, key hc⟩)
