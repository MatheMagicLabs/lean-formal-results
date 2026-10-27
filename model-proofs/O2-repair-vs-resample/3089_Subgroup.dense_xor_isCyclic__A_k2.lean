/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.dense_xor_isCyclic
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Order/ArchimedeanDiscrete.lean, line 77
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem dense_xor_isCyclic [Nontrivial G] [DenselyOrdered G] (H : Subgroup G) :
    Xor (Dense (H : Set G)) (IsCyclic H) := by
  have key : Dense (H : Set G) → ¬ IsCyclic H := by
    intro hd hc
    obtain ⟨g, hg⟩ := hc.exists_generator
    have hH : H = zpowers (g : G) := by
      ext x
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
        exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
      · intro hx
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        exact H.zpow_mem g.2 n
    obtain ⟨k, hk⟩ : ∃ k : G, H = zpowers k := ⟨g, hH⟩
    clear hH hg g
    subst hk
    have hdisc : DiscreteTopology (zpowers k) := inferInstance
    rw [discreteTopology_iff_isOpen_singleton_one, isOpen_induced_iff] at hdisc
    obtain ⟨U, hU, hUeq⟩ := hdisc
    have h1 : (1 : G) ∈ U := by
      have : (1 : zpowers k) ∈ Subtype.val ⁻¹' U := by
        rw [hUeq]; exact Set.mem_singleton _
      exact this
    obtain ⟨x, hx⟩ := exists_ne (1 : G)
    have hex : ∃ u : G, 1 < u := by
      rcases lt_or_gt_of_ne hx with h | h
      · exact ⟨x⁻¹, one_lt_inv'.mpr h⟩
      · exact ⟨x, h⟩
    obtain ⟨u, hu1, hu⟩ := exists_Ico_subset_of_mem_nhds (hU.mem_nhds h1) hex
    obtain ⟨z, hzH, hz⟩ := hd.exists_between hu1
    have hmem : (⟨z, hzH⟩ : zpowers k) ∈ Subtype.val ⁻¹' U := hu ⟨hz.1.le, hz.2⟩
    rw [hUeq, Set.mem_singleton_iff, Subtype.ext_iff] at hmem
    exact hz.1.ne' hmem
  rcases dense_or_isCyclic H with hd | hc
  · exact Or.inl ⟨hd, key hd⟩
  · exact Or.inr ⟨hc, fun hd => key hd hc⟩
