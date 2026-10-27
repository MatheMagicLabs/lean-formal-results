/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Subgroup.dense_xor_isCyclic
Source:      Mathlib @ a02a63c2, Mathlib/Topology/Algebra/Order/ArchimedeanDiscrete.lean, line 77
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
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
    obtain ⟨⟨g, hg⟩, hgen⟩ := hc
    have hpow : ∀ z ∈ H, ∃ n : ℤ, g ^ n = z := by
      intro z hz
      obtain ⟨n, hn⟩ := hgen ⟨z, hz⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have aux : ∀ k : G, 1 < k → (∀ z ∈ H, ∃ n : ℤ, k ^ n = z) → False := by
      intro k hk hk'
      obtain ⟨w, hwH, hw1, hw2⟩ := hd.exists_between hk
      obtain ⟨n, rfl⟩ := hk' w hwH
      have h1 : k ^ (0:ℤ) < k ^ n := by simpa using hw1
      have h2 : k ^ n < k ^ (1:ℤ) := by simpa using hw2
      rw [zpow_lt_zpow_iff_right hk] at h1 h2
      omega
    obtain ⟨y, hy⟩ := exists_ne (1 : G)
    obtain ⟨x, hx⟩ : ∃ x : G, 1 < x := by
      rcases lt_or_gt_of_ne hy with h | h
      · exact ⟨y⁻¹, one_lt_inv'.mpr h⟩
      · exact ⟨y, h⟩
    obtain ⟨z, hzH, hz1, -⟩ := hd.exists_between hx
    rcases lt_trichotomy g 1 with h | h | h
    · refine aux g⁻¹ (one_lt_inv'.mpr h) fun w hw => ?_
      obtain ⟨n, rfl⟩ := hpow w hw
      exact ⟨-n, by rw [inv_zpow', neg_neg]⟩
    · obtain ⟨n, rfl⟩ := hpow z hzH
      subst h
      simp at hz1
    · exact aux g h hpow
  rcases H.dense_or_isCyclic with h | h
  · exact Or.inl ⟨h, key h⟩
  · exact Or.inr ⟨h, fun hd => key hd h⟩
