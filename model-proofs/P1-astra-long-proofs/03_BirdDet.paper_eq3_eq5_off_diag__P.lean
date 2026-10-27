/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     BirdDet.paper_eq3_eq5_off_diag
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean, line 235
             (added after the model's training data; human proof 26 tactic steps)
Experiment:  P1-astra-long-proofs, arm P, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

theorem paper_eq3_eq5_off_diag (i j : Fin n) :
    ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j =
      ∑ α' ∈ S (p + 1) i, ∑ t : Fin (p + 1), bminor A i (α' t) (t.removeNth α') * A (α' t) j := by
  classical
  have hfilter :
      ∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j =
        ∑ k ∈ Finset.Ioi i, ∑ α ∈ (S p i).filter (fun α ↦ k ∉ Set.range α),
          bminor A i k α * A k j := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro α hα
    by_cases h : k ∈ Set.range α
    · simp [h, bminor_eq_zero_of_mem_range A α i h]
    · simp [h]
  have hreindex :
      ∑ k ∈ Finset.Ioi i, ∑ α ∈ (S p i).filter (fun α ↦ k ∉ Set.range α),
        bminor A i k α * A k j =
        ∑ α' ∈ S (p + 1) i, ∑ t : Fin (p + 1),
          bminor A i (α' t) (t.removeNth α') * A (α' t) j := by
    classical
    have hsorted {q : ℕ} {a b : Fin q → Fin n}
        (ha : StrictMono a) (hb : StrictMono b)
        (hr : Set.range a = Set.range b) : a = b := by
      have haux : ∀ r : ℕ, ∀ x : Fin q, x.val = r → a x = b x := by
        intro r
        induction r using Nat.strong_induction_on with
        | h r ih =>
          intro x hx
          obtain ⟨y, hy⟩ := hr ▸ (show a x ∈ Set.range a from ⟨x, rfl⟩)
          obtain ⟨z, hz⟩ := hr.symm ▸ (show b x ∈ Set.range b from ⟨x, rfl⟩)
          have hxy : x ≤ y := by
            by_contra hn
            have hyx : y < x := lt_of_not_ge hn
            have he : a y = b y := ih y.val (by rw [← hx]; exact hyx) y rfl
            exact (ne_of_lt hyx) (ha.injective (he.trans hy))
          have hxz : x ≤ z := by
            by_contra hn
            have hzx : z < x := lt_of_not_ge hn
            have he : a z = b z := ih z.val (by rw [← hx]; exact hzx) z rfl
            exact (ne_of_lt hzx) (hb.injective (he.symm.trans hz))
          exact le_antisymm
            (by simpa [hz] using ha.monotone hxz)
            (by simpa [hy] using hb.monotone hxy)
      exact funext fun x ↦ haux x.val x rfl
    symm
    suffices h :
        (∑ x ∈ (S (p + 1) i).sigma (fun _ ↦ (Finset.univ : Finset (Fin (p + 1)))),
          bminor A i (x.1 x.2) (x.2.removeNth x.1) * A (x.1 x.2) j) =
        (∑ y ∈ (Finset.Ioi i).sigma
          (fun k ↦ (S p i).filter (fun α ↦ k ∉ Set.range α)),
          bminor A i y.1 y.2 * A y.1 j) by
      simpa only [Finset.sum_sigma] using h
    refine Finset.sum_bij
      (fun x _ ↦ ⟨x.1 x.2, x.2.removeNth x.1⟩) ?_ ?_ ?_ ?_
    · intro x hx
      have hα := mem_S_iff.mp (Finset.mem_sigma.mp hx).1
      have hm := (Fin.strictMono_cons.mp hα).2
      apply Finset.mem_sigma.mpr
      refine ⟨Finset.mem_Ioi.mpr ((Fin.strictMono_cons.mp hα).1 x.2), ?_⟩
      apply Finset.mem_filter.mpr
      constructor
      · apply mem_S_iff.mpr
        apply Fin.strictMono_cons.mpr
        constructor
        · intro s
          exact (Fin.strictMono_cons.mp hα).1 (x.2.succAbove s)
        · exact hm.comp (Fin.strictMono_succAbove x.2)
      · rintro ⟨s, hs⟩
        have he : x.2.succAbove s = x.2 := hm.injective hs
        simpa using he
    · intro x hx y hy h
      have hk : x.1 x.2 = y.1 y.2 := congrArg Sigma.fst h
      have hd : x.2.removeNth x.1 = y.2.removeNth y.1 :=
        congrArg (fun z ↦ z.2) h
      have hmx := (Fin.strictMono_cons.mp
        (mem_S_iff.mp (Finset.mem_sigma.mp hx).1)).2
      have hmy := (Fin.strictMono_cons.mp
        (mem_S_iff.mp (Finset.mem_sigma.mp hy).1)).2
      have hr : Set.range x.1 = Set.range y.1 := by
        ext v
        constructor
        · rintro ⟨s, rfl⟩
          refine Fin.succAboveCases x.2 ?_ (fun u ↦ ?_) s
          · exact ⟨y.2, hk.symm⟩
          · exact ⟨y.2.succAbove u, (congrFun hd u).symm⟩
        · rintro ⟨s, rfl⟩
          refine Fin.succAboveCases y.2 ?_ (fun u ↦ ?_) s
          · exact ⟨x.2, hk⟩
          · exact ⟨x.2.succAbove u, congrFun hd u⟩
      have hab := hsorted hmx hmy hr
      have ht : x.2 = y.2 := hmy.injective (by simpa [hab] using hk)
      cases x
      cases y
      simp_all
    · intro y hy
      obtain ⟨hk, hα, hnot⟩ :
          i < y.1 ∧ y.2 ∈ S p i ∧ y.1 ∉ Set.range y.2 := by
        simpa only [Finset.mem_sigma, Finset.mem_Ioi, Finset.mem_filter] using hy
      obtain ⟨t, ht⟩ := exists_insertNth_mem_S hα hk hnot
      refine ⟨⟨t.insertNth y.1 y.2, t⟩, ?_, ?_⟩
      · exact Finset.mem_sigma.mpr ⟨ht, Finset.mem_univ t⟩
      · simp
    · intro x hx
      rfl
  exact hfilter.trans hreindex
