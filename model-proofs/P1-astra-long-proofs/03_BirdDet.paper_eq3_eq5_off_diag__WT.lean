/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     BirdDet.paper_eq3_eq5_off_diag
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean, line 235
             (added after the model's training data; human proof 26 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 3 call(s)
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
  let D : Finset (Fin n × (Fin p → Fin n)) :=
    (Finset.Ioi i) ×ˢ S p i
  let E : Finset ((Fin (p + 1) → Fin n) × Fin (p + 1)) :=
    S (p + 1) i ×ˢ Finset.univ
  let D' := D.filter (fun q => q.1 ∉ Set.range q.2)
  let f : Fin n × (Fin p → Fin n) → R :=
    fun q => bminor A i q.1 q.2 * A q.1 j
  let g : ((Fin (p + 1) → Fin n) × Fin (p + 1)) →
      Fin n × (Fin p → Fin n) :=
    fun q => (q.1 q.2, q.2.removeNth q.1)
  have hmem (q : (Fin (p + 1) → Fin n) × Fin (p + 1))
      (hq : q ∈ E) : g q ∈ D' := by
    have hα : q.1 ∈ S (p + 1) i := (Finset.mem_product.mp hq).1
    obtain ⟨hi, hm⟩ := Fin.strictMono_cons.mp (mem_S_iff.mp hα)
    have htail : q.2.removeNth q.1 ∈ S p i := by
      apply mem_S_iff.mpr
      apply Fin.strictMono_cons.mpr
      constructor
      · intro r
        exact hi (q.2.succAbove r)
      · exact hm.comp (Fin.strictMono_succAbove q.2)
    have hn : q.1 q.2 ∉ Set.range (q.2.removeNth q.1) := by
      rintro ⟨r, hr⟩
      exact Fin.succAbove_ne q.2 r (hm.injective hr)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨Finset.mem_Ioi.mpr (hi q.2), htail⟩, hn⟩
  have hinj : ∀ a ∈ E, ∀ b ∈ E, g a = g b → a = b := by
    rintro ⟨α, s⟩ ha ⟨β, t⟩ hb he
    have hmα : StrictMono α :=
      (Fin.strictMono_cons.mp (mem_S_iff.mp (Finset.mem_product.mp ha).1)).2
    have hmβ : StrictMono β :=
      (Fin.strictMono_cons.mp (mem_S_iff.mp (Finset.mem_product.mp hb).1)).2
    have hv : α s = β t := congrArg Prod.fst he
    have hd : s.removeNth α = t.removeNth β := congrArg Prod.snd he
    have hr : Set.range α = Set.range β := by
      calc
        Set.range α = Set.insert (α s) (Set.range (s.removeNth α)) := by
          exact (Fin.range_insertNth s (α s) (s.removeNth α)).symm.trans
            (congrArg Set.range (Fin.insertNth_self_removeNth s α)) |>.symm
        _ = Set.insert (β t) (Set.range (t.removeNth β)) := by rw [hv, hd]
        _ = Set.range β := by
          rw [← Fin.range_insertNth, Fin.insertNth_self_removeNth]
    have hab : α = β := (hmα.range_inj_of_wellFoundedLT hmβ).mp hr
    subst β
    have hst : s = t := hmα.injective hv
    subst t
    rfl
  have hsurj : ∀ b ∈ D', ∃ a ∈ E, g a = b := by
    rintro ⟨k, α⟩ hb
    have hb' : (i < k ∧ α ∈ S p i) ∧ k ∉ Set.range α := by
      simpa only [D', D, Finset.mem_filter, Finset.mem_product,
        Finset.mem_Ioi] using hb
    obtain ⟨t, ht⟩ := exists_insertNth_mem_S hb'.1.2 hb'.1.1 hb'.2
    refine ⟨(t.insertNth k α, t), ?_, ?_⟩
    · exact Finset.mem_product.mpr ⟨ht, Finset.mem_univ t⟩
    · dsimp [g]
      simp only [Fin.insertNth_apply_same, Fin.removeNth_insertNth]
  have hs : (∑ q ∈ E, f (g q)) = ∑ q ∈ D', f q := by
    refine Finset.sum_bij (fun q _ => g q) hmem hinj ?_ (fun _ _ => rfl)
    intro b hb
    obtain ⟨a, ha, he⟩ := hsurj b hb
    exact ⟨a, ha, he⟩
  have hz : (∑ q ∈ D', f q) = ∑ q ∈ D, f q := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro q hq hn
    have hk : q.1 ∈ Set.range q.2 := by
      by_contra hk
      exact hn (Finset.mem_filter.mpr ⟨hq, hk⟩)
    change bminor A i q.1 q.2 * A q.1 j = 0
    rw [bminor_eq_zero_of_mem_range A q.2 i hk, zero_mul]
  calc
    _ = ∑ q ∈ D, f q := (Finset.sum_product _ _ f).symm
    _ = ∑ q ∈ D', f q := hz.symm
    _ = ∑ q ∈ E, f (g q) := hs.symm
    _ = _ := Finset.sum_product _ _ (fun q => f (g q))
