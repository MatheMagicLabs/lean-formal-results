/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     BirdDet.paper_eq3_eq5_off_diag
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/Matrix/Determinant/Bird/Correctness.lean, line 235
             (added after the model's training data; human proof 26 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 3 call(s)
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
  have tail_range : ∀ {q : ℕ} (a b : Fin (q + 1) → Fin n), Injective a → a 0 = b 0 → Set.range a ⊆ Set.range b → Set.range (Fin.tail a) ⊆ Set.range (Fin.tail b) := by intro q a b ha h0 hr k hk; obtain ⟨v, hv⟩ := hk; obtain ⟨w, hw⟩ := hr ⟨v.succ, hv⟩; cases w using Fin.cases with | zero => exact False.elim (v.succ_ne_zero (ha (hv.trans (hw.symm.trans h0.symm)))) | succ w => exact ⟨w, hw⟩
  have sorted_unique : ∀ {q : ℕ} (a b : Fin q → Fin n), StrictMono a → StrictMono b → Set.range a = Set.range b → a = b := by intro q; induction q with | zero => intro a b _ _ _; exact Subsingleton.elim _ _ | succ q ih => intro a b ha hb hr; have h0 : a 0 = b 0 := (by exact le_antisymm (by obtain ⟨v, hv⟩ := hr.symm ▸ (show b 0 ∈ Set.range b from ⟨0, rfl⟩); simpa only [hv] using ha.monotone (show (0 : Fin (q + 1)) ≤ v from bot_le)) (by obtain ⟨v, hv⟩ := hr ▸ (show a 0 ∈ Set.range a from ⟨0, rfl⟩); simpa only [hv] using hb.monotone (show (0 : Fin (q + 1)) ≤ v from bot_le))); have ht := ih (Fin.tail a) (Fin.tail b) (ha.comp Fin.strictMono_succ) (hb.comp Fin.strictMono_succ) (Set.Subset.antisymm (tail_range a b ha.injective h0 hr.subset) (tail_range b a hb.injective h0.symm hr.symm.subset)); funext v; exact Fin.cases h0 (fun w => congrFun ht w) v
  let T := ((Finset.Ioi i) ×ˢ S p i).filter (fun x => x.1 ∉ Set.range x.2)
  have hs : (∑ k ∈ Finset.Ioi i, ∑ α ∈ S p i, bminor A i k α * A k j) = ∑ x ∈ T, bminor A i x.1 x.2 * A x.1 j := by unfold T; rw [Finset.sum_filter, Finset.sum_product]; apply Finset.sum_congr rfl; intro k hk; apply Finset.sum_congr rfl; intro α hα; by_cases h : k ∈ Set.range α <;> simp [h, bminor_eq_zero_of_mem_range, *]
  rw [hs]
  symm
  trans ∑ x ∈ (S (p + 1) i) ×ˢ (Finset.univ : Finset (Fin (p + 1))), bminor A i (x.1 x.2) (x.2.removeNth x.1) * A (x.1 x.2) j
  · simp only [Finset.sum_product]
  refine Finset.sum_bij (fun x _ => (x.1 x.2, x.2.removeNth x.1)) ?_ ?_ ?_ ?_
  · intro x hx; have hm := Fin.strictMono_cons.mp (mem_S_iff.mp (Finset.mem_product.mp hx).1); have hn : x.1 x.2 ∉ Set.range (x.2.removeNth x.1) := (by rintro ⟨q, hq⟩; have he : x.2.succAbove q = x.2 := hm.2.injective hq; simpa using he); change (x.1 x.2, x.2.removeNth x.1) ∈ ((Finset.Ioi i) ×ˢ S p i).filter _; rw [Finset.mem_filter, Finset.mem_product]; refine ⟨⟨Finset.mem_Ioi.mpr (hm.1 x.2), mem_S_iff.mpr (Fin.strictMono_cons.mpr ⟨fun q => hm.1 (x.2.succAbove q), ?_⟩)⟩, hn⟩; exact hm.2.comp (Fin.strictMono_succAbove x.2)
  · intro x hx y hy he; have hxmono := (Fin.strictMono_cons.mp (mem_S_iff.mp (Finset.mem_product.mp hx).1)).2; have hymono := (Fin.strictMono_cons.mp (mem_S_iff.mp (Finset.mem_product.mp hy).1)).2; have hb : x.1 x.2 = y.1 y.2 := congrArg Prod.fst he; have hd : x.2.removeNth x.1 = y.2.removeNth y.1 := congrArg Prod.snd he; have hr : Set.range x.1 = Set.range y.1 := (by apply Set.ext; intro k; exact ⟨(by rintro ⟨v, rfl⟩; exact Fin.succAboveCases x.2 ⟨y.2, hb.symm⟩ (fun q => ⟨y.2.succAbove q, (congrFun hd q).symm⟩) v), (by rintro ⟨v, rfl⟩; exact Fin.succAboveCases y.2 ⟨x.2, hb⟩ (fun q => ⟨x.2.succAbove q, congrFun hd q⟩) v)⟩); have hw := sorted_unique x.1 y.1 hxmono hymono hr; apply Prod.ext hw; apply hymono.injective; simpa only [hw] using hb
  · intro x hx; obtain ⟨hx, hn⟩ := Finset.mem_filter.mp hx; obtain ⟨hk, hα⟩ := Finset.mem_product.mp hx; obtain ⟨t, ht⟩ := exists_insertNth_mem_S hα (Finset.mem_Ioi.mp hk) hn; refine ⟨(t.insertNth x.1 x.2, t), Finset.mem_product.mpr ⟨ht, Finset.mem_univ _⟩, ?_⟩; simp
  · intro x hx; rfl
