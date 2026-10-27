/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_cycleGraph_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 392
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open Finset Function
namespace SimpleGraph
variable {α : Type*} [DecidableEq α] {G : SimpleGraph α}
variable {β : Type*} [DecidableEq β] {H : SimpleGraph β}
variable {a b v : α} {p : G.Walk a b} {f : G →g H}
namespace Walk
section
variable [Fintype α]
end
variable {p : G.Walk a a}
end Walk
variable [Fintype α]

@[simp]
theorem isHamiltonian_cycleGraph_iff {n : ℕ} : (cycleGraph n).IsHamiltonian ↔ n = 1 ∨ 3 ≤ n := by
  constructor
  · intro hH
    by_contra hc
    push_neg at hc
    obtain ⟨a, p, hp⟩ := hH (by rw [Fintype.card_fin]; exact hc.1)
    have h1 := hp.length_eq
    have h2 := hp.isCycle.three_le_length
    rw [Fintype.card_fin] at h1
    omega
  · rintro (rfl | hn)
    · intro h
      exact absurd (Fintype.card_fin 1) h
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      haveI : NeZero (m+3) := ⟨by omega⟩
      obtain ⟨f, hf⟩ : ∃ f : ℕ → Fin (m+3), ∀ i, (f i).val = i % (m+3) :=
        ⟨fun i => ⟨i % (m+3), Nat.mod_lt _ (by omega)⟩, fun i => rfl⟩
      have hv : ∀ a b : ℕ, a < m+3 → b < m+3 → f a = f b → a = b := by
        intro a b ha hb h
        have h2 := congrArg Fin.val h
        rw [hf, hf, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
        exact h2
      have hsub : ∀ x y : Fin (m+3), (x - y).val = (m+3 - y.val + x.val) % (m+3) := by
        intro x y
        first
          | rfl
          | exact Fin.coe_sub x y
          | simp [Fin.sub_def]
      have hA : ∀ x y : Fin (m+3), (y - x).val = 1 → (cycleGraph (m+3)).Adj x y := by
        intro x y h
        first
          | (rw [cycleGraph_adj']; exact Or.inr h)
          | (rw [cycleGraph_adj]; exact Or.inr (Fin.ext (by rw [h]; simp)))
      have hadj : ∀ j : ℕ, j < m+2 → (cycleGraph (m+3)).Adj (f j) (f (j+1)) := by
        intro j hj
        apply hA
        rw [hsub, hf, hf, Nat.mod_eq_of_lt (show j < m+3 by omega),
          Nat.mod_eq_of_lt (show j+1 < m+3 by omega)]
        have e : m+3-j+(j+1) = 1 + (m+3) := by omega
        rw [e, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      have h0 : (cycleGraph (m+3)).Adj (f (m+2)) (f 0) := by
        apply hA
        rw [hsub, hf, hf, Nat.mod_eq_of_lt (show m+2 < m+3 by omega), Nat.zero_mod]
        have e : m+3-(m+2)+0 = 1 := by omega
        rw [e]
        exact Nat.mod_eq_of_lt (by omega)
      have key : ∀ j : ℕ, j < m+3 → ∃ p : (cycleGraph (m+3)).Walk (f 0) (f j),
          p.support = (List.range (j+1)).map f ∧
          p.edges = (List.range j).map (fun i : ℕ => s(f i, f (i+1))) := by
        intro j
        induction j with
        | zero =>
          intro _
          exact ⟨Walk.nil, by simp, by simp⟩
        | succ j ih =>
          intro hj
          obtain ⟨p, hs, he⟩ := ih (by omega)
          refine ⟨p.concat (hadj j (by omega)), ?_, ?_⟩
          · simp [Walk.support_concat, hs, List.range_succ]
          · simp [Walk.edges_concat, he, List.range_succ]
      obtain ⟨p, hs, he⟩ := key (m+2) (by omega)
      have hnd : ((List.range (m+2+1)).map f).Nodup := by
        refine List.Nodup.map_on ?_ ?_
        · intro x hx y hy hxy
          have hx' := List.mem_range.1 hx
          have hy' := List.mem_range.1 hy
          exact hv x y (by omega) (by omega) hxy
        · first | exact List.nodup_range _ | exact List.nodup_range
      have hpath : p.IsPath := by
        rw [Walk.isPath_def, hs]; exact hnd
      have hedge : s(f (m+2), f 0) ∉ p.edges := by
        rw [he]
        intro hmem
        obtain ⟨i, hi, heq⟩ := List.mem_map.1 hmem
        have hi' := List.mem_range.1 hi
        rcases Sym2.eq_iff.1 heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have := hv i (m+2) (by omega) (by omega) h1
          omega
        · have := hv i 0 (by omega) (by omega) h1
          have := hv (i+1) (m+2) (by omega) (by omega) h2
          omega
      have hcyc : (Walk.cons h0 p).IsCycle := by
        rw [Walk.cons_isCycle_iff]
        exact ⟨hpath, hedge⟩
      intro _
      refine ⟨_, Walk.cons h0 p, ?_⟩
      rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
      refine ⟨hcyc, ?_⟩
      intro a
      rw [Walk.support_cons, List.tail_cons, hs]
      exact List.count_eq_one_of_mem hnd
        (List.mem_map.2 ⟨a.val, List.mem_range.2 (by have := a.isLt; omega),
          Fin.ext (by rw [hf, Nat.mod_eq_of_lt a.isLt])⟩)
