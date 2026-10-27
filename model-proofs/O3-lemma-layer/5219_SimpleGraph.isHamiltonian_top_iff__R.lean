/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     SimpleGraph.isHamiltonian_top_iff
Source:      Mathlib @ a02a63c2, Mathlib/Combinatorics/SimpleGraph/Hamiltonian.lean, line 404
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
theorem isHamiltonian_top_iff :
    (completeGraph α).IsHamiltonian ↔ Fintype.card α = 1 ∨ 3 ≤ Fintype.card α := by
  constructor
  · intro h
    by_cases h1 : Fintype.card α = 1
    · exact Or.inl h1
    · right
      obtain ⟨a, p, hp⟩ := h h1
      have := hp.toIsCycle.three_le_length
      rw [hp.length_eq] at this
      exact this
  · rintro (h1 | h3)
    · intro h; exact absurd h1 h
    · intro _
      have key : ∀ (l : List α) (a b : α), (a :: (l ++ [b])).Nodup →
          ∃ p : (completeGraph α).Walk a b, p.support = a :: (l ++ [b]) := by
        intro l
        induction l with
        | nil =>
          intro a b hn
          have hab : a ≠ b := by simpa using hn
          exact ⟨Walk.cons (show (completeGraph α).Adj a b from hab) Walk.nil, by simp⟩
        | cons c l ih =>
          intro a b hn
          rw [List.nodup_cons] at hn
          obtain ⟨hp, hpe⟩ := ih c b hn.2
          have hac : a ≠ c := by
            intro e; apply hn.1; simp [e]
          exact ⟨Walk.cons (show (completeGraph α).Adj a c from hac) hp, by simp [hpe]⟩
      have h2 : 2 < Fintype.card α := by omega
      obtain ⟨u, v, w, huv, huw, hvw⟩ := Fintype.two_lt_card_iff.mp h2
      obtain ⟨l', hmem, hnd⟩ : ∃ l' : List α,
          (∀ x, x ∈ l' ↔ x ≠ u ∧ x ≠ v ∧ x ≠ w) ∧ l'.Nodup :=
        ⟨((Finset.univ : Finset α) \ {u, v, w}).toList, by intro x; simp,
          Finset.nodup_toList _⟩
      have h0 : (w :: u :: l').Nodup := by simp [hmem, hnd, huw.symm]
      have hn1 : (w :: (l' ++ [u])).Nodup := by
        first
          | exact ((List.Perm.cons w (List.perm_append_singleton u l')).nodup_iff).mpr h0
          | simp [List.nodup_append, hmem, hnd, huw.symm]
      have hv : v ∉ w :: (l' ++ [u]) := by simp [hmem, hvw, huv.symm]
      have hn2 : (v :: w :: (l' ++ [u])).Nodup := List.nodup_cons.mpr ⟨hv, hn1⟩
      obtain ⟨r, hr⟩ := key l' w u hn1
      refine ⟨u, Walk.cons (show (completeGraph α).Adj u v from huv)
        (Walk.cons (show (completeGraph α).Adj v w from hvw) r), ?_⟩
      rw [Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
      refine ⟨?_, ?_⟩
      · rw [Walk.cons_isCycle_iff]
        refine ⟨Walk.IsPath.mk' (by rw [Walk.support_cons, hr]; exact hn2), ?_⟩
        intro he
        rw [Walk.edges_cons, List.mem_cons] at he
        rcases he with he | he
        · rw [Sym2.eq_iff] at he
          rcases he with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact huv h1
          · exact huw h1
        · have := Walk.snd_mem_support_of_mem_edges r he
          rw [hr] at this
          exact hv this
      · intro a
        simp only [Walk.support_cons, List.tail_cons, hr]
        apply List.count_eq_one_of_mem hn2
        by_cases hau : a = u
        · simp [hau]
        by_cases hav : a = v
        · simp [hav]
        by_cases haw : a = w
        · simp [haw]
        simp [hmem, hau, hav, haw]
