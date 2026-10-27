/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Convexity.StdSimplex.mem_range_map_iff
Source:      Mathlib @ d0a050ad6, Mathlib/Geometry/Convex/ConvexSpace/Defs.lean, line 220
             (added after the model's training data; human proof 33 tactic steps)
Experiment:  P1-astra-long-proofs, arm P, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma mem_range_map_iff
    (f : X → Y) (s : StdSimplex R Y) :
    s ∈ Set.range (map f) ↔ ∀ (x : Y), x ∉ Set.range f → s.weights x = 0 := by
  classical
  have hMap : ∀ (t : StdSimplex R X) (y : Y), y ∉ Set.range f → (t.map f).weights y = 0 := by
    intro t y hy
    have h : ∀ x : X, f x ≠ y := fun x hx ↦ hy ⟨x, hx⟩
    change (t.weights.mapDomain f) y = 0
    simp [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply, h]
  have hLift : (∀ y ∈ s.weights.support, y ∈ Set.range f) → ∃ t : StdSimplex R X, t.map f = s := by
    intro h
    obtain ⟨y, hy⟩ := s.support_weights_nonempty
    obtain ⟨x, hx⟩ := h y hy
    let g : Y → X := fun y ↦ if hy : y ∈ Set.range f then Classical.choose hy else x
    have hg : ∀ y ∈ s.weights.support, f (g y) = y := by
      intro y hy
      dsimp [g]
      rw [dif_pos (h y hy)]
      exact Classical.choose_spec (h y hy)
    refine ⟨s.map g, ?_⟩
    rw [map_map]
    apply StdSimplex.ext
    change s.weights.mapDomain (fun y ↦ f (g y)) = s.weights
    calc
      s.weights.mapDomain (fun y ↦ f (g y)) = s.weights.mapDomain id := by
        simp only [Finsupp.mapDomain, Finsupp.sum]
        apply Finset.sum_congr rfl
        intro y hy
        rw [hg y hy]
        rfl
      _ = s.weights := by simp
  refine ⟨?_, ?_⟩
  · rintro ⟨t, rfl⟩; exact hMap t
  · intro h; apply hLift; intro y hy; by_contra hn; exact (Finsupp.mem_support_iff.mp hy) (h y hn)
