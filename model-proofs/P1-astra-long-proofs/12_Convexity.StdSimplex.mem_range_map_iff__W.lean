/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Convexity.StdSimplex.mem_range_map_iff
Source:      Mathlib @ d0a050ad6, Mathlib/Geometry/Convex/ConvexSpace/Defs.lean, line 220
             (added after the model's training data; human proof 33 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 2 call(s)
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
  constructor
  · rintro ⟨t, rfl⟩ y hy; have h : ∀ x, f x ≠ y := fun x hx => hy ⟨x, hx⟩; simp [map, Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.single_apply, h]
  · {
  intro hs
  have hex : ∀ y, s.weights y ≠ 0 → ∃ x, f x = y := fun y hy => by { by_contra h; exact hy (hs y h) }
  obtain ⟨y, hy⟩ := s.support_weights_nonempty
  obtain ⟨x₀, _⟩ := hex y (Finsupp.mem_support_iff.mp hy)
  let g : Y → X := fun y => if h : ∃ x, f x = y then Classical.choose h else x₀
  have hg : ∀ y, s.weights y ≠ 0 → f (g y) = y := by { intro y hy; dsimp [g]; rw [dif_pos (hex y hy)]; exact Classical.choose_spec (hex y hy) }
  refine ⟨s.map g, ?_⟩
  rw [map_map]
  apply StdSimplex.ext
  change s.weights.mapDomain (fun y => f (g y)) = s.weights
  have he : s.weights.mapDomain (fun y => f (g y)) = s.weights.mapDomain id := by {
  unfold Finsupp.mapDomain
  apply Finset.sum_congr rfl
  intro y hy
  change Finsupp.single (f (g y)) (s.weights y) = Finsupp.single y (s.weights y)
  rw [hg y (Finsupp.mem_support_iff.mp hy)]
  }
  simpa using he
  }
