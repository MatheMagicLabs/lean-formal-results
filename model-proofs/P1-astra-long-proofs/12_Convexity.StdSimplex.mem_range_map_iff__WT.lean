/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Convexity.StdSimplex.mem_range_map_iff
Source:      Mathlib @ d0a050ad6, Mathlib/Geometry/Convex/ConvexSpace/Defs.lean, line 220
             (added after the model's training data; human proof 33 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
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
  · rintro ⟨t, rfl⟩ x hx
    exact Finsupp.mapDomain_of_notMem_range t.weights x hx
  · intro h
    have hs : ∀ y ∈ s.weights.support, y ∈ Set.range f := by
      intro y hy
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hy) (h y hn)
    obtain ⟨y, hy⟩ := s.support_weights_nonempty
    letI : Nonempty X := ⟨Classical.choose (hs y hy)⟩
    refine ⟨s.map (Function.invFun f), ?_⟩
    rw [map_map]
    apply StdSimplex.ext
    change s.weights.mapDomain (fun y ↦ f (Function.invFun f y)) = s.weights
    exact (Finsupp.mapDomain_congr (fun y hy ↦ Function.invFun_eq (hs y hy))).trans
      (Finsupp.mapDomain_id)
