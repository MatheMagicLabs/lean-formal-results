/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     PiTensorProduct.ext_of_span_eq_top
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/PiTensorProduct/Generators.lean, line 129
             (added after the model's training data; human proof 32 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 1 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma ext_of_span_eq_top
    (hg : ∀ i, Submodule.span R (Set.range (@g i)) = ⊤)
    {φ φ' : (⨂[R] i, M i) →ₗ[R] N}
    (h : ∀ (j : (i : ι) → γ i),
      φ (tprod _ (fun i ↦ g (j i))) = φ' (tprod _ (fun i ↦ g (j i)))) :
    φ = φ' := by
  classical
  letI := Fintype.ofFinite ι
  let F : MultilinearMap R M N := φ.compMultilinearMap (tprod R)
  let F' : MultilinearMap R M N := φ'.compMultilinearMap (tprod R)
  have hs : ∀ s : Finset ι, ∀ m : ∀ i, M i,
      (∀ i, i ∉ s → m i ∈ Set.range (@g i)) → F m = F' m := by {
  intro s
  induction s using Finset.induction_on with
  | empty => {
  intro m hm
  have hm' : ∀ i, ∃ j, g j = m i := fun i => hm i (by simp)
  choose j hj using hm'
  simpa only [F, F', LinearMap.compMultilinearMap_apply, hj] using h j
  }
  | @insert i s hi ih => {
  intro m hm
  have aux : ∀ x, x ∈ Submodule.span R (Set.range (@g i)) →
      F (Function.update m i x) = F' (Function.update m i x) := by {
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => {
  apply ih
  intro k hk
  by_cases hki : k = i
  · subst k; simpa using hx
  · simpa [Function.update, hki] using hm k (by simp [hki, hk])
  }
  | zero => { simp }
  | add x y hx hy ex ey => {
  rw [F.map_update_add, F'.map_update_add, ex, ey]
  }
  | smul a x hx ex => {
  rw [F.map_update_smul, F'.map_update_smul, ex]
  }
  }
  have hx : m i ∈ Submodule.span R (Set.range (@g i)) := by {
  rw [hg i]
  trivial
  }
  simpa using aux (m i) hx
  }
  }
  have hF : F = F' := by {
  ext m
  exact hs Finset.univ m (by simp)
  }
  apply PiTensorProduct.ext
  first
  | exact hF
  | exact fun m => congrArg (fun f : MultilinearMap R M N => f m) hF
