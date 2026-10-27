/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     PiTensorProduct.ext_of_span_eq_top
Source:      Mathlib @ d0a050ad6, Mathlib/LinearAlgebra/PiTensorProduct/Generators.lean, line 129
             (added after the model's training data; human proof 32 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 1 call(s)
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
  let f := φ.compMultilinearMap (tprod R)
  let f' := φ'.compMultilinearMap (tprod R)
  suffices H : ∀ (s : Finset ι) (m : ∀ i, M i), (∀ i, i ∉ s → m i ∈ Set.range (@g i)) → f m = f' m by
    apply PiTensorProduct.ext; apply MultilinearMap.ext; intro m; exact H Finset.univ m (by simp)
  intro s
  induction s using Finset.induction_on with
  | empty => intro m hm; have hm' : ∀ i, ∃ j, g j = m i := fun i ↦ hm i (by simp); choose j hj using hm'; have he : m = fun i ↦ g (j i) := funext fun i ↦ (hj i).symm; rw [he]; exact h j
  | @insert i s hi ih => intro m hm; have he : f.toLinearMap m i = f'.toLinearMap m i := LinearMap.ext_on_range (hg i) (fun j ↦ ih (Function.update m i (g j)) (fun k hk ↦ by by_cases hki : k = i; subst k; simpa using (Set.mem_range_self j : g j ∈ Set.range (@g i)); simpa [Function.update_of_ne hki] using hm k (by simp [hk, hki]))); simpa [MultilinearMap.toLinearMap] using LinearMap.congr_fun he (m i)
