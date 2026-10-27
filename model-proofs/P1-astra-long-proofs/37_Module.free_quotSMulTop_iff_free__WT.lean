/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Module.free_quotSMulTop_iff_free
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/Regular/Free.lean, line 34
             (added after the model's training data; human proof 29 tactic steps)
Experiment:  P1-astra-long-proofs, arm WT, solved after 4 call(s)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium), at most 10 calls per theorem: W = whole proof plus repair rounds;
             WT = W with read-only Mathlib sources to search; P = Lean-checked skeleton of have-steps, then one step per call
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`.
-/

lemma Module.free_quotSMulTop_iff_free [Module.FinitePresentation R M] {x : R}
    (mem : x ∈ (⊥ : Ideal R).jacobson) (reg : IsSMulRegular M x) :
    Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) ↔ Module.Free R M := by
  classical
  constructor
  swap
  · intro h; infer_instance
  intro h
  letI := h
  let I : Ideal R := Ideal.span {x}
  let S := R ⧸ I
  let Q := QuotSMulTop x M
  letI : Module.Finite S Q := Module.Finite.of_restrictScalars_finite R S Q
  let ι := Module.Free.ChooseBasisIndex S Q
  let b := Module.Free.chooseBasis S Q
  let q : M →ₗ[R] Q := (x • (⊤ : Submodule R M)).mkQ
  obtain ⟨v, hv⟩ : ∃ v : ι → M, ∀ i, q (v i) = b i := by exact Classical.axiomOfChoice (fun i ↦ Submodule.mkQ_surjective _ (b i))
  let f : (ι →₀ R) →ₗ[R] M := Finsupp.linearCombination R v
  let g : (ι →₀ R) →ₗ[R] (ι →₀ S) := Finsupp.mapRange.linearMap I.mkQ
  have hg : Function.Surjective g := Finsupp.mapRange_surjective I.mkQ (map_zero I.mkQ) I.mkQ_surjective
  have hc : q ∘ₗ f = (b.repr.symm.toLinearMap.restrictScalars R) ∘ₗ g := by apply Finsupp.lhom_ext; intro i r; change q (f (Finsupp.single i r)) = b.repr.symm (g (Finsupp.single i r)); simp only [f, Finsupp.linearCombination_single, map_smul, hv, g, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Basis.repr_symm_single]; exact (IsScalarTower.algebraMap_smul S r (b i)).symm
  have hqf : Function.Surjective (q ∘ₗ f) := by rw [hc]; exact b.repr.symm.surjective.comp hg
  have hI : I ≤ (⊥ : Ideal R).jacobson := (Ideal.span_singleton_le_iff_mem _).mpr mem
  have hf : Function.Surjective f := by apply LinearMap.surjective_of_surjective_comp_mkQ f I hI; have he : I • (⊤ : Submodule R M) = x • ⊤ := Submodule.ideal_span_singleton_smul x _; rw [he]; exact hqf
  have hsub := Finsupp.submodule_smul R ι (fun _ ↦ (⊤ : Submodule R R)) I
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Finsupp.submodule_top] at hsub
  have hk : LinearMap.ker g = x • (⊤ : Submodule R (ι →₀ R)) := by change LinearMap.ker (Finsupp.mapRange.linearMap I.mkQ) = _; rw [Finsupp.ker_mapRange, Submodule.ker_mkQ, hsub]; exact Submodule.ideal_span_singleton_smul x _
  have hfg : LinearMap.ker f ≤ LinearMap.ker g := by intro y hy; change f y = 0 at hy; change g y = 0; apply b.repr.symm.injective; have he := LinearMap.congr_fun hc y; simpa [hy] using he.symm
  have hle : LinearMap.ker f ≤ I • LinearMap.ker f := by change LinearMap.ker f ≤ Ideal.span {x} • LinearMap.ker f; rw [Submodule.ideal_span_singleton_smul]; intro y hy; have hy' := hfg hy; rw [hk, Submodule.mem_smul_pointwise_iff_exists] at hy'; obtain ⟨z, _, hz⟩ := hy'; apply (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr; refine ⟨z, ?_, hz⟩; change f z = 0; apply reg.right_eq_zero_of_smul; rw [← map_smul, hz]; exact hy
  have hker : LinearMap.ker f = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I (LinearMap.ker f) (Module.FinitePresentation.fg_ker f hf) hle hI
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨LinearMap.ker_eq_bot.mp hker, hf⟩)
