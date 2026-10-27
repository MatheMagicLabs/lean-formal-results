/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Module.free_quotSMulTop_iff_free
Source:      Mathlib @ d0a050ad6, Mathlib/RingTheory/Regular/Free.lean, line 34
             (added after the model's training data; human proof 29 tactic steps)
Experiment:  P1-astra-long-proofs, arm W, solved after 1 call(s)
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
  refine ⟨fun free ↦ ?_,fun free ↦ inferInstance⟩
  have := Module.Finite.of_restrictScalars_finite R (R⧸Ideal.span {x}) (QuotSMulTop x M)
  let I := Module.Free.ChooseBasisIndex (R⧸Ideal.span {x}) (QuotSMulTop x M)
  let b := Module.Free.chooseBasis (R⧸Ideal.span {x}) (QuotSMulTop x M)
  let b': QuotSMulTop x M≃ₗ[R]I→₀R⧸Ideal.span {x} := b.1.restrictScalars R
  let f := b'.symm.toLinearMap.comp (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x})))
  obtain ⟨g,hg⟩ := Module.projective_lifting_property (Submodule.mkQ (x•(⊤:Submodule R M))) f (Submodule.mkQ_surjective _)
  have surjf: Function.Surjective f := by simpa [f] using! Finsupp.mapRange_surjective _ rfl (Submodule.mkQ_surjective (Ideal.span {x}))
  have lejac: Ideal.span {x}≤(⊥:Ideal R).jacobson := by simpa
  have surjg: Function.Surjective g := by apply g.surjective_of_surjective_comp_mkQ (Ideal.span {x}) lejac; rwa [Submodule.ideal_span_singleton_smul x ⊤,hg]
  have kerf: LinearMap.ker f=x•(⊤:Submodule R (I→₀R)) := by simp only [LinearEquiv.ker_comp,f]; rw [Finsupp.ker_mapRange,Submodule.ker_mkQ,← (Ideal.span {x}).mul_top,← smul_eq_mul,Finsupp.submodule_smul]; simp [Submodule.ideal_span_singleton_smul]
  suffices injg: Function.Injective g from Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨injg,surjg⟩)
  rw [← LinearMap.ker_eq_bot]
  apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _ (Module.FinitePresentation.fg_ker g surjg) _ lejac
  rw [Submodule.ideal_span_singleton_smul]
  intro y hy
  have h: y∈x•(⊤:Submodule R (I→₀R)) := by simp [← kerf,← hg,LinearMap.mem_ker.mp hy]
  obtain ⟨z,_,hz⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h
  simp only [← hz,LinearMap.mem_ker,map_smul] at hy
  have := LinearMap.mem_ker.mpr (IsSMulRegular.right_eq_zero_of_smul reg hy)
  simpa [hz] using Submodule.smul_mem_pointwise_smul z x _ this
