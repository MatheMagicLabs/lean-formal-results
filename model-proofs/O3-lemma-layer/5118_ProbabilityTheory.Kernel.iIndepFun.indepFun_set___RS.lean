/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.Kernel.iIndepFun.indepFun_set₀
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Independence/Process/Basic.lean, line 293
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

open MeasureTheory MeasurableSpace Set
namespace ProbabilityTheory
variable {S T Ω : Type*} {mΩ : MeasurableSpace Ω}
namespace Kernel
variable {α : Type*} {mα : MeasurableSpace α} {κ : Kernel α Ω} {P : Measure α}

theorem iIndepFun.indepFun_set₀ {𝓧 : S → Type*} [∀ s, MeasurableSpace (𝓧 s)]
    {X : (s : S) → Ω → 𝓧 s} {I J : Set S} (hIJ : Disjoint I J) (hX : iIndepFun X κ P)
    (mX : ∀ s, AEMeasurable (X s) (κ ∘ₘ P)) :
    IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ X j ω) κ P := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp [Kernel.IndepFun, Kernel.Indep, Kernel.IndepSets]
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[P] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel (iIndep.ae_isProbabilityMeasure hX) hP
  have hc : η ∘ₘ P = κ ∘ₘ P := Measure.bind_congr_right η_eq.symm
  have hXη : iIndepFun X η P := hX.congr η_eq
  have mXη : ∀ s, AEMeasurable (X s) (η ∘ₘ P) := fun s => hc ▸ mX s
  have key : IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ X j ω) η P := by
    refine IndepFun.process_indepFun_process₀ (X := fun (i : I) => X i)
      (Y := fun (j : J) => X j) (fun i => mXη i) (fun j => mXη j) ?_
    intro I' J'
    have hd : Disjoint (I'.map (Function.Embedding.subtype _))
        (J'.map (Function.Embedding.subtype _)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_map, Function.Embedding.coe_subtype] at hx hx'
      obtain ⟨a, -, rfl⟩ := hx
      obtain ⟨b, -, hb⟩ := hx'
      exact Set.disjoint_left.mp hIJ a.2 (hb ▸ b.2)
    have := hXη.indepFun_finset₀ _ _ hd mXη
    exact this.comp (φ := fun f (i : I') => f ⟨i.1.1, Finset.mem_map_of_mem _ i.2⟩)
      (ψ := fun f (j : J') => f ⟨j.1.1, Finset.mem_map_of_mem _ j.2⟩)
      (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
      (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
  unfold IndepFun Indep IndepSets at key ⊢
  intro t1 t2 h1 h2
  filter_upwards [key t1 t2 h1 h2, η_eq] with a ha hκ
  rw [hκ]
  exact ha
