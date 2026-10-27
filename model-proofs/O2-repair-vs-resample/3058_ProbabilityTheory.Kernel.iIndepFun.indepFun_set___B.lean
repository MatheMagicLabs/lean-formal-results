/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.Kernel.iIndepFun.indepFun_set₀
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Independence/Process/Basic.lean, line 293
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem iIndepFun.indepFun_set₀ {𝓧 : S → Type*} [∀ s, MeasurableSpace (𝓧 s)]
    {X : (s : S) → Ω → 𝓧 s} {I J : Set S} (hIJ : Disjoint I J) (hX : iIndepFun X κ P)
    (mX : ∀ s, AEMeasurable (X s) (κ ∘ₘ P)) :
    IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ X j ω) κ P := by
  obtain rfl | hμ := eq_or_ne P 0
  · simp
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[P] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hX.ae_isProbabilityMeasure hμ
  have h1 : iIndepFun (fun i ω (_ : Unit) ↦ X i ω) κ P :=
    hX.comp (fun i x (_ : Unit) ↦ x) (fun i ↦ measurable_pi_iff.mpr fun _ ↦ measurable_id)
  have h2 : iIndepFun (fun i ω (_ : Unit) ↦ (mX i).mk (X i) ω) κ P :=
    iIndepFun.process_congr (T := fun _ ↦ Unit) (𝓧 := fun i _ ↦ 𝓧 i)
      (X := fun i _ ↦ X i) (X' := fun i _ ↦ (mX i).mk (X i)) h1
      (fun i _ ↦ Measure.ae_ae_of_ae_comp (mX i).ae_eq_mk)
  have h3 : iIndepFun (fun i ↦ (mX i).mk (X i)) κ P :=
    h2.comp (fun i (x : Unit → 𝓧 i) ↦ x ()) (fun i ↦ measurable_pi_apply _)
  refine IndepFun.process_congr (X := fun (i : I) ↦ (mX i).mk (X i))
    (Y := fun (j : J) ↦ (mX j).mk (X j)) ?_
    (fun i ↦ Measure.ae_ae_of_ae_comp (mX i).ae_eq_mk.symm)
    (fun j ↦ Measure.ae_ae_of_ae_comp (mX j).ae_eq_mk.symm)
  refine IndepFun.congr η_eq.symm ?_
  refine IndepFun.process_indepFun_process (fun i ↦ (mX i).measurable_mk)
    (fun j ↦ (mX j).measurable_mk) fun I' J' ↦ ?_
  let A : Finset S := I'.map (Function.Embedding.subtype _)
  let B : Finset S := J'.map (Function.Embedding.subtype _)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 ha
    obtain ⟨y, -, hy⟩ := Finset.mem_map.1 hb
    have hy' : (y : S) = x := hy
    exact Set.disjoint_left.1 hIJ x.2 (hy' ▸ y.2)
  have key := (h3.indepFun_finset A B hAB (fun i ↦ (mX i).measurable_mk)).congr η_eq
  exact key.comp
    (φ := fun (g : (a : A) → 𝓧 a) (i : I') ↦ g ⟨i.1.1, Finset.mem_map_of_mem _ i.2⟩)
    (ψ := fun (g : (b : B) → 𝓧 b) (j : J') ↦ g ⟨j.1.1, Finset.mem_map_of_mem _ j.2⟩)
    (measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _)
    (measurable_pi_iff.mpr fun _ ↦ measurable_pi_apply _)
