/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.Kernel.iIndepFun.indepFun_set₀
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Independence/Process/Basic.lean, line 293
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 1, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem iIndepFun.indepFun_set₀ {𝓧 : S → Type*} [∀ s, MeasurableSpace (𝓧 s)]
    {X : (s : S) → Ω → 𝓧 s} {I J : Set S} (hIJ : Disjoint I J) (hX : iIndepFun X κ P)
    (mX : ∀ s, AEMeasurable (X s) (κ ∘ₘ P)) :
    IndepFun (fun ω (i : I) ↦ X i ω) (fun ω (j : J) ↦ X j ω) κ P := by
  classical
  obtain rfl | hμ := eq_or_ne P 0
  · first
      | simp
      | (rintro _ _ _ _; simp)
  obtain ⟨X', hX'm, hae⟩ : ∃ X' : (s : S) → Ω → 𝓧 s, (∀ s, Measurable (X' s)) ∧
      ∀ s, ∀ᵐ a ∂P, X s =ᵐ[κ a] X' s :=
    ⟨fun s ↦ (mX s).mk (X s), fun s ↦ (mX s).measurable_mk,
      fun s ↦ Measure.ae_ae_of_ae_comp (mX s).ae_eq_mk⟩
  have hae' : ∀ s, ∀ᵐ a ∂P, X' s =ᵐ[κ a] X s := fun s ↦ (hae s).mono fun a h ↦ h.symm
  have hind : iIndepFun (fun s ω (_ : Unit) ↦ X' s ω) κ P := by
    refine iIndepFun.process_congr (X := fun s (_ : Unit) ↦ X s)
      (X' := fun s (_ : Unit) ↦ X' s) ?_ (fun s _ ↦ hae s)
    exact hX.comp (fun s (x : 𝓧 s) (_ : Unit) ↦ x)
      (fun s ↦ measurable_pi_iff.2 fun _ ↦ measurable_id)
  have hind' : iIndepFun X' κ P :=
    hind.comp (fun s (u : Unit → 𝓧 s) ↦ u ()) (fun s ↦ measurable_pi_apply ())
  refine IndepFun.process_congr (𝓧 := fun i : I ↦ 𝓧 i) (𝓨 := fun j : J ↦ 𝓧 j)
    (X := fun (i : I) ↦ X' i) (X' := fun (i : I) ↦ X i)
    (Y := fun (j : J) ↦ X' j) (Y' := fun (j : J) ↦ X j) ?_ (fun i ↦ hae' i) (fun j ↦ hae' j)
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[P] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hind'.ae_isProbabilityMeasure hμ
  apply IndepFun.congr (Filter.EventuallyEq.symm η_eq)
  have hη' : iIndepFun X' η P := hind'.congr η_eq
  refine IndepFun.process_indepFun_process (fun i : I ↦ hX'm i) (fun j : J ↦ hX'm j)
    fun I' J' ↦ ?_
  have hAB : Disjoint (I'.image Subtype.val) (J'.image Subtype.val) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_image] at hxA hxB
    obtain ⟨a, -, rfl⟩ := hxA
    obtain ⟨b, -, hb⟩ := hxB
    exact Set.disjoint_left.1 hIJ a.2 (by rw [← hb]; exact b.2)
  have h := hη'.indepFun_finset (I'.image Subtype.val) (J'.image Subtype.val) hAB
    (fun i ↦ hX'm i)
  exact h.comp
    (φ := fun (u : (i : (I'.image Subtype.val)) → 𝓧 i) (i : I') ↦
      u ⟨i.1.1, Finset.mem_image.2 ⟨i.1, i.2, rfl⟩⟩)
    (ψ := fun (u : (i : (J'.image Subtype.val)) → 𝓧 i) (j : J') ↦
      u ⟨j.1.1, Finset.mem_image.2 ⟨j.1, j.2, rfl⟩⟩)
    (measurable_pi_iff.2 fun i ↦ measurable_pi_apply _)
    (measurable_pi_iff.2 fun j ↦ measurable_pi_apply _)
