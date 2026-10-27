/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.Kernel.iIndepFun.indepFun_set₀
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Independence/Process/Basic.lean, line 293
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm A, attempt 0, verified in round 0 (round 0 = first attempt)
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
  · first | simp | (intro _ _ _ _; simp)
  obtain ⟨η, η_eq, hη⟩ : ∃ (η : Kernel α Ω), κ =ᵐ[P] η ∧ IsMarkovKernel η :=
    exists_ae_eq_isMarkovKernel hX.ae_isProbabilityMeasure hμ
  have hXY : ∀ s, ∀ᵐ a ∂P, X s =ᵐ[κ a] (mX s).mk (X s) :=
    fun s ↦ Measure.ae_ae_of_ae_comp (mX s).ae_eq_mk
  have h1 : iIndepFun (fun s ω (_ : Unit) ↦ X s ω) κ P :=
    hX.comp (fun s (x : 𝓧 s) (_ : Unit) ↦ x)
      (fun s ↦ measurable_pi_iff.2 fun _ ↦ measurable_id)
  have h2 : iIndepFun (fun s ω (_ : Unit) ↦ (mX s).mk (X s) ω) κ P :=
    iIndepFun.process_congr (T := fun _ ↦ Unit) (X := fun s _ ↦ X s)
      (X' := fun s _ ↦ (mX s).mk (X s)) h1 (fun s _ ↦ hXY s)
  have h3 : iIndepFun (fun s ↦ (mX s).mk (X s)) κ P :=
    h2.comp (fun s (f : Unit → 𝓧 s) ↦ f ()) (fun s ↦ measurable_pi_apply ())
  have h3' := h3.congr η_eq
  let eI : I ↪ S := ⟨Subtype.val, Subtype.val_injective⟩
  let eJ : J ↪ S := ⟨Subtype.val, Subtype.val_injective⟩
  have key : IndepFun (fun ω (i : I) ↦ (mX i).mk (X i) ω)
      (fun ω (j : J) ↦ (mX j).mk (X j) ω) η P := by
    refine IndepFun.process_indepFun_process (κ := η)
      (X := fun (i : I) ↦ (mX i).mk (X i)) (Y := fun (j : J) ↦ (mX j).mk (X j))
      (fun i ↦ (mX i).measurable_mk) (fun j ↦ (mX j).measurable_mk) fun A B ↦ ?_
    have hd : Disjoint (A.map eI) (B.map eJ) := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      have hxI : x ∈ I := by
        obtain ⟨a, -, rfl⟩ := Finset.mem_map.1 hxA
        exact a.2
      have hxJ : x ∈ J := by
        obtain ⟨b, -, rfl⟩ := Finset.mem_map.1 hxB
        exact b.2
      exact Set.disjoint_left.1 hIJ hxI hxJ
    have hind := h3'.indepFun_finset (A.map eI) (B.map eJ) hd
      (fun i ↦ (mX i).measurable_mk)
    have hφ : Measurable (fun (f : ∀ i : A.map eI, 𝓧 i.1) (a : A) ↦
        f ⟨a.1.1, Finset.mem_map.2 ⟨a.1, a.2, rfl⟩⟩) :=
      measurable_pi_iff.2 fun a ↦ measurable_pi_apply _
    have hψ : Measurable (fun (f : ∀ i : B.map eJ, 𝓧 i.1) (b : B) ↦
        f ⟨b.1.1, Finset.mem_map.2 ⟨b.1, b.2, rfl⟩⟩) :=
      measurable_pi_iff.2 fun b ↦ measurable_pi_apply _
    exact hind.comp hφ hψ
  have key' : IndepFun (fun ω (i : I) ↦ (mX i).mk (X i) ω)
      (fun ω (j : J) ↦ (mX j).mk (X j) ω) κ P :=
    key.congr η_eq.symm
  exact IndepFun.process_congr (X := fun (i : I) ↦ (mX i).mk (X i)) (X' := fun (i : I) ↦ X i)
    (Y := fun (j : J) ↦ (mX j).mk (X j)) (Y' := fun (j : J) ↦ X j) key'
    (fun i ↦ (hXY i).mono fun a ha ↦ ha.symm) (fun j ↦ (hXY j).mono fun a ha ↦ ha.symm)
