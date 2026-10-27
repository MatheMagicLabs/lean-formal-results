/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.Kernel.iIndepFun.indepFun_set₀
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Independence/Process/Basic.lean, line 293
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 1 (round 0 = first attempt)
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
  obtain ⟨X', hXX', hX'm⟩ : ∃ X' : (s : S) → Ω → 𝓧 s, (∀ s, ∀ᵐ a ∂P, X s =ᵐ[κ a] X' s) ∧
      ∀ s, Measurable (X' s) :=
    ⟨fun s => (mX s).mk (X s), fun s => Measure.ae_ae_of_ae_comp (mX s).ae_eq_mk,
      fun s => (mX s).measurable_mk⟩
  have h1 : iIndepFun (fun (s : S) ω (_ : Unit) ↦ X s ω) κ P :=
    hX.comp (fun s (x : 𝓧 s) (_ : Unit) => x)
      (fun s => measurable_pi_iff.2 fun _ => measurable_id)
  have h2 : iIndepFun (fun (s : S) ω (_ : Unit) ↦ X' s ω) κ P :=
    iIndepFun.process_congr (T := fun _ => Unit) (X := fun s (_ : Unit) => X s)
      (X' := fun s (_ : Unit) => X' s) h1 (fun s _ => hXX' s)
  have h3 : iIndepFun X' κ P :=
    h2.comp (fun s (f : Unit → 𝓧 s) => f ()) (fun s => measurable_pi_apply _)
  have h4 : IndepFun (fun ω (i : I) ↦ X' i ω) (fun ω (j : J) ↦ X' j ω) κ P := by
    rcases eq_or_ne P 0 with hP | hP
    · subst hP
      simp
    obtain ⟨η, η_eq, hη⟩ := exists_ae_eq_isMarkovKernel hX.ae_isProbabilityMeasure hP
    apply IndepFun.congr η_eq.symm
    refine IndepFun.process_indepFun_process (X := fun (i : I) => X' i)
      (Y := fun (j : J) => X' j) (fun i => hX'm i) (fun j => hX'm j) ?_
    intro I' J'
    have hAB : Disjoint (I'.map (Function.Embedding.subtype _))
        (J'.map (Function.Embedding.subtype _)) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 ha
      obtain ⟨j, -, hj⟩ := Finset.mem_map.1 hb
      have hj' : ((j : J) : S) = ((i : I) : S) := hj
      exact Set.disjoint_left.1 hIJ i.2 (by rw [← hj']; exact j.2)
    have h := (h3.congr η_eq).indepFun_finset _ _ hAB hX'm
    have hA : ∀ i : I', ((i : I) : S) ∈ I'.map (Function.Embedding.subtype _) :=
      fun i => Finset.mem_map_of_mem (Function.Embedding.subtype _) i.2
    have hB : ∀ j : J', ((j : J) : S) ∈ J'.map (Function.Embedding.subtype _) :=
      fun j => Finset.mem_map_of_mem (Function.Embedding.subtype _) j.2
    have hφ : Measurable (fun (x : (a : I'.map (Function.Embedding.subtype _)) → 𝓧 a)
        (i : I') => x ⟨i.1.1, hA i⟩) :=
      measurable_pi_iff.2 fun _ => measurable_pi_apply _
    have hψ : Measurable (fun (x : (a : J'.map (Function.Embedding.subtype _)) → 𝓧 a)
        (j : J') => x ⟨j.1.1, hB j⟩) :=
      measurable_pi_iff.2 fun _ => measurable_pi_apply _
    exact h.comp hφ hψ
  exact IndepFun.process_congr (X := fun (i : I) => X' i) (X' := fun (i : I) => X i)
    (Y := fun (j : J) => X' j) (Y' := fun (j : J) => X j) h4
    (fun i => (hXX' i).mono fun a h => h.symm) (fun j => (hXX' j).mono fun a h => h.symm)
