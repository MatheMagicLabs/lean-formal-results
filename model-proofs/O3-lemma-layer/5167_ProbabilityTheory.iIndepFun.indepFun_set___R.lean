/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ProbabilityTheory.iIndepFun.indepFun_set₀
Source:      Mathlib @ a02a63c2, Mathlib/Probability/Independence/Process/Basic.lean, line 442
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm R, verified in round 1 (round 0 = first attempt)
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
end Kernel
variable {P : Measure Ω}

theorem iIndepFun.indepFun_set₀ {𝓧 : S → Type*} [∀ s, MeasurableSpace (𝓧 s)]
    {X : (s : S) → Ω → 𝓧 s} {I J : Set S} (hIJ : Disjoint I J) (hX : iIndepFun X P)
    (mX : ∀ s, AEMeasurable (X s) P) :
    (fun ω (i : I) ↦ X i ω) ⟂ᵢ[P] (fun ω (j : J) ↦ X j ω) := by
  classical
  have hex : ∀ s, ∃ g : Ω → 𝓧 s, Measurable g ∧ X s =ᵐ[P] g := fun s ↦ mX s
  choose Y hYm hXY using hex
  have hY : iIndepFun Y P := hX.congr hXY
  have h1 : iIndep (fun s ↦ MeasurableSpace.comap (Y s) inferInstance) P := by
    first
      | exact hY
      | exact iIndepFun_iff_iIndep.1 hY
  have hInd := indep_iSup_of_disjoint
    (m := fun s ↦ MeasurableSpace.comap (Y s) inferInstance) (fun s ↦ (hYm s).comap_le) h1 hIJ
  have hInd' : ∀ t1 t2, MeasurableSet[⨆ i ∈ I, MeasurableSpace.comap (Y i) inferInstance] t1 →
      MeasurableSet[⨆ j ∈ J, MeasurableSpace.comap (Y j) inferInstance] t2 →
      P (t1 ∩ t2) = P t1 * P t2 := by
    first
      | exact (Indep_iff _ _ _).1 hInd
      | exact (indep_iff _ _ _).1 hInd
      | exact Indep_iff.1 hInd
      | exact indep_iff.1 hInd
      | exact fun t1 t2 h1 h2 ↦ hInd.measure_inter_eq_mul h1 h2
  have key : ∀ K : Set S, ∀ t, MeasurableSet[MeasurableSpace.comap
      (fun ω (i : K) ↦ X i ω) MeasurableSpace.pi] t →
      ∃ u, MeasurableSet[⨆ i ∈ K, MeasurableSpace.comap (Y i) inferInstance] u ∧ t =ᵐ[P] u := by
    intro K
    let M : MeasurableSpace Ω :=
      { MeasurableSet' := fun t ↦ ∃ u, MeasurableSet[⨆ i ∈ K,
            MeasurableSpace.comap (Y i) inferInstance] u ∧ t =ᵐ[P] u
        measurableSet_empty := ⟨∅, @MeasurableSet.empty _
            (⨆ i ∈ K, MeasurableSpace.comap (Y i) inferInstance), Filter.EventuallyEq.rfl⟩
        measurableSet_compl := fun t ⟨u, hu, htu⟩ ↦
          ⟨uᶜ, (⨆ i ∈ K, MeasurableSpace.comap (Y i) inferInstance).measurableSet_compl u hu,
            htu.compl⟩
        measurableSet_iUnion := fun f hf ↦ by
          choose u hu hfu using hf
          exact ⟨⋃ n, u n,
            (⨆ i ∈ K, MeasurableSpace.comap (Y i) inferInstance).measurableSet_iUnion u hu,
            EventuallyEq.countable_iUnion hfu⟩ }
    have hle : MeasurableSpace.comap (fun ω (i : K) ↦ X i ω) MeasurableSpace.pi ≤ M := by
      rw [MeasurableSpace.comap_le_iff_le_map]
      refine iSup_le fun i ↦ ?_
      rintro s ⟨B, hB, rfl⟩
      refine ⟨Y i ⁻¹' B, ?_, ?_⟩
      · exact le_iSup₂ (f := fun (j : S) (_ : j ∈ K) ↦
          MeasurableSpace.comap (Y j) inferInstance) i.1 i.2 _ ⟨B, hB, rfl⟩
      · first
          | exact (hXY i).preimage B
          | exact Filter.EventuallyEq.preimage (hXY i) B
    exact fun t ht ↦ hle t ht
  show Indep (MeasurableSpace.comap (fun ω (i : I) ↦ X i ω) MeasurableSpace.pi)
    (MeasurableSpace.comap (fun ω (j : J) ↦ X j ω) MeasurableSpace.pi) P
  first
    | rw [Indep_iff]
    | rw [indep_iff]
  intro t1 t2 ht1 ht2
  obtain ⟨u1, hu1, h1'⟩ := key I t1 ht1
  obtain ⟨u2, hu2, h2'⟩ := key J t2 ht2
  rw [measure_congr (h1'.inter h2'), measure_congr h1', measure_congr h2']
  exact hInd' u1 u2 hu1 hu2
