/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_pos_of_mem_minimalPrimes
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem ramificationIdx_pos_of_mem_minimalPrimes [q.LiesOver p] [q.IsPrime]
    (hq : q ∈ (p.map (algebraMap R S)).minimalPrimes)
    [IsNoetherianRing (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))] :
    0 < q.ramificationIdx R := by
  rw [ramificationIdx_eq p q]
  have hpq : p.map (algebraMap R S) ≤ q := hq.1.2
  have hImax : p.map (algebraMap R (Localization.AtPrime q)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal,
      IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map]
    exact Ideal.map_mono hpq
  have hI : p.map (algebraMap R (Localization.AtPrime q)) ≠ ⊤ := fun h =>
    (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime q)).ne_top
      (top_le_iff.mp (h ▸ hImax))
  have hnt : Nontrivial
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
    first
      | exact Ideal.Quotient.nontrivial_iff.mpr hI
      | exact Ideal.Quotient.nontrivial hI
      | exact Submodule.Quotient.nontrivial_of_lt_top _ hI.lt_top
  have hdim : Ring.KrullDimLE 0
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
    have key : ∀ J : Ideal (Localization.AtPrime q ⧸
        p.map (algebraMap R (Localization.AtPrime q))), J.IsPrime → J.IsMaximal := by
      intro J hJ
      set J1 := J.comap (Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime q))))
      have hJ1 : J1.IsPrime := Ideal.comap_isPrime _ _
      set J2 := J1.comap (algebraMap S (Localization.AtPrime q))
      have hJ2 : J2.IsPrime := Ideal.comap_isPrime _ _
      have hIJ1 : p.map (algebraMap R (Localization.AtPrime q)) ≤ J1 := fun x hx => by
        show Ideal.Quotient.mk _ x ∈ J
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact J.zero_mem
      have hpJ2 : p.map (algebraMap R S) ≤ J2 := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        show Ideal.Quotient.mk _ (algebraMap S (Localization.AtPrime q) (algebraMap R S x)) ∈ J
        rw [← IsScalarTower.algebraMap_apply]
        exact hIJ1 (Ideal.mem_map_of_mem _ hx)
      have hJ2q : J2 ≤ q := by
        intro x hx
        by_contra hxq
        exact hJ1.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
          (IsLocalization.map_units (Localization.AtPrime q) (⟨x, hxq⟩ : q.primeCompl)))
      have hJ2eq : J2 = q := le_antisymm hJ2q (hq.2 ⟨hJ2, hpJ2⟩ hJ2q)
      have hJ1eq : J1 = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
        refine le_antisymm (IsLocalRing.le_maximalIdeal hJ1.ne_top) ?_
        rw [← Localization.AtPrime.map_eq_maximalIdeal]
        exact (congrArg (Ideal.map (algebraMap S (Localization.AtPrime q))) hJ2eq.symm).trans_le
          Ideal.map_comap_le
      have hJ1max : J1.IsMaximal := by rw [hJ1eq]; infer_instance
      have hJmap : J1.map (Ideal.Quotient.mk
          (p.map (algebraMap R (Localization.AtPrime q)))) = J :=
        Ideal.map_comap_of_surjective
          (Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime q))))
          Ideal.Quotient.mk_surjective J
      rcases Ideal.map_eq_top_or_isMaximal_of_surjective
          (Ideal.Quotient.mk (p.map (algebraMap R (Localization.AtPrime q))))
          Ideal.Quotient.mk_surjective hJ1max with h | h
      · exact absurd (hJmap ▸ h) hJ.ne_top
      · exact hJmap ▸ h
    first
      | exact Ring.KrullDimLE.mk₀ key
      | exact Ring.krullDimLE_zero_iff.mpr key
  have hart : IsArtinianRing
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
    first
      | exact isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨inferInstance, hdim⟩
      | exact IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  let f : Submodule (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) →
      Submodule (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := fun N =>
    { carrier := N
      add_mem' := fun ha hb => N.add_mem ha hb
      zero_mem' := N.zero_mem
      smul_mem' := fun c x hx => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
        convert N.smul_mem a hx using 1
        first
          | rfl
          | (rw [Algebra.smul_def]; rfl)
          | (obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x; rfl)
          | simp [Algebra.smul_def] }
  have hf : StrictMono f := fun N M h =>
    SetLike.coe_ssubset_coe.mp
      (SetLike.coe_ssubset_coe.mpr h : (N : Set (Localization.AtPrime q ⧸
        p.map (algebraMap R (Localization.AtPrime q)))) ⊂ M)
  haveI hgt : WellFoundedGT (Submodule
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))) := by
    first
      | exact isNoetherian_iff'.mp inferInstance
      | infer_instance
  haveI hlt : WellFoundedLT (Submodule
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))) := by
    first
      | exact hart
      | infer_instance
  have h1 : IsArtinian (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
    first
      | exact hf.wellFoundedLT
      | exact ⟨Subrelation.wf (fun {a b} h => hf h) (InvImage.wf f wellFounded_lt)⟩
      | exact (isArtinian_iff _ _).mpr
          (Subrelation.wf (fun {a b} h => hf h) (InvImage.wf f wellFounded_lt))
  have h2 : IsNoetherian (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
    first
      | exact isNoetherian_iff'.mpr hf.wellFoundedGT
      | exact isNoetherian_iff'.mpr
          ⟨Subrelation.wf (fun {a b} h => hf h) (InvImage.wf f wellFounded_gt)⟩
      | exact isNoetherian_iff.mpr
          (Subrelation.wf (fun {a b} h => hf h) (InvImage.wf f wellFounded_gt))
  have hne : Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨h2, h1⟩)
  have hpos : 0 < Module.length (Localization.AtPrime q)
      (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q))) := by
    first
      | exact Module.length_pos
      | exact Module.length_pos_iff.mpr hnt
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hpos ⊢
  rw [ENat.toNat_coe]
  exact_mod_cast hpos
