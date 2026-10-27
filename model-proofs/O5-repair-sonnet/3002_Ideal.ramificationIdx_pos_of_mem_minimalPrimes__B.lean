/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Ideal.ramificationIdx_pos_of_mem_minimalPrimes
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/RamificationInertia/Ramification.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 3 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem ramificationIdx_pos_of_mem_minimalPrimes [q.LiesOver p] [q.IsPrime]
    (hq : q ∈ (p.map (algebraMap R S)).minimalPrimes)
    [IsNoetherianRing (Localization.AtPrime q ⧸ p.map (algebraMap R (Localization.AtPrime q)))] :
    0 < q.ramificationIdx R := by
  rw [show q.ramificationIdx R = (Module.length (Localization.AtPrime q)
    ((Localization.AtPrime q) ⧸ p.map (algebraMap R (Localization.AtPrime q)))).toNat from
    ramificationIdx_eq p q]
  set I := p.map (algebraMap R (Localization.AtPrime q)) with hI
  have key : ∀ P : Ideal (Localization.AtPrime q), P.IsPrime → I ≤ P →
      P = IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    intro P hP hIP
    have h1 : (P.comap (algebraMap S (Localization.AtPrime q))).IsPrime := inferInstance
    have h2 : P.comap (algebraMap S (Localization.AtPrime q)) ≤ q := by
      intro x hx
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime q) q x).1
        (IsLocalRing.le_maximalIdeal hP.ne_top (Ideal.mem_comap.1 hx))
    have h3 : p.map (algebraMap R S) ≤ P.comap (algebraMap S (Localization.AtPrime q)) := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact Ideal.map_le_iff_le_comap.1 hIP
    apply le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top)
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
    exact hq.2 ⟨h1, h3⟩ h2
  have hIm : I ≤ IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
    rw [hI, IsScalarTower.algebraMap_eq R S (Localization.AtPrime q), ← Ideal.map_map,
      ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.map_mono hq.1.2
  have hItop : I ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top hIm
  haveI : Nontrivial ((Localization.AtPrime q) ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hItop
  haveI : IsLocalRing ((Localization.AtPrime q) ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : Ring.KrullDimLE 0 ((Localization.AtPrime q) ⧸ I) := by
    refine Ring.KrullDimLE.mk₀ (fun P hP => ?_)
    have hPe : P = IsLocalRing.maximalIdeal ((Localization.AtPrime q) ⧸ I) := by
      apply le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top)
      intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hP' : (P.comap (Ideal.Quotient.mk I)).IsPrime := inferInstance
      have hIP' : I ≤ P.comap (Ideal.Quotient.mk I) := by
        intro z hz
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hz]
        exact P.zero_mem
      have := key _ hP' hIP'
      have hy : y ∈ IsLocalRing.maximalIdeal (Localization.AtPrime q) := by
        rw [IsLocalRing.mem_maximalIdeal]
        intro hy
        exact (IsLocalRing.mem_maximalIdeal _).1 hx (hy.map (Ideal.Quotient.mk I))
      rw [← this] at hy
      exact hy
    rw [hPe]
    exact IsLocalRing.maximalIdeal.isMaximal _
  haveI hArt : IsArtinianRing ((Localization.AtPrime q) ⧸ I) := by
    first
      | infer_instance
      | exact isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.2 ⟨inferInstance, inferInstance⟩
  let f : Submodule (Localization.AtPrime q) ((Localization.AtPrime q) ⧸ I) ↪o
      Submodule ((Localization.AtPrime q) ⧸ I) ((Localization.AtPrime q) ⧸ I) :=
    OrderEmbedding.ofMapLEIff
      (fun N => { carrier := N.carrier
                  add_mem' := fun {a b} ha hb => N.add_mem ha hb
                  zero_mem' := N.zero_mem
                  smul_mem' := by
                    intro c x hx
                    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective c
                    have h1 : s • x = Ideal.Quotient.mk I s * x := Algebra.smul_def s x
                    have h2 : Ideal.Quotient.mk I s • x = Ideal.Quotient.mk I s * x :=
                      smul_eq_mul _ _
                    rw [h2, ← h1]
                    exact N.smul_mem s hx })
      (fun a b => ⟨fun h x hx => h hx, fun h x hx => h hx⟩)
  have hart : IsArtinian (Localization.AtPrime q) ((Localization.AtPrime q) ⧸ I) := by
    have : WellFoundedLT (Submodule ((Localization.AtPrime q) ⧸ I) ((Localization.AtPrime q) ⧸ I)) :=
      inferInstance
    exact f.wellFoundedLT
  have hnoe : IsNoetherian (Localization.AtPrime q) ((Localization.AtPrime q) ⧸ I) := by
    have : WellFoundedGT (Submodule ((Localization.AtPrime q) ⧸ I) ((Localization.AtPrime q) ⧸ I)) :=
      isNoetherian_iff'.1 inferInstance
    exact isNoetherian_iff'.2 f.wellFoundedGT
  have hfin : IsFiniteLength (Localization.AtPrime q) ((Localization.AtPrime q) ⧸ I) := by
    first
      | exact isFiniteLength_iff_isNoetherian_isArtinian.2 ⟨hnoe, hart⟩
      | infer_instance
  have h0 : Module.length (Localization.AtPrime q) ((Localization.AtPrime q) ⧸ I) ≠ 0 := by
    rw [Ne, Module.length_eq_zero_iff]
    exact not_subsingleton _
  have h1 : Module.length (Localization.AtPrime q) ((Localization.AtPrime q) ⧸ I) ≠ ⊤ := by
    first
      | exact Module.length_ne_top_iff.2 hfin
      | exact (Module.length_lt_top_iff.2 hfin).ne
      | exact ne_of_lt (Module.length_lt_top.2 hfin)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 h1
  rw [← hn, ENat.toNat_coe]
  rw [← hn] at h0
  exact Nat.pos_of_ne_zero (fun h => h0 (by simp [h]))
