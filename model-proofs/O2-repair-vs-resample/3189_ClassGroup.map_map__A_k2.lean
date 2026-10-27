/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     ClassGroup.map_map
Source:      Mathlib @ a02a63c2, Mathlib/RingTheory/ClassGroup/ExtendedHom.lean, line 84
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm A, attempt 2, verified in round 0 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem map_map (f : A →+* B) (hf : Function.Injective f) (g : B →+* C)
    (hg : Function.Injective g) (x : ClassGroup A) :
    map g hg (map f hf x) = map (g.comp f) (hg.comp hf) x := by
  induction x using QuotientGroup.induction_on with | H α
  rw [map_quotientMk, map_quotientMk, map_quotientMk]
  congr 1
  ext : 1
  simp only [Units.coe_map, MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe,
    FractionalIdeal.extendedHom'_apply]
  rw [← FractionalIdeal.coeToSubmodule_inj, FractionalIdeal.coe_extended_eq_span,
    FractionalIdeal.coe_extended_eq_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    try simp only [SetLike.mem_coe] at hx
    rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_extended_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      apply Submodule.subset_span
      refine ⟨a, ha, ?_⟩
      first
        | rw [IsLocalization.map_map]
        | simp [IsLocalization.map_map]
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul b y _ hy =>
      rw [Algebra.smul_def, map_mul, IsLocalization.map_eq, ← Algebra.smul_def]
      exact Submodule.smul_mem _ _ hy
  · rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    apply Submodule.subset_span
    refine ⟨(IsLocalization.map (FractionRing B) f
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hf) :
        FractionRing A →+* FractionRing B) a, ?_, ?_⟩
    · try rw [SetLike.mem_coe]
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_extended_eq_span]
      exact Submodule.subset_span ⟨a, ha, rfl⟩
    · first
        | rw [IsLocalization.map_map]
        | simp [IsLocalization.map_map]
