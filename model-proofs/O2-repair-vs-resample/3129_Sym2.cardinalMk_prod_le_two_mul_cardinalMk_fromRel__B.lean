/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O2-repair-vs-resample, arm B, verified in round 1 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5: arm B = one attempt plus up to 3 repair rounds with Lean error messages; arm A = 4 independent attempts (attempt k)
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  have h : #{ p : α × α // r p.fst p.snd } ≤ #(Bool × fromRel sym) := by
    refine Cardinal.mk_le_of_injective
      (f := fun p => (decide (s(p.1.1, p.1.2).out = p.1), ⟨s(p.1.1, p.1.2), by simpa using p.2⟩)) ?_
    rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rcases Sym2.eq_iff.mp h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rw [← h2] at h1
      by_cases hab' : a = b
      · subst hab'
        rfl
      · exfalso
        obtain ⟨⟨x, y⟩, hq⟩ : ∃ q : α × α, q = s(a, b).out := ⟨_, rfl⟩
        have key : s(x, y) = s(a, b) := by
          first
            | grind [mk_fst_out_snd_out]
            | (rw [Prod.ext_iff] at hq; obtain ⟨hx, hy⟩ := hq; simp only at hx hy;
               rw [hx, hy]; exact mk_fst_out_snd_out _)
            | (rw [Prod.ext_iff] at hq; obtain ⟨hx, hy⟩ := hq; simp only at hx hy;
               rw [hx, hy]; simp [mk_fst_out_snd_out])
        rw [← hq] at h1
        rcases Sym2.eq_iff.mp key with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · first
            | (simp [Prod.ext_iff] at h1; done)
            | (simp [Prod.ext_iff] at h1; grind)
            | (simp [Prod.ext_iff] at h1; tauto)
            | grind
        · first
            | (simp [Prod.ext_iff] at h1; done)
            | (simp [Prod.ext_iff] at h1; grind)
            | (simp [Prod.ext_iff] at h1; tauto)
            | grind
  simpa using h
