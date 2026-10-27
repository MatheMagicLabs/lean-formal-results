/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O5-repair-sonnet, arm B, verified in round 0 (round 0 = first attempt)
Prover:      claude-sonnet-5-5
Setup:       Sonnet 5.5: arm B = repair loop; arm A = independent attempts
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

-- (context: the Mathlib file above this declaration)
theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  have key : ∀ p q : α × α, s(p.1, p.2) = s(q.1, q.2) →
      (p.1 = (s(p.1, p.2)).out.1 ↔ q.1 = (s(q.1, q.2)).out.1) → p = q := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h hb
    simp only at h hb
    have ho : s((s(c, d)).out.1, (s(c, d)).out.2) = s(c, d) := by
      first
        | exact mk_fst_out_snd_out _
        | simp
    rw [h] at hb
    rw [Sym2.eq_iff] at h ho
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rcases ho with ⟨o1, o2⟩ | ⟨o1, o2⟩
      · have : a = (s(c, d)).out.1 := hb.mpr o1.symm
        have hcd : d = c := by grind
        subst h1 h2
        grind
      · have : c = (s(c, d)).out.1 := hb.mp (by grind)
        grind
  have mem : ∀ p : {p : α × α // r p.1 p.2}, s(p.1.1, p.1.2) ∈ fromRel sym :=
    fun p => fromRel_prop.mpr p.2
  let f : {p : α × α // r p.1 p.2} → Bool × (fromRel sym) :=
    fun p => (decide (p.1.1 = (s(p.1.1, p.1.2)).out.1), ⟨s(p.1.1, p.1.2), mem p⟩)
  have hinj : Function.Injective f := by
    intro p q h
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq, decide_eq_decide] at h
    obtain ⟨hb, hz⟩ := h
    exact Subtype.ext (key _ _ hz hb)
  have h2 : #(Bool × (fromRel sym)) = 2 * #(fromRel sym) := by
    simp
  calc _ ≤ #(Bool × (fromRel sym)) := Cardinal.mk_le_of_injective hinj
    _ = _ := h2
