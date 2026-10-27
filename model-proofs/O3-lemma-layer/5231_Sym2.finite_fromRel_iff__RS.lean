/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 140
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O3-lemma-layer, arm RS, verified in round 2 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop: arm R = repair only; arm RS = repair plus the Lean-checked lemma layer
Check:       the proof replaced the human proof in the Mathlib file above; Lean reported
             0 errors and no `sorry`; sorry/admit/native_decide/search tactics were rejected.
-/

namespace Sym2
open scoped Cardinal
variable {α : Type*}
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
variable (α) in
open scoped Classical in
variable (α) in
variable (α) in
section fromRel
variable {r : α → α → Prop} (sym : Std.Symm r)

theorem finite_fromRel_iff : (fromRel sym).Finite ↔ Finite { p : α × α // r p.fst p.snd } := by
  constructor
  · intro h
    have : Finite (fromRel sym) := h.to_subtype
    rw [← Cardinal.lt_aleph0_iff_finite] at this ⊢
    exact lt_of_le_of_lt (cardinalMk_prod_le_two_mul_cardinalMk_fromRel sym)
      (Cardinal.mul_lt_aleph0 Cardinal.ofNat_lt_aleph0 this)
  · intro h
    have : Finite (fromRel sym) := by
      refine Finite.of_surjective
        (fun p : {p : α × α // r p.fst p.snd} =>
          (⟨s(p.1.1, p.1.2), fromRel_prop.mpr p.2⟩ : fromRel sym)) ?_
      rintro ⟨z, hz⟩
      have hz' : s(z.out.1, z.out.2) ∈ fromRel sym := by
        rw [mk_fst_out_snd_out]
        exact hz
      refine ⟨⟨z.out, fromRel_prop.mp hz'⟩, ?_⟩
      exact Subtype.ext (mk_fst_out_snd_out z)
    exact Set.toFinite _
