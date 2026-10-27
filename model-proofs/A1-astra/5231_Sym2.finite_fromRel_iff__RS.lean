/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.finite_fromRel_iff
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 140
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra (Codex, effort medium): R = proof plus up to 3 repair rounds with Lean errors; RS = R plus lemma layer; RT = R with read-only Mathlib sources to search; N0-N3 = independent attempts
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
  classical
  constructor
  · intro h
    letI := h.fintype
    apply Cardinal.mk_lt_aleph0_iff.mp
    refine lt_of_le_of_lt (cardinalMk_prod_le_two_mul_cardinalMk_fromRel sym) ?_
    have hfin : #(Fin 2 × ↥(fromRel sym)) < ℵ₀ :=
      Cardinal.mk_lt_aleph0_iff.mpr inferInstance
    simpa [Cardinal.mk_prod] using hfin
  · intro h
    letI := h
    let f : { p : α × α // r p.fst p.snd } → ↥(fromRel sym) :=
      fun p => ⟨s(p.1.1, p.1.2), fromRel_prop.mpr p.2⟩
    have hf : Function.Surjective f := by
      intro z
      refine ⟨⟨z.1.out, ?_⟩, ?_⟩
      · apply fromRel_prop.mp
        simpa only [mk_fst_out_snd_out] using z.2
      · apply Subtype.ext
        exact mk_fst_out_snd_out z.1
    haveI : Finite ↥(fromRel sym) := Finite.of_surjective f hf
    exact Set.toFinite _
