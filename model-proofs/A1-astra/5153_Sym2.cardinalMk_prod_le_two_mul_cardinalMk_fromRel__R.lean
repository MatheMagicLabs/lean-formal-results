/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm R, verified in round 1 (round 0 = first attempt)
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

theorem cardinalMk_prod_le_two_mul_cardinalMk_fromRel :
    #{ p : α × α // r p.fst p.snd } ≤ 2 * #(fromRel sym) := by
  classical
  let f : {p : α × α // r p.fst p.snd} → fromRel sym :=
    fun p => ⟨s(p.1.1, p.1.2), p.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    induction x using Sym2.inductionOn with
    | _ a b =>
      exact ⟨⟨(a, b), hx⟩, rfl⟩
  choose g hg using hf
  have h :
      ∀ p q, f p = f q → p = q ∨ p.1 = q.1.swap := by
    intro p q hpq
    have he := congrArg Subtype.val hpq
    change s(p.1.1, p.1.2) = s(q.1.1, q.1.2) at he
    have he' : p.1 = q.1 ∨ p.1 = q.1.swap := by
      simpa [Sym2.eq_iff, Prod.ext_iff] using he
    exact he'.imp (fun hpq => Subtype.ext hpq) id
  let e : {p : α × α // r p.fst p.snd} → Bool × fromRel sym :=
    fun p => (if p = g (f p) then true else false, f p)
  have he : Function.Injective e := by
    intro p q hpq
    have hfp : f p = f q := congrArg Prod.snd hpq
    have hb := congrArg Prod.fst hpq
    change (if p = g (f p) then true else false) =
      (if q = g (f q) then true else false) at hb
    have hp' := h p (g (f p)) (hg (f p)).symm
    have hq' := h q (g (f q)) (hg (f q)).symm
    rw [← hfp] at hb hq'
    by_cases hp : p = g (f p)
    · have hq : q = g (f p) := by
        by_contra hq
        rw [if_pos hp, if_neg hq] at hb
        cases hb
      exact hp.trans hq.symm
    · have hq : q ≠ g (f p) := by
        intro hq
        rw [if_neg hp, if_pos hq] at hb
        cases hb
      exact Subtype.ext
        ((hp'.resolve_left hp).trans (hq'.resolve_left hq).symm)
  calc
    _ ≤ #(Bool × fromRel sym) := Cardinal.mk_le_of_injective he
    _ = 2 * #(fromRel sym) := by simp [Cardinal.mk_prod]
