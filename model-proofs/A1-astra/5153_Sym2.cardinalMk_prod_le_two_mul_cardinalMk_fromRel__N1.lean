/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm N1, verified in round 0 (round 0 = first attempt)
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
  have hex (q : Sym2 α) : ∃ a b, s(a, b) = q := by
    induction q using Sym2.inductionOn
    exact ⟨_, _, rfl⟩
  let rep (q : Sym2 α) : α × α :=
    ⟨Classical.choose (hex q),
      Classical.choose (Classical.choose_spec (hex q))⟩
  have hrep (q : Sym2 α) : s((rep q).1, (rep q).2) = q :=
    Classical.choose_spec (Classical.choose_spec (hex q))
  let f : {p : α × α // r p.fst p.snd} → fromRel sym :=
    fun p => ⟨s(p.val.1, p.val.2), by simpa using p.property⟩
  let g : {p : α × α // r p.fst p.snd} → Bool × fromRel sym :=
    fun p => (decide (p.val.1 = (rep (f p).val).1), f p)
  have hg : Function.Injective g := by
    intro p q h
    have hf : f p = f q := congrArg Prod.snd h
    have hb := congrArg Prod.fst h
    change decide (p.val.1 = (rep (f p).val).1) =
      decide (q.val.1 = (rep (f q).val).1) at hb
    rw [← hf] at hb
    have hb' : (p.val.1 = (rep (f p).val).1) ↔
        (q.val.1 = (rep (f p).val).1) := by
      simpa using hb
    have hp : s(p.val.1, p.val.2) =
        s((rep (f p).val).1, (rep (f p).val).2) :=
      (hrep (f p).val).symm
    have hq : s(q.val.1, q.val.2) =
        s((rep (f p).val).1, (rep (f p).val).2) := by
      calc
        s(q.val.1, q.val.2) = (f p).val :=
          congrArg Subtype.val hf.symm
        _ = _ := (hrep (f p).val).symm
    rw [Sym2.eq_iff] at hp hq
    rcases hp with ⟨hp₁, hp₂⟩ | ⟨hp₁, hp₂⟩ <;>
      rcases hq with ⟨hq₁, hq₂⟩ | ⟨hq₁, hq₂⟩ <;>
      apply Subtype.ext <;>
      apply Prod.ext <;>
      simp_all
  simpa using Cardinal.mk_le_of_injective hg
