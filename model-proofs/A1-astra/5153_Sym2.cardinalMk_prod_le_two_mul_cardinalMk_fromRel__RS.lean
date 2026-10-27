/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_le_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 119
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A1-astra, arm RS, verified in round 1 (round 0 = first attempt)
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
  let β := {z : Sym2 α // z ∈ fromRel sym}
  have hex : ∀ z : β, ∃ p : α × α, s(p.1, p.2) = z.1 := by
    intro z
    induction z.1 using Sym2.inductionOn with
    | hf a b => exact ⟨(a, b), rfl⟩
  choose rep hrep using hex
  have horient (z : β) (p : α × α) (h : s(p.1, p.2) = z.1) :
      p = rep z ∨ p = (rep z).swap := by
    have hh := Sym2.eq_iff.mp (h.trans (hrep z).symm)
    rcases hh with hh | hh
    · exact Or.inl (Prod.ext hh.1 hh.2)
    · exact Or.inr (Prod.ext hh.1 hh.2)
  let f : {p : α × α // r p.1 p.2} → β :=
    fun p => ⟨s(p.1.1, p.1.2), fromRel_prop.mpr p.2⟩
  let g : {p : α × α // r p.1 p.2} → Bool × β :=
    fun p => (decide (p.1 = rep (f p)), f p)
  have hg : Function.Injective g := by
    intro p q h
    have hz : f p = f q := congrArg Prod.snd h
    have hb : decide (p.1 = rep (f p)) = decide (q.1 = rep (f q)) :=
      congrArg Prod.fst h
    rw [← hz] at hb
    have hp' := horient (f p) p.1 rfl
    have hq' := horient (f p) q.1 (congrArg Subtype.val hz).symm
    apply Subtype.ext
    by_cases hp : p.1 = rep (f p)
    · have hq : q.1 = rep (f p) := by
        by_contra hq
        simp [hp, hq] at hb
      exact hp.trans hq.symm
    · have hq : q.1 ≠ rep (f p) := by
        intro hq
        simp [hp, hq] at hb
      exact (hp'.resolve_left hp).trans (hq'.resolve_left hq).symm
  calc
    _ ≤ #(Bool × β) := Cardinal.mk_le_of_injective hg
    _ = 2 * #(fromRel sym) := by simp [Cardinal.mk_prod, β]
