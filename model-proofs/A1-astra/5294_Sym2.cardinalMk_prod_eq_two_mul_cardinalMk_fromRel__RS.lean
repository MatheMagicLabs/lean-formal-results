/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
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

theorem cardinalMk_prod_eq_two_mul_cardinalMk_fromRel [Std.Irrefl r] :
    #{ p : α × α // r p.fst p.snd } = 2 * #(fromRel sym) := by
  classical
  let S := {z : Sym2 α // z ∈ fromRel sym}
  have hrep : ∀ z : Sym2 α, ∃ p : α × α, s(p.1, p.2) = z := by
    intro z
    refine Sym2.inductionOn z ?_
    intro a b
    exact ⟨(a, b), rfl⟩
  have hex : ∀ z : S, ∃ p : α × α, s(p.1, p.2) = z.1 :=
    fun z => hrep z.1
  choose p hp using hex
  have hr : ∀ z : S, r (p z).1 (p z).2 := by
    intro z
    apply fromRel_prop.mp
    rw [hp z]
    exact z.2
  have hn : ∀ z : S, (p z).1 ≠ (p z).2 := by
    intro z h
    have hz := hr z
    rw [h] at hz
    exact (Std.Irrefl.irrefl _) hz
  let f : S ⊕ S → {q : α × α // r q.1 q.2} :=
    fun x =>
      match x with
      | .inl z => ⟨p z, hr z⟩
      | .inr z => ⟨((p z).2, (p z).1), sym.symm _ _ (hr z)⟩
  let g : {q : α × α // r q.1 q.2} → S :=
    fun q => ⟨s(q.1.1, q.1.2), fromRel_prop.mpr q.2⟩
  have hgf : ∀ x : S ⊕ S, g (f x) = Sum.elim id id x := by
    intro x
    rcases x with z | z
    · apply Subtype.ext
      exact hp z
    · apply Subtype.ext
      change s((p z).2, (p z).1) = z.1
      rw [Sym2.eq_swap]
      exact hp z
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg g h
    rw [hgf, hgf] at hh
    rcases x with z | z <;> rcases y with w | w
    · change z = w at hh
      subst w
      rfl
    · change z = w at hh
      subst w
      have he := congrArg (fun q => q.1.1) h
      change (p z).1 = (p z).2 at he
      exact False.elim (hn z he)
    · change z = w at hh
      subst w
      have he := congrArg (fun q => q.1.1) h
      change (p z).2 = (p z).1 at he
      exact False.elim (hn z he.symm)
    · change z = w at hh
      subst w
      rfl
  apply le_antisymm (cardinalMk_prod_le_two_mul_cardinalMk_fromRel sym)
  simpa [Cardinal.mk_sum, two_mul, S] using
    (Cardinal.mk_le_of_injective hf)
