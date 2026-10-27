/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  E1-repair-decomposition, arm V, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, which part of Lean feedback makes repair work: after a shared first attempt (E0), V = full error messages, Z = line numbers only, B = only "Lean rejected this proof"
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
  let X := {p : α × α // r p.fst p.snd}
  let Y := fromRel sym
  let t : X → X := fun x =>
    ⟨(x.1.2, x.1.1), sym.symm _ _ x.2⟩
  let f : X → Y := fun x =>
    ⟨s(x.1.1, x.1.2), by simpa [Y] using x.2⟩
  have hf (x x' : X) : f x = f x' ↔ x = x' ∨ x = t x' := by
    constructor
    · intro h
      have he :
          (x.1.1 = x'.1.1 ∧ x.1.2 = x'.1.2) ∨
          (x.1.1 = x'.1.2 ∧ x.1.2 = x'.1.1) := by
        simpa [f, Sym2.eq_iff, Prod.ext_iff] using
          congrArg (fun z : Y => z.1) h
      rcases he with h | h
      · exact Or.inl (Subtype.ext (Prod.ext h.1 h.2))
      · exact Or.inr (Subtype.ext (Prod.ext h.1 h.2))
    · rintro (h | h)
      · rw [h]
      · subst x
        apply Subtype.ext
        simp [f, t, Sym2.eq_iff, Prod.ext_iff]
  have ht (x : X) : t x ≠ x := by
    intro h
    have he : x.1.2 = x.1.1 :=
      congrArg (fun z : X => z.1.1) h
    have hr := x.2
    change r x.1.1 x.1.2 at hr
    rw [he] at hr
    exact irrefl _ hr
  have hft (x : X) : f (t x) = f x :=
    (hf _ _).2 (Or.inr rfl)
  have hs : Function.Surjective f := by
    rintro ⟨z, hz⟩
    revert hz
    refine Sym2.inductionOn z ?_
    intro a b hab
    exact ⟨⟨(a, b), by simpa [Y] using hab⟩, rfl⟩
  choose g hg using hs
  let F : Bool × Y → X := fun q =>
    if q.1 then t (g q.2) else g q.2
  have hF (b : Bool) (y : Y) : f (F (b, y)) = y := by
    cases b <;> simp [F, hft, hg]
  have hi : Function.Injective F := by
    rintro ⟨b, y⟩ ⟨b', y'⟩ h
    have hy : y = y' := by
      simpa only [hF] using congrArg f h
    subst y'
    have hb : b = b' := by
      cases b <;> cases b'
      · rfl
      · exact False.elim (ht (g y) h.symm)
      · exact False.elim (ht (g y) h)
      · rfl
    exact Prod.ext hb rfl
  have hsur : Function.Surjective F := by
    intro x
    have hx : f x = f (g (f x)) := (hg (f x)).symm
    rcases (hf _ _).1 hx with h | h
    · exact ⟨(false, f x), h.symm⟩
    · exact ⟨(true, f x), h.symm⟩
  calc
    #X = #(Bool × Y) :=
      Cardinal.mk_congr (Equiv.ofBijective F ⟨hi, hsur⟩).symm
    _ = 2 * #Y := by simp [Cardinal.mk_prod]
