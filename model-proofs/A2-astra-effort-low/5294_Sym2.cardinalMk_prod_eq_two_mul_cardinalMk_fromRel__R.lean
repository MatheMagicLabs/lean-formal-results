/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-low, arm R, verified in round 2 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort low (arms R, N0)
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
  let P := {p : α × α // r p.1 p.2}
  let f : P → fromRel sym := fun p => ⟨s(p.1.1, p.1.2), p.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    revert hz
    refine Sym2.inductionOn z ?_
    intro a b hab
    exact ⟨⟨(a, b), hab⟩, rfl⟩
  choose g hg using hf
  let swap : P → P := fun p =>
    ⟨(p.1.2, p.1.1), sym.symm _ _ p.2⟩
  have hswap (p : P) : f (swap p) = f p := by
    apply Subtype.ext
    simp [f, swap, Sym2.eq_iff, Prod.ext_iff]
  have hne (p : P) : p.1.1 ≠ p.1.2 := by
    intro h
    have hp := p.2
    rw [h] at hp
    exact irrefl _ hp
  let F : Bool × fromRel sym → P :=
    fun x => if x.1 then swap (g x.2) else g x.2
  have hF (x : Bool × fromRel sym) : f (F x) = x.2 := by
    rcases x with ⟨b, z⟩
    cases b <;> simp [F, hswap, hg]
  have hbij : Function.Bijective F := by
    constructor
    · rintro ⟨b, z⟩ ⟨c, w⟩ h
      have hzw : z = w := by
        simpa only [hF] using congrArg f h
      subst w
      cases b <;> cases c
      · rfl
      · have he := congrArg (fun p : P => p.1.1) h
        exact False.elim (hne (g z) (by simpa [F, swap] using he))
      · have he := congrArg (fun p : P => p.1.1) h
        exact False.elim (hne (g z) (by simpa [F, swap] using he.symm))
      · rfl
    · intro p
      have h := congrArg Subtype.val (hg (f p))
      have hc :
          ((g (f p)).1.1 = p.1.1 ∧ (g (f p)).1.2 = p.1.2) ∨
          ((g (f p)).1.1 = p.1.2 ∧ (g (f p)).1.2 = p.1.1) := by
        simpa [f, Sym2.eq_iff, Prod.ext_iff] using h
      rcases hc with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · refine ⟨(false, f p), ?_⟩
        change g (f p) = p
        exact Subtype.ext (Prod.ext h₁ h₂)
      · refine ⟨(true, f p), ?_⟩
        change swap (g (f p)) = p
        exact Subtype.ext (Prod.ext h₂ h₁)
  simpa [Cardinal.mk_prod] using
    Cardinal.mk_congr (Equiv.ofBijective F hbij).symm
