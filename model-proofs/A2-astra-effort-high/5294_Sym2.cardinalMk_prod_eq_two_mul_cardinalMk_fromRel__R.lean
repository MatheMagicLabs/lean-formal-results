/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  A2-astra-effort-high, arm R, verified in round 0 (round 0 = first attempt)
Prover:      gpt-6-astra
Setup:       GPT-6 Astra, reasoning effort high (arms R, N0)
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
  have heq (a b c d : α) :
      s(a, b) = s(c, d) ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
    simp [Sym2.eq_iff]
  have hr (a b : α) (h : r a b) : r b a := by
    have hm : s(a, b) ∈ fromRel sym := h
    rw [(heq a b b a).2 (Or.inr ⟨rfl, rfl⟩)] at hm
    exact hm
  let g : P → fromRel sym := fun p => ⟨s(p.1.1, p.1.2), p.2⟩
  have hex (e : fromRel sym) :
      ∃ p : P, s(p.1.1, p.1.2) = e.1 := by
    rcases e with ⟨e, he⟩
    revert he
    refine Sym2.inductionOn e ?_
    intro a b hab
    exact ⟨⟨(a, b), hab⟩, rfl⟩
  choose rep hrep using hex
  have gp (e : fromRel sym) : g (rep e) = e := by
    apply Subtype.ext
    exact hrep e
  let swap : P → P := fun p => ⟨(p.1.2, p.1.1), hr _ _ p.2⟩
  have gs (p : P) : g (swap p) = g p := by
    apply Subtype.ext
    exact (heq _ _ _ _).2 (Or.inr ⟨rfl, rfl⟩)
  have ns (p : P) : swap p ≠ p := by
    intro h
    have hab : p.1.2 = p.1.1 :=
      congrArg (fun q : P => q.1.1) h
    have haa : r p.1.1 p.1.1 := by
      simpa only [hab] using p.2
    exact Std.Irrefl.irrefl _ haa
  let f : Bool × fromRel sym → P :=
    fun q => if q.1 then swap (rep q.2) else rep q.2
  have gf (q : Bool × fromRel sym) : g (f q) = q.2 := by
    rcases q with ⟨b, e⟩
    cases b <;> simp [f, gs, gp]
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨b, e⟩ ⟨c, d⟩ h
      have hed : e = d := by
        simpa only [gf] using congrArg g h
      subst d
      have hbc : b = c := by
        cases b <;> cases c
        · rfl
        · exact False.elim (ns _ (by simpa [f] using h.symm))
        · exact False.elim (ns _ (by simpa [f] using h))
        · rfl
      exact Prod.ext hbc rfl
    · intro x
      have hx :
          s(x.1.1, x.1.2) =
            s((rep (g x)).1.1, (rep (g x)).1.2) :=
        (congrArg Subtype.val (gp (g x))).symm
      rcases (heq _ _ _ _).1 hx with h | h
      · refine ⟨(false, g x), ?_⟩
        apply Subtype.ext
        simpa [f] using (Prod.ext h.1 h.2).symm
      · refine ⟨(true, g x), ?_⟩
        apply Subtype.ext
        simpa [f, swap] using (Prod.ext h.1 h.2).symm
  calc
    #P = #(Bool × fromRel sym) :=
      Cardinal.mk_congr (Equiv.ofBijective f hf).symm
    _ = 2 * #(fromRel sym) := by simp [Cardinal.mk_prod]
