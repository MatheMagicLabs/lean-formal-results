/-
Machine-generated proof, checked by Lean during the experiment.

Theorem:     Sym2.cardinalMk_prod_eq_two_mul_cardinalMk_fromRel
Source:      Mathlib @ a02a63c2, Mathlib/Data/Sym/Sym2/Card.lean, line 130
             (new in Mathlib since d0a050ad6, i.e. after the models' training data)
Experiment:  O4-layer-with-search, arm RT, verified in round 3 (round 0 = first attempt)
Prover:      claude-opus-5-5
Setup:       Opus 5.5 with repair loop, lemma layer and name search (arm RT)
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
  apply le_antisymm (cardinalMk_prod_le_two_mul_cardinalMk_fromRel sym)
  have hz : ∀ z : fromRel sym, s(z.1.out.1, z.1.out.2) = z.1 := fun z => Quot.out_eq _
  have key : ∀ z : fromRel sym, r z.1.out.1 z.1.out.2 := by
    intro z
    have h2 : s(z.1.out.1, z.1.out.2) ∈ fromRel sym := by
      rw [hz z]
      exact z.2
    exact Sym2.fromRel_prop.1 h2
  have hs : ∀ p : α × α, s(p.2, p.1) = s(p.1, p.2) := fun p => Sym2.eq_swap
  calc 2 * #(fromRel sym) = #(Bool × fromRel sym) := by
        rw [Cardinal.mk_prod]
        simp [Cardinal.mk_fintype, Fintype.card_bool, Cardinal.lift_id]
    _ ≤ #{ p : α × α // r p.fst p.snd } := by
      refine Cardinal.mk_le_of_injective
        (f := fun x : Bool × fromRel sym =>
          cond x.1 (⟨x.2.1.out, key x.2⟩ : { p : α × α // r p.fst p.snd })
            ⟨x.2.1.out.swap, sym.symm _ _ (key x.2)⟩) ?_
      rintro ⟨b, z⟩ ⟨b', z'⟩ h
      cases b <;> cases b' <;> simp only [cond_true, cond_false, Subtype.mk.injEq] at h <;>
        have e := congrArg (fun p : α × α => s(p.1, p.2)) h <;>
        (try simp only [Prod.fst_swap, Prod.snd_swap] at e) <;>
        (try rw [hs z.1.out] at e) <;>
        (try rw [hs z'.1.out] at e) <;>
        rw [hz z, hz z'] at e <;>
        obtain rfl := Subtype.ext e <;>
        first
        | rfl
        | (exfalso
           have h1 := congrArg Prod.fst h
           simp only [Prod.fst_swap] at h1
           have k := key z
           rw [h1] at k
           exact irrefl _ k)
