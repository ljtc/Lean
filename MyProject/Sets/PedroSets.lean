import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity


section
variable {α : Type*}
variable (s t u : Set α)
open Set

/-
Given a type α, a term of type Set α can be seen as a subset of α.
Somethig like α is our "universe". The membership relation is local,
in the sense that it only makes sense for a term x : α (element) and
a term s : Set α (subset).

We know that a subset s : Set α is given by a characteristic function
p : α → Prop and viceversa, s = {x | p x}. The correspondence extends to
logical conectives and operations on sets.

The conclution of the previous discution is that we can prove properties
of operations on sets in the same way we prove logical propositions.
-/

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := λ _ => λ xinsu => ⟨ h xinsu.1, xinsu.2⟩


/-
Useful stuff to deal with sets
-/
#check subset_def
#check inter_def
#check mem_setOf
#check inter_def
#check mem_inter_iff

#check union_def
#check mem_union

/-
In Lean, it is possible to substitute equals for equals by means of
the rewriting tactic.
rw [...]
We can think that rewrite can replace stuff that is definitionally equal.
For "more complex subtitutions" we can use the simplifier
simp
It will be useful, for now, to use a restricted version in which we have
to pass the substitution we want
simp only [...]
-/

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := λ _ => λ su => ⟨ h su.1, su.2⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro _ su
  constructor
  . apply h (And.left su)
  . apply And.right su

example : s ⊆ s ∪ t := λ _ => λ es => Or.inl (es)

example : s ∩ t ⊆ s := λ _ => λ syt => And.left syt

example : s ∩ t ⊆ s := λ _ => λ syt => syt.1

example (h : u ⊆ s) (h' : u ⊆ t) : u ⊆ s ∩ t := λ _ => λ eu=>  ⟨ h eu, h' eu⟩

example (h : s ⊆ u) (h' : t ⊆ u) : s ∪ t ⊆ u := λ _ => λ sot => sot.elim (λ es => h es) (λ et => h' et)


/-
rintro is stronger than intro, in the same way rcases is stronger
than cases. In the following example it is possible to introduce the
hypotesis and make cases with a one line command. Try,
rintro x ⟨xs, xt | xu⟩
. sorry
. sorry
Compare with
intro x ⟨xs, h⟩
rcases h with xt | xu
. sorry
. sorry
-/
example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := λ _ => λ ⟨ es, etou⟩ => etou.elim (λ et=> Or.inl ⟨ es, et⟩ ) (λ eu=> Or.inr ⟨ es, eu⟩ )

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  rintro _ (⟨ es,et⟩ | ⟨ es, eu⟩ )
  . exact ⟨ es, Or.inl et⟩
  . exact ⟨ es, Or.inr eu⟩

#check diff_eq
#check mem_diff
example : (s \ t) \ u ⊆ s \ (t ∪ u) := λ _ => λ ⟨ ⟨ es, nt⟩ ,nu⟩ => ⟨ es, λ tou=> tou.elim (λ et=> nt et) (λ eu => nu eu)⟩


/-
Equality of sets is given by the extesionality axiom
s = t ↔ ∀ x, x ∈ s ↔ x ∈ t
In Lean there is a tactic to use the axiom of extensionality
ext
Even if equality is a biconditional, constructor tactic will fail
to destruct the biconditional. So,

in tactic mode start the proof with
ext x

In term mode you can use somethig like:
Set.ext λ x => ⟨λ ... => ..., λ ... => ...⟩
-/
#check ext

example : s ∩ t = t ∩ s := Set.ext λ _ => ⟨ λ  ⟨A , Z⟩ => ⟨ Z, A⟩ , λ ⟨ A, Z⟩ => ⟨ Z, A⟩ ⟩

example : s ∪ t = t ∪ s := by
  ext _
  constructor
  . rintro ( A | Z)
    . apply Or.inr A
    . apply Or.inl Z
  . rintro ( A | Z)
    . apply Or.inr A
    . apply Or.inl Z

example : s ∪ t = t ∪ s := Set.ext λ _ => ⟨ λ h => h.elim (Or.inr) (Or.inl), λ h => h.elim (Or.inr) (Or.inl)⟩

example (h : s ⊆ t) : s = s ∩ t := Set.ext λ _ => ⟨λ es => ⟨ es, h es⟩  , λ ⟨ A, _⟩ => A⟩

example (h : s ⊆ t) : t = s ∪ t := Set.ext λ _ => ⟨λ A=> Or.inr A, λ hip=> hip.elim (λ A=> h A) (λ B => B) ⟩

example : s ∩ (s ∪ t) = s := Set.ext λ _ => ⟨ λ A=> A.1, λ A=> ⟨ A, Or.inl A⟩ ⟩

example : s ∪ s ∩ t = s := Set.ext λ _ => ⟨λ h=> h.elim (λ a=> a) (λ b=> b.1) , λ A=> Or.inl A⟩

example : s \ t ∪ t = s ∪ t := Set.ext λ x => ⟨ λ h=> h.elim (λ A=> Or.inl A.1) (λ T=> Or.inr T), λ A=> A.elim (λ S=> Or.elim (em (x ∈ t)) (λ T=> Or.inr T ) (λ N=> Or.inl ⟨S, N⟩ )) (Or.inr)⟩

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := Set.ext λ _ => ⟨λ h=> h.elim (λ ⟨ S, NT⟩ => ⟨ Or.inl S, λ int=> NT int.2⟩ ) (λ ⟨ S, NT⟩ => ⟨ Or.inr S, λ int=> NT int.1⟩ ), λ ⟨ SuT, Nint ⟩=> SuT.elim (λ S=> Or.inl ⟨ S, λ T=> Nint ⟨ S,T⟩⟩  ) (λ T=> Or.inr ⟨T, λ S=> Nint ⟨ S, T⟩ ⟩  ) ⟩

#check mem_compl_iff

example : s ⊆ t → s ∩ tᶜ ⊆ ∅ :=   λ sct => λ _ => λ  ⟨ es, nt⟩  => False.elim (nt (sct  es))


example : (x ∈ (s ∩ tᶜ)) → x ∈ s := λ h => h.1

example : (x ∈ (s ∩ tᶜ)) → ¬ (x ∈ t ) := λ h => h.2


#check mem_inter_iff
example : s \ (t ∪ u) = (s \ t) ∩ (s \ u) := sorry

example : s \ (t ∩ u) = (s \ t) ∪ (s \ u) := sorry


end


section
--Arbitrary unions and intersections
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

/-
Hint:
Translate from sets to logic usin rw [...]
-/
#check mem_inter_iff
#check mem_iUnion
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := sorry

#check mem_iInter
example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := sorry

/-
Hint:
Use by_cases xs : x ∈ s at an appropiate point
-/
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := sorry


#check mem_diff
#check mem_iInter
#check mem_iUnion
example (j : I) : ⋂ i, s \ A i ⊆ s \ ⋃ i, A i := sorry

example : s \ ⋃ i, A i ⊆ ⋂ i, s \ A i := sorry



end
