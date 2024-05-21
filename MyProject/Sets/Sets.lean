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

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨xs, xu⟩
  constructor
  . exact h xs
  . assumption

example (h: s ⊆ t): s ∩ u ⊆ t ∩ u := λ _ => λ xinscapu => ⟨(h xinscapu.1) , xinscapu.2⟩

example (h: s⊆ t) : s∪ w ⊆ t ∪ w := λ _ => λ xinunion => Or.elim xinunion (λ h1=> Or.inl (h h1)) (λ h2 => Or.inr (h2))


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

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def]--expands the definition of subset in the goal
  rw [inter_def, inter_def]--expands the intersections in the goal
  rw [subset_def] at h--expands the subset in the hypotesis
  simp only [mem_setOf]
  --Now we have to prove a logical proposition
  intro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  --first we expand the definitions of subset and intersection everywhere
  simp only [subset_def, mem_inter_iff] at *
  --the result is a logical proposition
  intro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩


example : s ⊆ s ∪ t := sorry

example : s ∩ t ⊆ s := sorry

example (h : u ⊆ s) (h' : u ⊆ t) : u ⊆ s ∩ t := sorry

example (h : s ⊆ u) (h' : t ⊆ u) : s ∪ t ⊆ u := sorry


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
example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := sorry

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := sorry

#check diff_eq
#check mem_diff
example : (s \ t) \ u ⊆ s \ (t ∪ u) := sorry


/-
Equality of sets is given by the extesionality axiom
s = t ↔ ∀ x, x ∈ s ↔ x ∈ t
In Lean there is a tactic to use the axiom of extensionality
ext
Even if equality is a biconditional, constructor tactic will fail
to destruct the biconditional. So, in tactic mode start the proof with
ext x
In term mode you can use somethig like:
Set.ext λ x => ⟨λ ... => ..., λ ... => ...⟩
-/
#check ext

example : s ∩ t = t ∩ s := sorry

example : s ∪ t = t ∪ s := sorry

example (h : s ⊆ t) : s = s ∩ t := sorry

example (h : s ⊆ t) : t = s ∪ t := sorry

example : s ∩ (s ∪ t) = s := sorry

example : s ∪ s ∩ t = s := sorry

example : s \ t ∪ t = s ∪ t := sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := sorry

#check mem_compl_iff
example : s ⊆ t ↔ s ∩ tᶜ = ∅ := sorry

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
