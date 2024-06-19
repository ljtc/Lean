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


example : s ⊆ s ∪ t := by
simp

example : s ⊆ s ∪ t := by
  intro x xs
  constructor
  assumption

example : s ∩ t ⊆ s := by
simp

example : s ∩ t ⊆ s := by
  intro x ⟨ xs, _⟩
  assumption


example (h : u ⊆ s) (h' : u ⊆ t) : u ⊆ s ∩ t := by
  intro x
  intro xu
  constructor
  . exact h xu
  . exact h' xu



example (h : s ⊆ u) (h' : t ⊆ u) : s ∪ t ⊆ u := by
  intro x
  intro xst
  rcases xst with xs|xt
  . exact h xs
  . exact h' xt


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
example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  rintro x ⟨xs, xt|xu⟩
  constructor
  . exact ⟨ xs,xt⟩
  right
  . exact ⟨ xs, xu⟩

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  intro x h
  rcases h with ⟨xs, xt⟩|⟨ xs, xu⟩
  . simp
    constructor
    . assumption
    . left
      assumption
  simp
  constructor
  assumption
  right
  assumption


#check diff_eq
#check mem_diff
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x h
  simp
  simp at h
  obtain ⟨ ⟨ hs, hnt⟩, hu ⟩ := h
  constructor
  assumption
  constructor
  assumption
  assumption




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

example : s ∩ t = t ∩ s := by
ext x
constructor
simp
intro h
intro h1
. exact ⟨ h1, h⟩
intro ⟨h2,h3⟩
. exact ⟨h3, h2⟩




example : s ∪ t = t ∪ s := by
ext x
constructor
simp
intro h
rcases h with xs|xt
right
assumption
left
assumption
simp
intro h
rcases h with xt|xs
right
assumption
left
assumption


example (h : s ⊆ t) : s = s ∩ t := by
ext x
constructor
intro h1
constructor
assumption
exact h h1
intro ⟨xs, _⟩
assumption



example (h : s ⊆ t) : t = s ∪ t := by
ext x
constructor
intro h1
simp
right
assumption
intro h2
rcases h2 with xs|xt
. exact h xs
assumption


example : s ∩ (s ∪ t) = s := by
ext x
constructor
simp
intro h
intro _
assumption
simp
intro h1
constructor
assumption
left
assumption


example : s ∪ s ∩ t = s := by
ext x
constructor
intro h
rcases h with hs|⟨ hs,_⟩
assumption
assumption
intro h1
left
assumption


example : s \ t ∪ t = s ∪ t := by
ext x
constructor
simp
intro h
rcases h with hs|ht
. by_cases h1 : x ∈ t
  right
  assumption
  left
  constructor
  assumption
  assumption
simp
right
assumption


example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
ext x
constructor
simp
intro h
rcases h with ⟨ hs, nht⟩ | ⟨ hs , nht⟩
constructor
. exact Or.inl hs
intro _
. exact nht
constructor
. exact Or.inr hs
intro ht
exfalso
. exact nht ht
intro ⟨ h1, h2⟩
simp at h1
simp at h2
simp
rcases h1 with hs|ht
left
. exact  ⟨hs, (h2 hs)⟩
right
constructor
assumption
intro hs
exfalso
. exact (h2 hs) ht


example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  . intro h1
    rcases h1 with h2|hr
    . rcases h2 with hp|hq
      . exact Or.inl hp
      . exact Or.inr (Or.inl hq)
    . exact Or.inr (Or.inr hr)
  . intro h3
    rcases h3 with hp|h4
    . exact Or.inl (Or.inl hp)
    . rcases h4 with hr|hr
      . exact Or.inl (Or.inr hr)
      . exact Or.inr hr

#check mem_compl_iff
example : s ⊆ t ↔ s ∩ tᶜ = ∅ := by
constructor
intro h1
ext x
constructor
intro hst
simp at hst
obtain ⟨hs, ht⟩ := hst
exact ht (h1 hs)
intro hv
exfalso
exact hv
intro h1
intro x hs
by_cases h: x ∈ t
assumption
have : x ∈ s ∩ tᶜ:= by
  exact ⟨ hs , h ⟩
rw  [h1] at this
exfalso
exact this





example : s \ (t ∪ u) = (s \ t) ∩ (s \ u) := by
ext x
simp
constructor
intro ⟨ hs, ⟨ hnt,hnu⟩ ⟩
constructor
exact ⟨ hs , hnt ⟩
exact ⟨ hs,hnu⟩
intro ⟨⟨ _,hnu⟩,⟨  hs, hu⟩  ⟩
constructor
assumption
constructor
assumption
assumption




example : s \ (t ∩ u) = (s \ t) ∪ (s \ u) := by
ext x
simp
constructor
intro ⟨ hs,htu⟩
by_cases h: x ∈ t
right
constructor
assumption
apply htu h
left
constructor
assumption
assumption
intro h
rcases h with ⟨ h1,h2⟩| ⟨ h3, h4 ⟩
constructor
assumption
intro h5
exfalso
apply h2 h5
constructor
assumption
intro _
assumption


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
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
ext x
simp
constructor
intro ⟨ h1, h2⟩
constructor
assumption
assumption
intro ⟨ h3, h4⟩
constructor
assumption
assumption




example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
ext x
simp
constructor
intro h
constructor
intro i
. exact (h i).1
intro u
. exact (h u).2
intro ⟨ h1,h2⟩
intro i
. exact ⟨ (h1 i), (h2 i)⟩








/-
Hint:
Use by_cases xs : x ∈ s at an appropiate point
-/
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
ext x
simp
constructor
intro h i
rcases h with hs|ha
right
apply hs
left
apply ha
intro h
by_cases xs : x ∈ s
constructor
assumption
right
intro i
rcases h i with hs|ha
assumption
exfalso
apply xs ha






example (j : I) : ⋂ i, s \ A i ⊆ s \ ⋃ i, A i := by
intro i h
simp at h
simp
constructor
exact (h j).1
intro hh
exact (h hh).2


example : s \ ⋃ i, A i ⊆ ⋂ i, s \ A i := by
intro i ⟨ h1, h2⟩
simp
intro t
constructor
assumption
simp at h2
. exact (h2 t)



end
