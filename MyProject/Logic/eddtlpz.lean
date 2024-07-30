import Mathlib.Tactic.Use
import Mathlib.Tactic.PushNeg
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.ByContra

variable( α : Type)
variable (A B C D P p q r: Prop)
variable (F G: α → Prop)

example: (∃x, F x →B) → ((∀x, F x)→B):= by
  intro ⟨w,Fw⟩ h
  exact Fw (h w)

example: (∃x, F x → G x) → ((∀x, F x) → ∃x, G x):= by
  intro ⟨r, Fr⟩ s
  exact ⟨r,Fr (s r)⟩

example: A ∨ B ↔ B ∨ A:=
  Iff.intro
  --A ∨ B → B ∨ A--
  (fun A_or_B => A_or_B.elim (fun a => Or.inr a) (fun b => Or.inl b))
  --B ∨ A → A ∨ B--
  (fun B_or_A => B_or_A.elim (fun b => Or.inr b) (fun a => Or.inl a))

example: A ∨ B ↔ B ∨ A:= by
  constructor

  . rintro (a|b)
    . right
      assumption
    . left
      assumption

  . rintro (b|a)
    . right
      assumption
    . left
      assumption

example: A ∧ B ↔ B ∧ A:=
  Iff.intro
  --A ∧ B → B ∧ A--
  (fun A_and_B => And.intro (A_and_B.right) (A_and_B.left))
  --B ∧ A → B ∧ A--
  (fun B_and_A => And.intro (And.right B_and_A) (And.left B_and_A))

example: A ∧ B ↔ B ∧ A := by
  constructor

  . intro ⟨a,b⟩
    exact ⟨b,a⟩

  . intro ⟨b,a⟩
    exact ⟨a,b⟩

-- associativity of ∧ and ∨
example: (A ∧ B) ∧ C ↔ A ∧ (B ∧ C):=
  Iff.intro
  (fun ABC => And.intro (And.left (And.left ABC)) (And.intro (And.right (And.left ABC)) (And.right ABC)))
  (fun ABC => And.intro (And.intro (And.left ABC) (And.left (And.right ABC))) (And.right (And.right ABC)))

example: (A ∧ B) ∧ C ↔ A ∧ (B ∧ C):= by
  constructor
  . rintro ⟨⟨a,b⟩,c⟩
    exact ⟨a,⟨b,c⟩⟩

  . rintro ⟨a,⟨b,c⟩⟩
    exact ⟨⟨a,b⟩,c⟩

example: (A ∨ B) ∨ C ↔ A ∨ (B ∨ C):=
  Iff.intro
  (fun ABC => ABC.elim (fun AB => AB.elim (fun a => Or.inl a) (fun b => Or.inr (Or.inl b))) (fun c => Or.inr (Or.inr c)))
  (fun ABC => ABC.elim (fun a => Or.inl (Or.inl a)) (fun BC => BC.elim (fun b => Or.inl (Or.inr b)) (fun c => Or.inr c)))

example: (A ∨ B) ∨ C ↔ A ∨ (B ∨ C):= by
  constructor
  . rintro ((a|b)|c)
    . left
      assumption
    . right
      left
      assumption
    . right
      right
      assumption

  . rintro (a|(b|c))
    . left
      left
      assumption
    . left
      right
      assumption
    . right
      assumption

-- distributivity
example: A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C):=
  Iff.intro
  (fun ABC => (ABC.right).elim (fun b => Or.inl (And.intro (ABC.left) b)) (fun c => Or.inr (And.intro (ABC.left) c)))
  (fun ABAC => And.intro (ABAC.elim (fun AB => AB.left) (fun AC => AC.left)) (ABAC.elim (fun AB => Or.inl AB.right) (fun AC => Or.inr AC.right)))

theorem ayos: A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C):= by
  constructor
  . rintro ⟨a,(b|c)⟩
    . left
      exact ⟨a,b⟩
    . right
      exact ⟨a,c⟩

  . rintro (⟨a,b⟩|⟨a,c⟩)
    . constructor
      . assumption
      . left
        assumption
    . constructor
      . assumption
      . right
        assumption

example: A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C):=
  Iff.intro
  (fun ABC => And.intro (ABC.elim (fun a => Or.inl a) (fun BC => Or.inr BC.left)) (ABC.elim (fun a => Or.inl a) (fun BC => Or.inr BC.right)))
  (fun ABAC => (ABAC.left).elim (fun a => Or.inl a) (fun b => (ABAC.right).elim (fun a => Or.inl a) (fun c => Or.inr (And.intro b c))))

example: A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C):= by
  constructor
  . rintro (a|⟨b,c⟩)
    . constructor
      . left
        assumption
      . left
        assumption
    . constructor
      . right
        assumption
      . right
        assumption

  . rintro ⟨(a|b),(a|c)⟩
    . left
      assumption
    . constructor
      . assumption
    . constructor
      .assumption
    . right
      exact ⟨b,c⟩

-- other properties
example: (A → (B → C)) ↔ (A ∧ B → C):=
  Iff.intro
  (fun ABC => fun AB => (ABC (AB.left)) AB.right)
  (fun ABC => fun a => fun b => ABC (And.intro (a) (b)))

example: (A → (B → C)) ↔ (A ∧ B → C):= by
  constructor
  . intro atobtoc
    intro ⟨a,b⟩
    exact (atobtoc a) b

  . intro aybtoc
    intro a
    intro b
    exact aybtoc ⟨a,b⟩

example: ((A ∨ B) → C) ↔ (A → C) ∧ (B → C):=
  Iff.intro
  (fun ABC => And.intro (fun a => ABC (Or.inl a)) (fun b => ABC (Or.inr b)))
  (fun ACBC => fun AB => AB.elim (fun a => ACBC.left a) (fun b => ACBC.right b))

example: ((A ∨ B) → C) ↔ (A → C) ∧ (B → C):= by
  constructor
  . intro aobtoc
    . constructor
      . intro a
        have: A∨B := by
          left
          assumption
        exact aobtoc this
      . intro b
        have: A∨B := by
          right
          assumption
        exact aobtoc this

  . intro ⟨atoc,btoc⟩
    rintro (a|b)
    . exact atoc a
    . exact btoc b

example: ¬(A ∨ B) ↔ ¬A ∧ ¬B:=
  Iff.intro
  (fun AB => And.intro (fun a => AB (Or.inl a)) (fun b => AB (Or.inr b)))
  (fun AB => fun ab => ab.elim (fun a => AB.left a) (fun b => AB.right b))

example: ¬(A ∨ B) ↔ ¬A ∧ ¬B:= by
  constructor
  . push_neg at *
    intro naynb
    assumption
  . by_contra! h
    apply ayos h



example: ¬A ∨ ¬B → ¬(A ∧ B):=
  fun AB => fun ab => AB.elim (fun a => a ab.left) (fun b => b ab.right)

example: ¬(A ∧ ¬A):=
  fun AA => AA.right AA.left

example: A ∧ ¬B → ¬(A → B):=
  fun AB => fun ab => AB.right (ab AB.left)

example: ¬A → (A → B):=
  fun na => fun a => False.elim (na a)

example: (¬A ∨ B) → (A → B):=
  fun AB => fun a => AB.elim (fun na => False.elim (na a)) (fun b => b)

example : A ∨ False ↔ A :=
  Iff.intro
  (fun af => af.elim (fun a => a) (fun f => False.elim f))
  (fun a => Or.inl a)

example: A ∧ False ↔ False:=
  Iff.intro
  (fun af => af.right)
  (fun f => False.elim f)

example: (A → B) → (¬B → ¬A):=
  (fun AB => fun nb => fun a => nb (AB a))

example: ¬(A ↔ ¬A):=
  fun AA => (AA.mp  (AA.mpr ((fun AnA => (fun a => (AnA a) a)) (AA.mp)))) (AA.mpr ((fun AnA => (fun a => (AnA a) a)) (AA.mp)))

/-LOGICA CLASICA-/
open Classical

/-
Hint:
Usa Or.elim (em p)
Por ejemplo, en el primero intenta algo así
example : (A → B ∨ C) → ((A → B) ∨ (A → C)) :=
  fun ABC => Or.elim (Classical.em A)
    (fun hA => dem suponiendo que se vale A)
    (fun hnA => dem suponiendo que se vale ¬A)
-/

theorem hola : ¬A → A → B :=
  fun na => fun a => False.elim (na a)

theorem jaja: A → A ∨ B:=
fun a => Or.inl a

example : (A → B ∨ C) → ((A → B) ∨ (A → C)) :=
  fun ABC => (Classical.em A).elim
  (fun a => (ABC a).elim (fun b => Or.inl (fun _ => b)) (fun c => Or.inr (fun _ => c)))
  (fun na => Or.inl ((fun hna => fun a => False.elim (hna a)) na))

example : ¬A → A → B :=
fun hna => fun a => False.elim (hna a)

example : ¬(A ∧ B) → ¬A ∨ ¬B :=
fun nayb => (Classical.em A).elim
(fun a => (Classical.em B).elim (fun b => False.elim (nayb (And.intro (a) (b)))) (fun nb => Or.inr nb))
(fun na => Or.inl na)

example : ¬(A → B) → A ∧ ¬B :=
fun natob => (Classical.em A).elim
  (fun a => (Classical.em B).elim
    (fun b => False.elim (natob (fun _ => b)))
    (fun nb => And.intro (a) (nb))
  )
  (fun na => False.elim (natob ((fun hna => fun a => False.elim (hna a)) na)))

example : (A → B) → (¬A ∨ B) :=
fun atob => (Classical.em A).elim
  (fun a => (Classical.em B).elim
    (fun b => Or.inr b)
    (fun nb => False.elim (nb (atob a)))
  )
  (fun na => Or.inl na)

example : (¬B → ¬A) → (A → B) :=
fun nbtona => (Classical.em A).elim
  (fun a => (Classical.em B).elim
    (fun b => (fun _ => b))
    (fun nb => False.elim  ((nbtona nb) a))
  )
  (fun na => (fun hna => fun a => False.elim (hna a)) na)
--Hint:
#check Classical.em p

example : A ∨ ¬A :=
Classical.em A

example : (((A → B) → A) → A) :=
fun atobtoa =>

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

/---SETS---/

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

example (a b c : ℝ):  a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]

example: (A → (B → (C ∨ D)) ∧ ((P ∧ ¬C) → B)) → ¬C → (A→ (P→ D)):=
  fun h => fun nc => fun a => fun p =>
  (((h a).left) (((h a).right) (And.intro (p) (nc)))).elim
    (fun c => False.elim (nc c))
    (fun d => d)

example: (A → (B → (C ∨ D)) ∧ ((P ∧ ¬C) → B)) → ¬C → (A→ (P→ D)):= by
  intro h nc a p
  obtain ⟨_,h2⟩ := h a
  obtain b := h2 ⟨p, nc⟩
  obtain (c|d) := (h a).left b
  . exact False.elim (nc c)
  . exact d

example: ((A∨B)→ C)→ ((B∨ C)→ D) → (A∨ B)→ D:=
  fun h => fun h1 => fun aob => (Or.elim aob () ()) (h aob)
