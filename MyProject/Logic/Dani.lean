
import Mathlib.Tactic
#check 4/-Section 3 Propositions and Proofs-/
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q → q ∧ p :=
example : p ∧ q → q ∧ p :=
example : p ∧ q ↔ q ∧ p :=
Iff.intro
(fun ha => ⟨ha.2,ha.1⟩ )
(fun hb=> ⟨hb.2, hb.1⟩)
example : p ∧ q → q ∧ p :=  by
  intro ⟨hp, hq⟩
  constructor
  . assumption
  . assumption

example : p ∨ q ↔ q ∨ p := ⟨ λ ha => Or.elim ha (λ hp => Or.inr hp)
(λ hq => Or.inl hq) , λ hb => Or.elim hb (λ hq => Or.inr hq)
(λ hp => Or.inl hp) ⟩


-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  intro ⟨ ⟨ hp, hq⟩, hr⟩
  constructor
  . assumption
  . constructor
    . assumption
    . assumption
  intro ⟨ hp, ⟨ hq, hr⟩ ⟩
  constructor
  constructor <;> assumption
  . assumption

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

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro h1
    rcases h1 with ⟨hp,hqr⟩
    rcases hqr with hq|hr
    . exact Or.inl ⟨hp,hq⟩
    . exact Or.inr ⟨ hp, hr⟩
  . intro h2
    constructor
    rcases h2 with ⟨hp,_⟩|⟨hp, _⟩
    assumption
    assumption
    rcases h2 with ⟨_,hq⟩|⟨_, hr⟩
    constructor
    assumption
    . exact Or.inr hr

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  intro h1
  constructor
  rcases h1 with hp|hqr
  constructor
  assumption
  rcases hqr with ⟨hq, _⟩
  . exact Or.inr hq
  rcases h1 with hp| ⟨_, hr⟩
  constructor
  assumption
  .exact Or.inr hr
  intro h2
  rcases h2 with ⟨hpq, hpr⟩
  rcases hpq with hp|hq
  constructor
  assumption
  rcases hpr with hp|hr
  constructor
  assumption
  . exact Or.inr ⟨hq, hr⟩





-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
constructor
intro h1
intro hpq
rcases hpq with ⟨ hp, hq ⟩
exact h1 hp hq
intro h2
intro hp
intro hq
exact h2 ⟨ hp, hq⟩


example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
constructor
intro h1
constructor
intro hp
rcases hp with hp
. exact h1 (Or.inl hp)
intro hq
rcases hq with hq
. exact h1 (Or.inr hq)
intro ⟨ h2p, h2q⟩
intro hpq
rcases hpq with hp|hq
. exact h2p hp
. exact h2q hq

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
constructor
intro h1
constructor
intro hp
rcases h1 with hp
. exact h1 (Or.inl hp)
intro hq
rcases h1 with hq
. exact h1 (Or.inr hq )
intro ⟨ hp2, hq2 ⟩
intro hpq
rcases hpq with hp|hq
. exact hp2 hp
. exact hq2 hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
constructor
intro h1
constructor
intro hp
exact h1 (Or.inl hp)
intro hq
exact h1 (Or.inr hq)
intro ⟨h2p, h2q⟩ hpq
rcases hpq with hp|hq
exact h2p hp
exact h2q hq


example : ¬p ∨ ¬q → ¬(p ∧ q) := by
intro h1
intro ⟨nhp,nhq⟩
rcases h1 with hp|hq
exact hp nhp
exact hq nhq

example : ¬(p ∧ ¬p) := by
intro ⟨hp, nhp⟩
rcases hp with hp
exact nhp hp

example : p ∧ ¬q → ¬(p → q) := by
intro ⟨ h1p, nhq⟩
intro h2
exact nhq (h2 h1p)

example : ¬p → (p → q) := by
intro h1
intro  h2
exfalso
exact h1 h2


example : (¬p ∨ q) → (p → q) := by
intro h1
rcases h1 with nhp|hq
intro h2
exfalso
exact nhp h2
intro _
exact hq




example : p ∨ False ↔ p := by
constructor
intro h1
rcases h1 with p|F
assumption
exfalso
assumption
intro h2
apply (Or.inl h2)

example : p ∧ False ↔ False := by
constructor
intro ⟨ _, F⟩
assumption
intro F2
constructor
exfalso
assumption
assumption

example : (p → q) → (¬q → ¬p) := by
intro h1
intro hnq
intro hp
exfalso
exact hnq (h1 hp)

example : p→(q→r) → ((p→q)→ (p→r)) := by
intro h1



/-Prove ¬(p ↔ ¬p) without using classical logic-/
theorem p_iff_nop (p : Prop) : ¬(p ↔ ¬p) := by
intro h1
have:

/-Classical Reasoning-/
section classical
open Classical

/-
In Lean Calssical logic means that we have excluded middle.
For every proposition p we can use
Or.elim (em p)
  (case in which p is true)
  (case supposing ¬p is true)
-/

variable (p q r : Prop)

example :  (p → (q ∨ r)) → ((p → q) ∨ (p → r)) := by
intro h1


example : ¬(p ∧ q) → ¬p ∨ ¬q := λ nopyq => Or.elim (Classical.em p) (λ hp => Or.elim (Classical.em q) (λ hq => False.elim (nopyq ⟨hp,hq⟩)) (λ nhq => Or.inr nhq )) (λ nhp => Or.inl nhp)




example (h : ¬(p ∧ q)) : ¬p ∨ ¬q :=
  Or.elim (em p)
    (fun hp : p =>
      Or.inr
        (show ¬q from
          fun hq : q =>
          h ⟨hp, hq⟩))
    (fun hp : ¬p =>
      Or.inl hp)


example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>
  show False from hnq (hpq hp)



example : ¬(p → q) → p ∧ ¬q := by
intro h1
push_neg at h1
assumption

example : (p → q) → (¬p ∨ q) := by
intro h1



example : (¬q → ¬p) → (p → q) := sorry

example : p ∨ ¬p := Or.elim (em p ) (Or.inl) (Or.inr)

/-
Me parece que esta propiedad no es un tautología.
No debería ser demostrable.
Tomar p verdadero y q falso
example : (((p → q) → p) → p) := sorry
-/
end classical




/-Section 4 Quantifiers and Equality-/
section ex41
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
constructor
intro h1
constructor
intro xp
exact (h1 xp).left
intro xq
exact (h1 xq).right
intro h2
intro x
constructor
exact (h2.left x)
exact (h2.right x)


example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
  fun h : ∀ x : α, p x ∧ q x =>
  fun y : α =>
  show p y from (h y).left



example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
intro h1
intro xp
intro x
apply h1
apply xp

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
intro h1
intro x
rcases h1 with hp|hq
constructor
apply hp
right
apply hq


example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := λ h => Or.elim h () ()

end ex41



section classic41
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _ : α, r) → r := λ ⟨ _, hr ⟩ => hr

example (a : α) : r → (∃ x : α, r) := λ hr => ⟨ a , hr ⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := ⟨ λ ⟨ t, pr⟩ =>  ⟨⟨ t, pr.1⟩ , pr.2⟩, λ ⟨ ⟨ t, hp⟩, hr⟩  => ⟨ t ,⟨  hp, hr ⟩  ⟩ ⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
constructor
intro ⟨t, hpq ⟩
rcases hpq with hp|hq
constructor
exact ⟨t, hp⟩
right
exact ⟨t, hq⟩
intro h2pq
rcases h2pq with ⟨t,hp⟩| ⟨t, hq⟩
use t
left
assumption
use t
right
assumption

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
constructor
intro

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
end classic41



section Section42
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
intro a
constructor
b

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry



section Section43
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
end Section43



section Section44
/-
Write the definition of the following definitions and theorems
-/
def even (n : Nat) : Prop := sorry

def prime (n : Nat) : Prop := sorry

def infinitely_many_primes : Prop := sorry

def Fermat_prime (n : Nat) : Prop := sorry

def infinitely_many_Fermat_primes : Prop := sorry

def goldbach_conjecture : Prop := sorry

def Goldbach's_weak_conjecture : Prop :=
  let odd (n : Nat) : Prop := sorry
  sorry

def Fermat's_last_theorem : Prop := sorry
end Section44
