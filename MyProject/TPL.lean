/-Section 3 Propositions and Proofs-/
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := sorry

example : p ∨ q ↔ q ∨ p := sorry

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry

example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry

example : ¬(p ∧ ¬p) := sorry

example : p ∧ ¬q → ¬(p → q) := sorry

example : ¬p → (p → q) := sorry

example : (¬p ∨ q) → (p → q) := sorry

example : p ∨ False ↔ p := sorry

example : p ∧ False ↔ False := sorry

example : (p → q) → (¬q → ¬p) := sorry


/-Prove ¬(p ↔ ¬p) without using classical logic-/
theorem p_iff_nop (p : Prop) : ¬(p ↔ ¬p) := sorry


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

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry

example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry

example : ¬(p → q) → p ∧ ¬q := sorry

example : (p → q) → (¬p ∨ q) := sorry

example : (¬q → ¬p) → (p → q) := sorry

example : p ∨ ¬p := sorry

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

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry
end ex41



section classic41
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r := sorry

example (a : α) : r → (∃ x : α, r) := sorry

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry

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

example : α → ((∀ x : α, r) ↔ r) := sorry

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
