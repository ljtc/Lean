import Mathlib.Tactic

/-Section 3 Propositions and Proofs-/
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  constructor
  . intro ⟨hp, hq⟩
    exact ⟨hq, hp⟩
  . intro ⟨hq, hp⟩
    constructor <;> assumption--try to solve all the goals by assumption

/-
cases take a coproduct A+B and induce an arrow A+B → C by using the
universal property of the coproduct, i.e., we must give it an arrow
from the inclusions inl: A → A+B and inr: B → A+B. This is the function
of case inl and case inr
-/

/-
At this point, the main difference between cases and rcases (in addition
to syntax) is that rcases destroys the ∨ of the hypothesis and creates
a goal for each disjunct
-/
example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro h
    cases h
    case inl hp => exact Or.inr hp
    case inr => left; assumption
  . intro h
    rcases h with hq | hp
    . exact Or.inr hq
    . left
      assumption

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  . intro ⟨⟨hp, hq⟩, hr⟩
    exact ⟨hp, ⟨hq, hr⟩⟩
  . intro ⟨hp, ⟨hq, hr⟩⟩
    constructor
    . constructor <;> assumption
    . assumption

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  . intro h
    cases h
    case inl hpq =>
      cases hpq
      case inl hp => left; assumption
      case inr hq => right; left; assumption
    case inr hr => right; right; assumption
  . intro h
    rcases h with hp | hqr
    . left; left; assumption
    . rcases hqr with hq | hr
      . left; right; assumption
      . right; assumption

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro ⟨hp, hqr⟩
    rcases hqr with hq | hr
    . left; exact ⟨hp, hq⟩
    . right; exact ⟨hp, hr⟩
  . intro h
    rcases h with ⟨hp, hq⟩ | ⟨hp, hr⟩
    . constructor
      . exact hp
      . left; assumption
    . constructor
      . assumption
      . right; assumption

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro h
    rcases h with hp | ⟨hq, hr⟩
    . constructor
      . left; assumption
      . left; assumption
    . constructor
      . right; assumption
      . right; assumption
  . intro ⟨hpq, hpr⟩
    rcases hpq with hp | hq
    . left; assumption
    . rcases hpr with hp' | hr
      . left; assumption
      . right; exact ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  constructor
  . intro h ⟨hp, hq⟩
    exact (h hp) hq
  . intro h hp hq
    exact h ⟨hp, hq⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro h
    constructor
    . intro hp
      exact h (Or.inl hp)
    . intro hq
      exact h (Or.inr hq)
  . intro ⟨hpr, hqr⟩ hpq
    rcases hpq with hp | hq
    . exact hpr hp
    . exact hqr hq

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  constructor
  . intro h
    constructor
    . intro hp
      exact h (Or.inl hp)
    . intro hq
      exact h (Or.inr hq)
  . intro ⟨hnp, hnq⟩ hpq
    rcases hpq with hp | hq
    . exact hnp hp
    . exact hnq hq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro h ⟨hp, hq⟩
  rcases h with hnp | hnq
  . exact hnp hp
  . exact hnq hq

example : ¬(p ∧ ¬p) := by
  intro ⟨hp, hnp⟩
  exact hnp hp

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩ hpq
  exact hnq (hpq hp)

example : ¬p → (p → q) := by
  intro hnp hp
  exact absurd hp hnp

example : (¬p ∨ q) → (p → q) := by
  intro h hp
  rcases h with hnp | hq
  . exact absurd hp hnp
  . assumption

example : p ∨ False ↔ p := by
  constructor
  . intro h
    cases h
    case inl => assumption
    case inr hf => exfalso; assumption
  . intro hp
    left
    assumption

example : p ∧ False ↔ False := by
  constructor
  . intro ⟨_, _⟩
    assumption
  . intro
    exfalso
    assumption

example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  exact hnq (hpq hp)

/-Prove ¬(p ↔ ¬p) without using classical logic-/
theorem p_iff_nop (p : Prop) : ¬(p ↔ ¬p) := by
  intro ⟨h, h'⟩
  have np : ¬p := by
    intro hp
    exact (h hp) hp
  have nnp : ¬¬p := by
    intro hnp
    exact hnp (h' hnp)
  exact nnp np


/-Classical Reasoning-/
section classical
open Classical

/-
In Lean Calssical logic means that we have excluded middle.
For every proposition p we can use
Or.elim (em p)
  (case in which p is true)
  (case supposing ¬p is true)

Of course, we can use cases (em p) or rcases (em p) with hp | hnp
-/

variable (p q r : Prop)

/-
Instead of Or.elim (em p), it is possible to use contradiction.
I have used push_neg from Mathlib.Tactic to write equivalences,
in clasical logic, of negation of propositions.
-/
example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  by_contra h'
  push_neg at h'
  rcases (h (h'.1).1) with hq | hr
  . exact (h'.1).2 hq
  . exact (h'.2).2 hr

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro h
  by_contra! h'
  exact h h'

example : ¬(p → q) → p ∧ ¬q := by
  intro h
  by_contra! h'
  exact h h'

example : (p → q) → (¬p ∨ q) := by
  intro h
  by_contra! h'
  exact h'.2 (h h'.1)

example : (¬q → ¬p) → (p → q) := by
  intro h hp
  by_contra hnq
  exact (h hnq) hp

--Mathlib.Tactic forces the sintax Classical.em, otherwise it is ambiguous
example : p ∨ ¬p := Classical.em p

example : p ∨ ¬p := by
  by_contra! h
  exact h.1 h.2

example : (((p → q) → p) → p) := by
  intro h
  contrapose! h
  have : p → q := by
    intro hp
    exfalso
    exact h hp
  exact ⟨this, h⟩

end classical



/-Section 4 Quantifiers and Equality-/
section ex41
variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor
    . intro a
      exact (h a).1
    . intro a
      exact (h a).2
  . intro ⟨h, h'⟩ x
    exact ⟨h x, h' x⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro h h' a
  exact (h a) (h' a)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h a
  rcases h with hp | hq
  . left
    exact hp a
  . right
    exact hq a

end ex41



section classic41
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

/-
In the following example Lean will raise a warning because we are not
going to use the variable x. If you want to avoid that kind of warning
it is possible to write (∃ _ : α, r) → r
-/
example : (∃ x : α, r) → r := by
  intro ⟨_, hr⟩
  assumption

example (a : α) : r → (∃ x : α, r) := by
  intro hr
  exact ⟨a, hr⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  exact exists_and_right

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := by
  constructor
  . intro ⟨a, h⟩
    constructor
    . use a
      exact h.1
    . exact h.2
  . intro ⟨⟨a, hp⟩, hr⟩
    exact ⟨a, ⟨hp, hr⟩⟩

/-
In Mathlib there is another tactic to handle existencial cuantifiers.
To prove ∃ x, p x we have to give a pair ⟨a, h⟩, where a : α and h : p a,
with Mathlib.Tactic we can "break" the pair and write
use a
exact h
as a proof of ∃ x, p x.
-/
/-
An example where it is clear that rcases is stronger than cases
is the following:
-/
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  . intro ⟨a, hpq⟩
    rcases hpq with hp | hq
    . left
      exact ⟨a, hp⟩
    . right
      exact ⟨a, hq⟩
  . intro h
    rcases h with ⟨a, hp⟩ | ⟨a, hq⟩ --(*)
    . exact ⟨a, Or.inl hp⟩
    . use a
      right
      assumption
/- (*)
rcases can destruct the hypotesis as a pair, while cases can't.
With cases we would like to write the following, however it will fail
cases h
case inl ⟨a, hp⟩ => sorry
case inr ⟨a, hq⟩ => sorry
-/

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  . intro h ⟨a, hnp⟩
    exact hnp (h a)
  . intro h a
    push_neg at h
    exact h a

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  . intro ⟨a, hp⟩ h
    exact (h a) hp
  . intro h
    push_neg at h
    assumption

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  . intro h a
    push_neg at h
    exact h a
  . intro h ⟨a, hp⟩
    exact (h a) hp

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  . intro h
    push_neg at h
    assumption
  . intro ⟨a, hnp⟩ h
    exact hnp (h a)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  . intro h ⟨a, hp⟩
    exact (h a) hp
  . intro h a hp
    exact h ⟨a, hp⟩

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  . intro ⟨b, hpr⟩ h
    exact hpr (h b)
  . intro h
    by_contra h'
    push_neg at h'
    have : ∀ (x : α), p x := by
      intro b
      exact (h' b).1
    exact (h' a).2 (h this)

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  . intro ⟨b, hrp⟩ hr
    use b
    exact hrp hr
  . intro h
    by_contra h'
    push_neg at h'
    have : ∃ x, p x := h (h' a).1
    rcases this with ⟨b, hp⟩
    exact (h' b).2 hp

end classic41



section Section42
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := by
  intro a
  constructor
  . intro h
    exact h a
  . intro hr _
    assumption


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  . intro h
    by_contra h'
    push_neg at h'
    rcases h'.1 with ⟨a, hnp⟩
    rcases (h a) with hp | hr
    . exact hnp hp
    . exact h'.2 hr
  . intro h a
    rcases h with hp | _
    . left
      exact hp a
    . right
      assumption

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  . intro h hr a
    exact (h a) hr
  . intro h a hr
    exact (h hr) a

end Section42


section Section43
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
  have : shaves barber barber ↔ ¬shaves barber barber := h barber
  exact (p_iff_nop (shaves barber barber)) this
end Section43



section Section44
/-
Write the definition of the following definitions and theorems
-/
def even (n : Nat) : Prop := ∃ (m : Nat), n = 2 * m

def prime (n : Nat) : Prop :=
  1 < n ∧ ∀ (a b : Nat), n = a * b → (a = 1 ∨ b = 1)

def infinitely_many_primes : Prop :=
  ∀ (n : Nat), ∃ p, prime p ∧ n < p

def Fermat_prime (n : Nat) : Prop :=
  prime n ∧ ∃ (m : Nat), n = 2^(2^m) + 1

def infinitely_many_Fermat_primes : Prop :=
  ∀ (k : Nat), ∃ n, Fermat_prime n ∧ k < n

def goldbach_conjecture : Prop :=
  ∀ (n : Nat), 2 < n → (∃ p q, prime p ∧ prime q ∧ n = p + q)

def Goldbach's_weak_conjecture : Prop :=
  let odd (n : Nat) : Prop := ∃ (m : Nat), n = 2 * m + 1
  ∀ (n : Nat), odd n ∧ 5 < n →
    ∃ p₁ p₂ p₃, prime p₁ ∧ prime p₂ ∧ prime p₃ ∧ n = p₁ + p₂ + p₃

def Fermat's_last_theorem : Prop :=
  ∀ (n : Nat), 2 < n → ¬∃ (a b c : Nat), a^n + b^n = c^n
end Section44
