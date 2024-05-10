variable (p q r : Prop)

/-
In Lean we can prove a proposition using many approaches.
We illustrate the idea with the first two exercises.
-/

--Exercise 1. p ∧ q ↔ q ∧ p
--"Strong" Natural Deduction
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
  (fun hpq => And.intro (And.right hpq) (And.left hpq))
  (fun hqp => And.intro (And.right hqp) (And.left hqp))

--Natural Deduction, with Brower-Heyting-Kolmogorov?
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
  (fun hpq => ⟨hpq.2, hpq.1⟩)
  (fun hqp => ⟨hqp.2, hqp.1⟩)

--Tactic mode
example : p ∧ q ↔ q ∧ p := by
  constructor --destroys the goal's biconditional in two implications
  . intro ⟨hp, hq⟩
    --we can use BHK idea to prove an ∧
    exact ⟨hq, hp⟩
  . intro ⟨hq, hp⟩
    constructor --we can destroy the ∧ and demonstrate each part
    . exact hp --if we already know that one hypotesis is what we want
    . assumption --Lean will look into the hypotesis and compare with the goal


--Exercise 2. p ∨ q ↔ q ∨ p
--Natural Deduction
example : p ∨ q ↔ q ∨ p :=
  Iff.intro
  (fun hpq =>
    Or.elim hpq (fun hp => Or.inr hp) (fun hq => Or.inl hq))
  (fun hqp =>
    Or.elim hqp (fun hq => Or.inr hq) (fun hp => Or.inl hp))

--Tactic mode
example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro hpq
    cases hpq
    case inl hp => right; exact hp
    case inr => left; assumption --no need to name and mention hypotesis
  . intro hqp
    rcases hqp with hq | _
    . right; exact hq
    . left; assumption --no need to name and mention hypotesis
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
