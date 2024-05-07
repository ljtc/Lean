import Mathlib.Tactic.Use

section LJ1
variable (α : Type)
variable (A B C : Prop)
variable (F G : α → Prop)

-- 1)
example : ¬A ∨ B → (A → B) := by
  intro h ha
  apply Or.elim h
  . intro hna
    exfalso
    exact hna ha
  . intro hb
    assumption

-- 2)
example : (∃ x, F x) → ¬∀ y, ¬F y := by
  intro ⟨x, fx⟩  h
  exact (h x) fx

-- 3)
example : A ∧ B → A := by
  intro ⟨ha, _⟩
  assumption

-- 4)
example : A → A ∨ B := by
  intro ha
  apply Or.inl ha

-- 5)
example : (¬A ∨ ¬B) → ¬(A ∧ B) := by
  intro h ⟨ha, hb⟩
  apply Or.elim h
  . intro hna
    exact hna ha
  . intro hnb
    exact hnb hb

-- 6)
example : ¬(A ∨ B) ↔ ¬A ∧ ¬B := by
  constructor --apply Iff.elim (...) (...)
  . intro h
    constructor --apply And.elim
    . intro ha
      have hab : A ∨ B := Or.inl ha
      exact h hab
    . intro hb
      have hab : A ∨ B := Or.inr hb
      exact h hab
  . intro ⟨hna, hnb⟩ hab
    cases hab
    case inr hb => exact hnb hb
    case inl ha => exact hna ha

-- 7)
example : (A ∨ C) ∧ (B ∨ C) ↔ (A ∧ B) ∨ C := by
  constructor
  . intro ⟨hac, hbc⟩
    cases hac
    case inl ha =>
      cases hbc
      case inl hb => exact Or.inl ⟨ha, hb⟩
      case inr hc => exact Or.inr hc
    case inr hc =>
      right
      assumption
  . intro habc
    constructor
    . cases habc
      case inl hab => exact Or.inl hab.1
      case inr hc => exact Or.inr hc
    . cases habc
      case inl hab => left; exact hab.2
      case inr hc => right; exact hc

-- 8)
example : (∃ x, ¬F x) → ¬∀ x, F x := by
  intro ⟨x, nfx⟩ h
  exact nfx (h x)

-- 9)
example : (∀ x, F x ∧ G x) ↔ (∀ x, F x) ∧ (∀ x, G x ):= by
  constructor
  . intro h
    constructor
    . intro x
      exact (h x).1
    . intro x
      exact (h x).2
  . intro ⟨fx, gx⟩ x
    exact ⟨(fx x), (gx x)⟩


-- 10)
example : (A → ¬B) → (B → ¬A) := by
  intro h hb ha
  exact (h ha) hb

-- 11)
example : (∃ x, A → F x) → (A → ∃ x, F x) := by
  intro ⟨x, afx⟩ ha
  exact ⟨x, (afx ha)⟩

-- 12)
example : (∃ x, F x → A) → (∀ x, F x) → A := by
  intro ⟨x, fxa⟩ h
  exact fxa (h x)

-- 13)
example : (∃ x, F x → G x) → (∀ x, F x) → (∃ x, G x) := by
  intro ⟨x, fg⟩ h
  use x
  exact fg (h x)

end LJ1
