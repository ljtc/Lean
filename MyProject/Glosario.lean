import Mathlib.Tactic
section
variable (α : Type)
variable (w : α)
variable (p q r : Prop)
variable (a b : α → Prop)

--En general
/-
exact le dice a Lean que el goal es satisfecho por el término que
se le pasa
-/
example (h : p) : p := by
  exact h

/-
assumption busca entre las hipótesis para ver si una puede cerrar el goal
-/
example (h : p) : p := by
  assumption

/-
have hace lemas intermedios
-/
example : p := by
  have bla : q := by
    sorry
  sorry

/-
exfalso es el principio de explosión. Así, modifica el goal a False
-/
example : p := by
  exfalso
  sorry



--Lógica

-- para modificar el goal
/-
Para "romper" conjunciones del goal se usa constructor. Crea un goal
por cada conjunto (¿se dice así?)
-/
example : p ∧ q := by
  constructor
  . sorry
  . sorry

example : p ↔ q := by
  constructor
  . sorry
  . sorry

/-
Las disyunciones se rompen con left y right. Modica el goal, ahora habrá
que demostrar el lado izquierdo o derecho del goal anterior.
-/
example : p ∨ q := by
  left
  sorry

example : p ∨ q := by
  right
  sorry

/-
Un existencial se puede romper con use. Modica el goal para demostrar que
la fórmula se satisface con el término que se le paso a use. Requiere
import Mathlib.Tactic.Use
-/
example : ∃ x, a x := by
  use w
  sorry

/-
Los conectivos y cuantificadores que se interpretan como funciones en BHK
se rompen con intro. En implicaciones es como suponer el antecedente y el
goal se vuelve el consecuente. En universales es como empesar con sea x,
en este caso el goal se modica para demostrar que x satisface la fórmula
-/
example : p → q := by
  intro hp
  sorry

example : ∀ x, a x := by
  intro x
  sorry

example : ¬p := by
  intro hp
  sorry

/-
Cuando la hipótesis es compleja se puede romper y suponer cada parte de
ella de una sola vez
-/
example : p ∧ q → r := by
  intro ⟨hp, hq⟩
  sorry

example : (∃ x, a x ∧ b x) → p := by
  intro ⟨x, ⟨ha, hb⟩⟩
  sorry
/-
Hay un r intro que puede romper una disyunción al mismo tiempo que
supone el antecedente. En este caso se crean dos goals.
-/
example : p ∨ q → r := by
  rintro (hp | hq)
  . sorry
  . sorry


-- para modificar hipótesis
/-
Para romper conjunciones de una hipótesis se usa obtain
-/
example (h : p ∧ q) : r := by
  obtain ⟨hp, hq⟩ := h
  sorry

/-
Las disyunciones se rompen con cases o rcases. Hay varias formas
para la sitaxis de estos
-/
example (h : p ∨ q) : r := by
  cases h with
  | inl hp => sorry
  | inr hq => sorry

example (h : p ∨ q) : r := by
  cases h
  case inl hp => sorry
  case inr hq => sorry

example (h : p ∨ q) : r := by
  rcases h with hp | hq
  . sorry
  . sorry
/-
rcases es más fuerte ya que puede romper fórmulas complejas
-/
example (h : (∃ x, a x) ∧ p ∨ q) : r := by
  rcases h with ⟨⟨x, ha⟩, hp⟩ | hq
  . sorry
  . sorry

/-
Un existencial se rompe con obtain, como una conjunción.
-/
example (h : ∃ x, a x) : p := by
  obtain ⟨x, ha⟩ := h
  sorry

/-
Para romper conectivos y cuantificadores que se interpretan como funciones
en BHK se usa apply
-/
example (h : p → q) (hp : p) : q := by
  apply h hp

example (h : ∀ x, a x) : a w := by
  apply h w

example (h : ¬p) (hp : p) : False := by
  apply h hp




--Lógica clásica
/-
Para el tercero excluido se usa by_cases. Crea dos goals, en uno se
supone que la proposición es cierta y en el otro que la negación
es cierta
-/
example : p := by
  by_cases h : p
  . sorry
  . sorry

/-
Las demostraciones por contradicción se hacen usando by_contra. Introduce
la negación del goal como hipótesis y el goal es False
-/
example : p := by
  by_contra hnp
  sorry

/-
Cuando hay negaciones en el goal o las hipótesis, se puede modicar la
fórmula con las equivalencias lógicas que incluyen ¬. Para esto se usa
la táctica push_neg. Requiere
import Mathlib.Tactic.PushNeg
-/
example : ¬(p ∨ q) := by
  push_neg
  sorry

example (h : ¬(p → q)) : r := by
  push_neg at h
  sorry
/-
En Lean es posible aplicar una táctica en todos los lugares donde sea
posible usarla
-/
example (h : ¬(p → q)) : ¬(p ∨ q) := by
  push_neg at *
  sorry
/-
También es posible combinar by_contra con push_neg
-/
example : p ∧ q := by
  by_contra! h
  sorry
end



--Conjuntos
