import Mathlib.Tactic.Use
import Mathlib.Tactic.PushNeg
import Mathlib.Tactic.ByContra
import Mathlib.Data.Set.Lattice
import Mathlib.Algebra.Ring.Defs

section log5
variable (α : Type)
variable (w : α)
variable (p q r : Prop)
variable (a b : α → Prop)


--En general
/-
`exact` le dice a Lean que el goal es satisfecho por el término que
se le pasa
-/
example (h : p) : p := by
  exact h

/-
`assumption` busca entre las hipótesis para ver si una puede cerrar el goal
-/
example (h : p) : p := by
  assumption

/-
Los conectivos y cuantificadores que se interpretan como funciones en BHK
se rompen con `intro`. En implicaciones es como suponer el antecedente y el
goal se vuelve el consecuente. En universales es como empesar con "sea x",
en este caso el goal se modifica para demostrar que x satisface la fórmula.
-/
example : p → p := by
  intro hp
  exact hp

example : ∀ x, a x := by
  intro x
  sorry


example : ¬p := by
  intro hp
  sorry

/-
`have` hace lemas intermedios
-/


/-
`exfalso` es el principio de explosión. Así, modifica el goal a False
-/
example : ¬ p → (p → q) := by
  intro np hp
  exfalso
  apply np hp



--Lógica

-- para modificar el goal
/-
Para "romper" conjunciones del goal se usa `constructor`. Crea un goal
por cada conjunto (¿se dice así?)
-/
example : p ∧ q := by
  constructor
  . sorry
  . sorry

-- Un ↔ (si y solo si) es una conjuncion de dos implicaciones. Asi que tambien podemos usar `constructor`
example : p ↔ q := by
  constructor
  . sorry
  . sorry

/-Las disyunciones se rompen con `left` y `right`. Modifica el goal, ahora habrá
que demostrar el lado izquierdo o derecho del goal anterior.
-/
example : p ∨ q := by
  left
  sorry

example : p ∨ q := by
  right
  sorry

/-
Un existencial se puede romper con `use`. Modica el goal para demostrar que
la fórmula se satisface con el término que se le paso a use. Requiere
`import Mathlib.Tactic.Use`
-/
example : ∃ x, a x := by
  use w
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
Hay un `rintro` que puede romper una disyunción al mismo tiempo que
supone el antecedente. En este caso se crean dos goals.
-/
example : p ∨ q → r := by
  rintro (hp | hq)
  . sorry
  . sorry


-- para modificar hipótesis
/-
Para romper conjunciones de una hipótesis se usa `obtain`
-/
example (h : p ∧ q) : r := by
  obtain ⟨hp, hq⟩ := h
  sorry

/-
Las disyunciones se rompen con `cases` o `rcases`. Hay varias formas
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
`rcases` es más fuerte ya que puede romper fórmulas complejas
-/
example (h : (∃ x, a x) ∧ p ∨ q) : r := by
  rcases h with ⟨⟨x, ha⟩, hp⟩ | hq
  . sorry
  . sorry

/-
Un existencial se rompe con `obtain`, como una conjunción.
-/
example (h : ∃ x, a x) : p := by
  obtain ⟨x, ha⟩ := h
  sorry

/-
Para romper conectivos y cuantificadores que se interpretan como funciones
en BHK se usa `apply`
-/
example (h : p → q) (hp : p) : q := by
  apply h hp

example (h : ∀ x, a x) : a w := by
  apply h w

example (h : ¬p) (hp : p) : False := by
  apply h hp




--Lógica clásica
/-
Para el tercero excluido se usa `by_cases`. Crea dos goals, en uno se
supone que la proposición es cierta y en el otro que la negación
es cierta
-/
example : p := by
  by_cases h : p
  . sorry
  . sorry

/-
Las demostraciones por contradicción se hacen usando `by_contra`. Introduce
la negación del goal como hipótesis y el goal es False
-/
example : p := by
  by_contra hnp
  sorry

/-
Cuando hay negaciones en el goal o las hipótesis, se puede modicar la
fórmula con las equivalencias lógicas que incluyen ¬. Para esto se usa
la táctica `push_neg`. Requiere
`import Mathlib.Tactic.PushNeg`
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
También es posible combinar `by_contra` con `push_neg`. Requiere
`import Mathlib.Tactic.ByContra`
-/
example : p ∧ q := by
  by_contra! h
  sorry



end log



--Conjuntos
section sets
variable {α I : Type*}
variable (A : I → Set α)
variable (a b c : Set α)
open Set
/-
Una estrategia es usar las definiciones para cabiar las hipótesis y el
goal de manera que sean proposiciones de la forma x ∈ s ...
-/
-- operaciones a lo más binarias
#check subset_def
#check inter_def
#check mem_inter_iff
#check union_def
#check mem_union
#check mem_setOf
#check diff_eq
#check mem_diff
#check mem_compl_iff
/-
Para usar las definiciones se usa rw [...]
-/
example : a ⊆ b := by
  rw [subset_def]
  sorry

example (x : α) : x ∈ a ∩ b := by
  rw [mem_inter_iff]
  sorry

example (x : α) : x ∈ a ∪ b := by
  rw [mem_union]
  sorry

example (x : α) : x ∈ a \ b := by
  rw [mem_diff]
  sorry

example (x : α) : x ∈ aᶜ := by
  rw [mem_compl_iff]
  sorry
/-
Un poco más general, rw [...] puede cambiar el goal o las hipótesis usando
igualdades o equivalencias. El cambio es del tŕmino de la izquierda de
la igualdad al término de la derecha. Para hacerlo al revés se debe
usar con rw [<-...]
-/
example (h : a = b) : a = c := by
  rw [h]
  sorry

example (h : a = b) : b = c := by
  rw [<-h]
  sorry

example (p q r : Prop) (h : p ↔ q) : p → r := by
  rw [h]
  sorry

/-
Es posible no usar las definiciones de las operaciones conjuntisatas y
hacer las demostraciones usando que sabemos qué significan
-/
example (xa : x ∈ a) (h : a ⊆ b) : x ∈ b := by
  apply h xa
/-
Una consecuencia es que es posible hacer estas demostraciones en
modo término
-/

-- igualdad
/-
Las proposiciones que afirman la igualdad de dos conjuntos se demuestran
usando el axioma de extensionalidad, en Lean se abrevia con ext
-/
#check ext
example : a = b := by
  ext x
  sorry

-- operaciones arbitrarias
/-
Una intersección arbitraria está muy relacionada con un universal y una
unión arbitraria con un existencial. En las definiciones de abajo aparece
esta relación
-/
#check mem_iInter
#check mem_iUnion

example (x : α) : x ∈ ⋂ i, A i := by
  rw [mem_iInter]
  sorry

example (x : α) : x ∈ ⋃ i, A i := by
  rw [mem_iUnion]
  sorry


end sets



--Igualdades
/-
Lean tiene varias formas para demostrar igualdades, las que más he usado
son `rw [...]`, `simp [...]` (estas dos se parecen mucho, aunque simp es
más fuerte) y `calc`
-/
section
variable {G : Type*} [Group G]
variable (a b c : G)

example (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1] --sutituye a por b en el goal. PD b=c
  rw [h2] --sutituye b por c en el goal. PD c=c. Al final hace rfl

example (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1, h2]

example (h1 : a = b) (h2 : b = c) : a = c := by
  simp only [h1, h2]

example (h1 : a = b) (h2 : b = c) : a = c := by
  calc
    a = b := by assumption
    _ = c := by assumption
end
