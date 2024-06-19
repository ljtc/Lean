--Esto está en la sección 5 de *Theorem Proving in Lean 4*


/-
`t1 <;> t2` trata de cerrar todos los subgoals generados por la táctica
`t1` usando la táctica `t2`
-/
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption



/-
`first | t₁ | t₂ | ... | tₙ` aplica cada `tᵢ` hasta que alguna tiene
éxito, o manda un error
-/
example (p q : Prop) (hp : p) : p ∨ q := by
  first | left; assumption | right; assumption
--`left; assumption` resuelve el goal. `right; assumption` falla

example (p q : Prop) (hq : q) : p ∨ q := by
  first | left; assumption | right; assumption
--`left; assumption` falla. `right; assumption` resuelve el goal



/-
Se puede combinar con la táctica `repeat`
-/
example (p q r : Prop) (hp : p) : p ∨ q ∨ r := by
  repeat (first | left; assumption | right | assumption)
--resuelve el goal con la primera aplicación de `left; assumption`

example (p q r : Prop) (hq : q) : p ∨ q ∨ r := by
  repeat (first | left; assumption | right | assumption)
--con la primera aplicación el goal es `q ∨ r`
--en la segunda aplicación el goal se cierra con `left; assumption`

example (p q r : Prop) (hr : r) : p ∨ q ∨ r := by
  repeat (first | left; assumption | right | assumption)
--con la primera aplicación el goal es `q ∨ r`
--en la segunda aplicación `left; assumption` vuelve a fallar
--se aplica `right` y el goal es `r`, el cual se cierra con `assumption`



/-
En el siguiente ejemplo se necesita `repeat`ya que `constructor` no
rompe a `q ∧ r`
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  repeat (first | constructor | assumption)

/-
El ejemplo anterior falla si se escribe así:

example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> constructor <;> assumption

Esto es porque el segundo constructor falla en resolver los goals
generados por el primer constructor.
Para esto está `try t`, que ejecuta `t` y manda "exito". Así, puede
pasar a lo siguiente
-/
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption
