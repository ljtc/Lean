import Mathlib.Algebra.Module.LinearMap.Basic

/-
En Mathlib se unificaron los nombre de espacio vectorial, modulo y
semi-modulo. Todos los anteriores de llaman modulo. La diferencia que
hay entre los tres es la estructura que tienen "los escalares" Por ejemplo:
ℕ^n es un semi-modulo sobre el semianillo (rig) ℕ,
ℤ^n es un modulo sobre el anillo ℤ,
ℝ^n es un espacio vectorial sobre el campo ℝ
-/

variable (R V : Type*) [Field R] [AddCommGroup V] [Module R V]
--Axiomas de espacio vectorial para la suma
#check add_assoc
#check add_comm
#check add_zero
#check add_left_neg
--Axiomas para el producto por escalar, llamado `smul`
#check smul_add
#check add_smul
#check one_smul
#check smul_smul
