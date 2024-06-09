import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Set.Function
import Mathlib.Tactic.NormNum


/-
Lo siguiente es para evitar conflictos con las cosas que ya existen
en Mathlib. Los teoremas de abajo llevan el nombre que tienen en Mathlib.
-/
namespace MyGroup
variable {G : Type*} [Group G]
variable (a b c : G)
/-
Axiomas de grupo en Mathlib
-/
#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := sorry

theorem mul_one (a : G) : a * 1 = a := sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := sorry

theorem inv_uni {a b c : G} (h₁ : a * c = 1)
        (h₂ : b * a = 1) : b = c := sorry

example (h1 : ∀ a : G, a * b = a) (h2 : ∀ a : G, c * a = a) : b = c := sorry

example : (a⁻¹)⁻¹ = a := sorry

example (h : a * a = a) : a = 1 := sorry

example (h : a * b = a * c) : b = c := sorry


/-
Para cada x : G podemos definir una función Lx : G → G tal que
Lx(a) = x * a, multiplicar x por la izquierda. Análogamente, hay una
función que multiplica x por la derecha Rx : G → G.
-/
variable (x : G)
def L : G → G := fun (a : G) ↦ x * a
def R : G → G := fun (a : G) ↦ a * x

/-
La función Lx es biyectiva. Análogamente, Rx también es biyectiva.
-/
open Function

#print Injective
#print Surjective
#print Bijective

#check mul_left_cancel_iff

lemma Liny : Injective (fun a ↦ x * a) := sorry

lemma Lsupra : Surjective (fun a ↦ x * a) := sorry

lemma Lbiy : Bijective (fun a ↦ x * a) := sorry


end MyGroup


namespace MyRing
section
variable (R : Type*) [Ring R]
variable (a b c d : R)
/-
Axiomas de anillo en Mathlib
-/
#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)


theorem add_zero (a : R) : a + 0 = a := sorry

theorem add_right_neg (a : R) : a + -a = 0 := sorry

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := sorry

theorem add_neg_cancel_right (a b : R) : a + b + -b = a := sorry

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := sorry

theorem mul_zero (a : R) : a * 0 = 0 := sorry

theorem zero_mul (a : R) : 0 * a = 0 := sorry

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := sorry

theorem neg_neg (a : R) : - -a = a := sorry

lemma add_of_mul_neg_eq_zero (a b : R) : a * b + -a * b = 0 := sorry

theorem inv_uniq (a b c : R) (h₁ : a + c = 0) (h₂ : b + a = 0) : b = c := sorry

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := sorry

end


section conmutativo
variable (R : Type*) [CommRing R]
variable (a b c d : R)
#check (mul_comm: ∀ a b : R, a * b = b * a)

#check mul_neg
#check sub_eq_add_neg
#check add_right_neg
example : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := sorry

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := sorry

end conmutativo
end MyRing
