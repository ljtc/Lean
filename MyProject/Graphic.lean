import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.GroupTheory.GroupAction.Defs

namespace Graphic
/-
A monoid M is graphic if it satifies the graphical identity,
aba = ab
-/
class GraphicMonoid (M : Type) extends Monoid M where
  graphic_id : ∀ a b : M, a * b * a = a * b

/-
Since a Graphic Monoid is a Monoid,
then it satisfies the axioms of monoid.
Of course, all the theorems for monoids in Mathlib are aviable
for graphic monoids.
-/
example {M : Type} [GraphicMonoid M] (a b c : M) :
    (a * b) * c = a * (b * c) := by
  rw[mul_assoc]

example {M : Type} [GraphicMonoid M] (a : M) : a * 1 = a := by
  rw [mul_one]

example {M : Type} [GraphicMonoid M] (a : M) : 1 * a = a := by
  rw [one_mul]

theorem elem_idem {M : Type} [GraphicMonoid M] (a : M) : a * a = a := by
  calc a * a
    _ = a * 1 * a := by rw [mul_one]
    _ = a * 1     := by rw [GraphicMonoid.graphic_id a 1]
    _ = a         := by rw [mul_one]

theorem unit_id {M : Type} [GraphicMonoid M] (a b : M) (h : a * b = 1)
    : a = 1 := by
  calc
    a

end Graphic
