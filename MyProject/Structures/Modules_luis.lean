import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic

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


namespace MyR2
--una forma de definir ℝ²
@[ext] --dos parejas son iguales si coinciden en sus coordenadas por ext
structure R2 where
  x : ℝ
  y : ℝ

example (a b : R2) (hx : a.x = b.x) (hy : a.y = b.y) : a = b := by
  ext <;> assumption

def add (a b : R2) : R2 := ⟨a.x + b.x, a.y + b.y⟩
/-Una forma alternativa es:
def add (a b : R2) : R2 where
  x := a.x + b.x
  y := a.y + b.y
-/

def neg (a : R2) : R2 := ⟨-a.x, -a.y⟩

def zero : R2 := ⟨0, 0⟩

def smul (r : ℝ) (a : R2) : R2 := ⟨r * a.x, r * a.y⟩

protected theorem add_assoc (a b c : R2) :
    add (add a b) c = add a (add b c) := by
  simp only [add]
  ext <;> dsimp
  . exact add_assoc a.x b.x c.x
  . exact add_assoc a.y b.y c.y

protected theorem add_comm (a b : R2) : add a b = add b a := by
  rw [add, add]
  ext <;> dsimp
  repeat' apply add_comm

protected theorem zero_add (a : R2) : add zero a = a := by
  rw [add]
  ext <;> dsimp
  repeat' apply zero_add

protected theorem add_zero (a : R2) : add a zero = a := by
  rw [add]
  ext <;> dsimp
  repeat' apply add_zero

def nsmul := fun (n : ℕ) ↦ fun (a : R2) ↦ smul ↑n a

protected theorem nsmul_zero : ∀ a, nsmul 0 a = zero := by
  intro a
  rw [nsmul, smul]
  ext <;> dsimp
  . rw [Nat.cast_zero]
    apply zero_mul
  . rw [Nat.cast_zero]
    apply zero_mul

protected theorem nsmul_succ :
    ∀ (n : ℕ) (a), nsmul (n + 1) a = add (nsmul n a) a := by
  intro n a
  simp only [nsmul, smul, add]
  ext <;> dsimp
  repeat' rw [Nat.cast_succ, add_mul, one_mul]


instance : AddCommMonoid R2 where
  add := MyR2.add
  add_assoc := MyR2.add_assoc
  zero := MyR2.zero
  zero_add := MyR2.zero_add
  add_zero := MyR2.add_zero
  add_comm := MyR2.add_comm
  nsmul := MyR2.nsmul
  nsmul_zero := MyR2.nsmul_zero
  nsmul_succ := MyR2.nsmul_succ


protected theorem one_smul (a : R2) : smul (1 : ℝ) a = a := by
  rw [smul]
  ext <;> dsimp
  repeat' apply one_mul

protected theorem mul_smul (r s : ℝ) (a : R2) :
    smul (r * s) a = smul r (smul s  a) := by
  simp only [smul]
  ext <;> dsimp
  repeat' apply mul_assoc

protected theorem smul_zero (r : ℝ) : smul r zero = zero := by
  rw [smul]
  ext <;> dsimp
  repeat' apply mul_zero

protected theorem smul_add (r : ℝ) (a b : R2) :
    smul r (add a b) = add (smul r a) (smul r b) := by
  simp only [add, smul]
  ext <;> dsimp
  repeat' apply mul_add

protected theorem add_smul (r s : ℝ) (a : R2) :
    smul (r + s) a = add (smul r a) (smul s a) := by
  simp only [smul, add]
  ext <;> dsimp
  repeat' apply add_mul

protected theorem zero_smul (a : R2) : smul (0 : ℝ) a = zero := by
  simp only [smul]
  ext <;> dsimp
  repeat' apply zero_mul



instance : Module ℝ R2 where
  smul := MyR2.smul
  one_smul := MyR2.one_smul
  mul_smul := MyR2.mul_smul
  smul_zero := MyR2.smul_zero
  smul_add := MyR2.smul_add
  add_smul := MyR2.add_smul
  zero_smul := MyR2.zero_smul


end MyR2


--Theorem 1.1 (Cancelation Law for Vector Adition)
example (x y z : V) (h : x + z = y + z) : x = y := by
  apply add_right_cancel h
