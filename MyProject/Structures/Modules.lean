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
--posiblemente más pero ya lo olvidé


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
    add (add a b) c = add a (add b c) := sorry

protected theorem add_comm (a b : R2) : add a b = add b a := sorry

protected theorem zero_add (a : R2) : add zero a = a := sorry

protected theorem add_zero (a : R2) : add a zero = a := sorry

def nsmul := fun (n : ℕ) ↦ fun (a : R2) ↦ smul ↑n a

protected theorem nsmul_zero : ∀ a, nsmul 0 a = zero := sorry

protected theorem nsmul_succ :
    ∀ (n : ℕ) (a), nsmul (n + 1) a = add (nsmul n a) a := sorry


instance : AddCommMonoid R2 where
  add := sorry
  add_assoc := sorry
  zero := sorry
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry


protected theorem one_smul (a : R2) : smul (1 : ℝ) a = a := sorry

protected theorem mul_smul (r s : ℝ) (a : R2) :
    smul (r * s) a = smul r (smul s  a) := sorry

protected theorem smul_zero (r : ℝ) : smul r zero = zero := sorry
protected theorem smul_add (r : ℝ) (a b : R2) :
    smul r (add a b) = add (smul r a) (smul r b) := sorry

protected theorem add_smul (r s : ℝ) (a : R2) :
    smul (r + s) a = add (smul r a) (smul s a) := sorry

protected theorem zero_smul (a : R2) : smul (0 : ℝ) a = zero := sorry



instance : Module ℝ R2 where
  smul := sorry
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry


end MyR2


--Theorem 1.1 (Cancelation Law for Vector Adition)
example (x y z : V) (h : x + z = y + z) : x = y := sorry

--Corollary 1 (The vector 0 in unique)
example (x : V) (h : ∀ (y : V), y + x = y) : x = 0 := sorry

--Corollary 2 (Aditive inverse is unique)
