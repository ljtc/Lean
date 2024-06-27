import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

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

def nsmul := fun (n : ℕ) ↦ fun (a : R2) ↦ smul ↑n a

def zsmul := fun (m : ℤ) ↦ fun (a : R2) ↦ smul ↑m a


/-
Lo siguiente es para usar +, • y - en lugar de add, smul y neg
en las operaciones con vectores
-/
instance : Add R2 where
  add := MyR2.add

instance : SMul ℝ R2 where
  smul := MyR2.smul

instance : Neg R2 where
  neg := MyR2.neg

instance : Zero R2 where
  zero := MyR2.zero


protected theorem add_assoc (a b c : R2) :
    (a + b) + c = a + (b + c) := by
  ext
  . exact add_assoc a.x b.x c.x
  . exact add_assoc a.y b.y c.y

protected theorem add_comm (a b : R2) : a + b = b + a := sorry

protected theorem zero_add (a : R2) : 0 + a = a := sorry

protected theorem add_zero (a : R2) : a + 0 = a := sorry

protected theorem add_left_neg (a : R2) : -a + a = 0 := sorry

protected theorem nsmul_zero : ∀ a, nsmul 0 a = zero := sorry

protected theorem nsmul_succ :
    ∀ (n : ℕ) (a), nsmul (n + 1) a = add (nsmul n a) a := sorry

protected theorem zsmul_zero' : ∀ a, zsmul 0 a = zero := sorry

protected theorem zsmul_succ' :
    ∀ (n : ℕ) (a : R2), zsmul (Int.ofNat n.succ) a = add (zsmul (Int.ofNat n) a)  a := sorry

protected theorem zsmul_neg' :
    ∀ (n : ℕ) (a : R2), zsmul (Int.negSucc n) a = neg (zsmul (↑n.succ) a) := sorry


instance : AddCommGroup R2 where
  add := sorry
  add_assoc := sorry
  zero := sorry
  zero_add := sorry
  add_zero := sorry
  add_comm := sorry
  nsmul := sorry
  nsmul_zero := sorry
  nsmul_succ := sorry
  neg := sorry
  zsmul := sorry
  zsmul_zero' := sorry
  zsmul_succ' := sorry
  zsmul_neg' := sorry
  add_left_neg := sorry


protected theorem one_smul (a : R2) : (1 : ℝ) • a = a := sorry

protected theorem mul_smul (r s : ℝ) (a : R2) :
    (r * s) • a = r • (s • a) := sorry

protected theorem smul_zero (r : ℝ) : r • (0 : R2) = 0 := sorry

protected theorem smul_add (r : ℝ) (a b : R2) :
    r • (a + b) = (r • a) + (r • b) := sorry

protected theorem add_smul (r s : ℝ) (a : R2) :
    (r + s) • a = (r • a) + (s • a) := sorry

protected theorem zero_smul (a : R2) : (0 : ℝ) • a = 0 := sorry


instance : Module ℝ R2 where
  smul := sorry
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry


end MyR2


--Theorem 1.1 (Ley de cancelación para la suma)
example (x y z : V) (h : x + z = y + z) : x = y := sorry

--Corolario 1 (El vector 0 es único)
example (x : V) (h : ∀ (y : V), y + x = y) : x = 0 := sorry

--Corollary 2 (Los inversos aditivos son únicos)
example (x y : V) (h : x + y = 0) : y = -x := sorry

--Theorem 1.2
--(a) 0x = 0
example (x : V) : (0 : R) • x = 0 := sorry

--(b) (-r)x = -(rx) = r(-x)
example (x : V) (r : R) : (-r) • x = -(r • x) := sorry

example (x : V) (r : R) : -(r • x) = r • -x := sorry

--(c) r0 = 0
example (r : R) : r • (0 : V) = 0 := sorry
