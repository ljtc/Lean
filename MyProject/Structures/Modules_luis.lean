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

protected theorem add_comm (a b : R2) : a + b = b + a := by
  ext
  repeat' apply add_comm

protected theorem zero_add (a : R2) : 0 + a = a := by
  ext
  repeat' apply zero_add

protected theorem add_zero (a : R2) : a + 0 = a := by
  ext
  repeat' apply add_zero

protected theorem add_left_neg (a : R2) : -a + a = 0 := by
  ext
  repeat' apply add_left_neg

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

protected theorem zsmul_zero' : ∀ a, zsmul 0 a = zero := by
  intro a
  rw [zsmul, smul]
  ext <;> dsimp
  repeat (first | rw [Int.cast_zero] | apply zero_mul)

protected theorem zsmul_succ' :
    ∀ (n : ℕ) (a : R2), zsmul (Int.ofNat n.succ) a = add (zsmul (Int.ofNat n) a)  a := by
  intro n a
  simp only [zsmul, smul, add]
  ext <;> dsimp
  repeat' rw [Nat.cast_succ,Int.cast_add,Int.cast_one,add_mul,one_mul]

protected theorem zsmul_neg' :
    ∀ (n : ℕ) (a : R2), zsmul (Int.negSucc n) a = neg (zsmul (↑n.succ) a) := by
  intro n a
  simp only [zsmul, smul, neg]
  ext <;> dsimp
  repeat' rw [Int.negSucc_coe, Int.cast_neg, neg_mul]


instance : AddCommGroup R2 where
  add := MyR2.add
  add_assoc := MyR2.add_assoc
  zero := MyR2.zero
  zero_add := MyR2.zero_add
  add_zero := MyR2.add_zero
  add_comm := MyR2.add_comm
  nsmul := MyR2.nsmul
  nsmul_zero := MyR2.nsmul_zero
  nsmul_succ := MyR2.nsmul_succ
  neg := MyR2.neg
  zsmul := MyR2.zsmul
  zsmul_zero' := MyR2.zsmul_zero'
  zsmul_succ' := MyR2.zsmul_succ'
  zsmul_neg' := MyR2.zsmul_neg'
  add_left_neg := MyR2.add_left_neg


protected theorem one_smul (a : R2) : (1 : ℝ) • a = a := by
  ext
  repeat' apply one_mul

protected theorem mul_smul (r s : ℝ) (a : R2) :
    (r * s) • a = r • (s • a) := by
  ext
  repeat' apply mul_assoc

protected theorem smul_zero (r : ℝ) : r • (0 : R2) = 0 := by
  ext
  repeat' apply mul_zero

protected theorem smul_add (r : ℝ) (a b : R2) :
    r • (a + b) = (r • a) + (r • b) := by
  ext
  repeat' apply mul_add

protected theorem add_smul (r s : ℝ) (a : R2) :
    (r + s) • a = (r • a) + (s • a) := by
  ext
  repeat' apply add_mul

protected theorem zero_smul (a : R2) : (0 : ℝ) • a = 0 := by
  ext
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


--Theorem 1.1 (Ley de cancelación para la suma)
example (x y z : V) (h : x + z = y + z) : x = y := by
  apply add_right_cancel h

--Corolario 1 (El vector 0 es único)
example (x : V) (h : ∀ (y : V), y + x = y) : x = 0 := by
  calc
    x = 0 + x := by rw [zero_add]
    _ = 0     := by rw [(h 0)]

--Corollary 2 (Los inversos aditivos son únicos)
example (x y : V) (h : x + y = 0) : y = -x := by
  exact (neg_eq_of_add_eq_zero_right h).symm

--Theorem 1.2
--(a) 0x = 0
example (x : V) : (0 : R) • x = 0 := by
  exact zero_smul R x

--(b) (-r)x = -(rx) = r(-x)
example (x : V) (r : R) : (-r) • x = -(r • x) := by sorry

example (x : V) (r : R) : -(r • x) = r • -x := by sorry

--(c) r0 = 0
example (r : R) : r • (0 : V) = 0 := by
  exact smul_zero r
