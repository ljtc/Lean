import Mathlib.Tactic.Use

variable( α : Type)
variable (A B C p q r: Prop)
variable (F G: α → Prop)

example: (∃x, F x →B) → ((∀x, F x)→B):= by
  intro ⟨w,Fw⟩ h
  exact Fw (h w)

example: (∃x, F x → G x) → ((∀x, F x) → ∃x, G x):= by
  intro ⟨r, Fr⟩ s
  exact ⟨r,Fr (s r)⟩

example: A ∨ B ↔ B ∨ A:=
  Iff.intro
  --A ∨ B → B ∨ A--
  (fun A_or_B => A_or_B.elim (fun a => Or.inr a) (fun b => Or.inl b))
  --B ∨ A → A ∨ B--
  (fun B_or_A => B_or_A.elim (fun b => Or.inr b) (fun a => Or.inl a))

example: A ∧ B ↔ B ∧ A:=
  Iff.intro
  --A ∧ B → B ∧ A--
  (fun A_and_B => And.intro (A_and_B.right) (A_and_B.left))
  --B ∧ A → B ∧ A--
  (fun B_and_A => And.intro (And.right B_and_A) (And.left B_and_A))

-- associativity of ∧ and ∨
example: (A ∧ B) ∧ C ↔ A ∧ (B ∧ C):=
  Iff.intro
  (fun ABC => And.intro (And.left (And.left ABC)) (And.intro (And.right (And.left ABC)) (And.right ABC)))
  (fun ABC => And.intro (And.intro (And.left ABC) (And.left (And.right ABC))) (And.right (And.right ABC)))

example: (A ∨ B) ∨ C ↔ A ∨ (B ∨ C):=
  Iff.intro
  (fun ABC => ABC.elim (fun AB => AB.elim (fun a => Or.inl a) (fun b => Or.inr (Or.inl b))) (fun c => Or.inr (Or.inr c)))
  (fun ABC => ABC.elim (fun a => Or.inl (Or.inl a)) (fun BC => BC.elim (fun b => Or.inl (Or.inr b)) (fun c => Or.inr c)))

-- distributivity
example: A ∧ (B ∨ C) ↔ (A ∧ B) ∨ (A ∧ C):=
  Iff.intro
  (fun ABC => (ABC.right).elim (fun b => Or.inl (And.intro (ABC.left) b)) (fun c => Or.inr (And.intro (ABC.left) c)))
  (fun ABAC => And.intro (ABAC.elim (fun AB => AB.left) (fun AC => AC.left)) (ABAC.elim (fun AB => Or.inl AB.right) (fun AC => Or.inr AC.right)))

example: A ∨ (B ∧ C) ↔ (A ∨ B) ∧ (A ∨ C):=
  Iff.intro
  (fun ABC => And.intro (ABC.elim (fun a => Or.inl a) (fun BC => Or.inr BC.left)) (ABC.elim (fun a => Or.inl a) (fun BC => Or.inr BC.right)))
  (fun ABAC => (ABAC.left).elim (fun a => Or.inl a) (fun b => (ABAC.right).elim (fun a => Or.inl a) (fun c => Or.inr (And.intro b c))))

-- other properties
example: (A → (B → C)) ↔ (A ∧ B → C):=
  Iff.intro
  (fun ABC => fun AB => (ABC (AB.left)) AB.right)
  (fun ABC => fun a => fun b => ABC (And.intro (a) (b)))

example: ((A ∨ B) → C) ↔ (A → C) ∧ (B → C):=
  Iff.intro
  (fun ABC => And.intro (fun a => ABC (Or.inl a)) (fun b => ABC (Or.inr b)))
  (fun ACBC => fun AB => AB.elim (fun a => ACBC.left a) (fun b => ACBC.right b))

example: ¬(A ∨ B) ↔ ¬A ∧ ¬B:=
  Iff.intro
  (fun AB => And.intro (fun a => AB (Or.inl a)) (fun b => AB (Or.inr b)))
  (fun AB => fun ab => ab.elim (fun a => AB.left a) (fun b => AB.right b))

example: ¬A ∨ ¬B → ¬(A ∧ B):=
  fun AB => fun ab => AB.elim (fun a => a ab.left) (fun b => b ab.right)

example: ¬(A ∧ ¬A):=
  fun AA => AA.right AA.left

example: A ∧ ¬B → ¬(A → B):=
  fun AB => fun ab => AB.right (ab AB.left)

example: ¬A → (A → B):=
  fun na => fun a => False.elim (na a)

example: (¬A ∨ B) → (A → B):=
  fun AB => fun a => AB.elim (fun na => False.elim (na a)) (fun b => b)

example : A ∨ False ↔ A :=
  Iff.intro
  (fun af => af.elim (fun a => a) (fun f => False.elim f))
  (fun a => Or.inl a)

example: A ∧ False ↔ False:=
  Iff.intro
  (fun af => af.right)
  (fun f => False.elim f)

example: (A → B) → (¬B → ¬A):=
  (fun AB => fun nb => fun a => nb (AB a))

example: ¬(A ↔ ¬A):=
  fun AA => (AA.mp  (AA.mpr ((fun AnA => (fun a => (AnA a) a)) (AA.mp)))) (AA.mpr ((fun AnA => (fun a => (AnA a) a)) (AA.mp)))

/-LOGICA CLASICA-/
open Classical

/-
Hint:
Usa Or.elim (em p)
Por ejemplo, en el primero intenta algo así
example : (A → B ∨ C) → ((A → B) ∨ (A → C)) :=
  fun ABC => Or.elim (Classical.em A)
    (fun hA => dem suponiendo que se vale A)
    (fun hnA => dem suponiendo que se vale ¬A)
-/

theorem hola : ¬A → A → B :=
  fun na => fun a => False.elim (na a)

theorem jaja: A → A ∨ B:=
fun a => Or.inl a

theorem adios : ¬A → (A → B) ∨ (A → C) :=
  fun na => ((fun na => fun a => False.elim (na a)) (na)).inl

example : (A → B ∨ C) → ((A → B) ∨ (A → C)) :=
  fun ABC => (em A).elim (fun a => (ABC a).elim (fun b => Or.inl (fun _ => b)) (fun c => Or.inr (fun d => c))) (fun na =>  (Or.inl (fun na => fun a => False.elim (na a))) ((Or.inr (fun na => fun a => False.elim (na a)))) )

example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry

example : ¬(p → q) → p ∧ ¬q := sorry

example : (p → q) → (¬p ∨ q) := sorry

example : (¬q → ¬p) → (p → q) := sorry

--Hint:
#check Classical.em p

example : p ∨ ¬p :=
fun pp => pp.elim (fun h => a) (fun hh => a)

example : (((p → q) → p) → p) := sorry
