
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
--import Mathlib.Data.Nat.Parity--

section Set

variable {α : Type*}
variable (s t u : Set α)
open Set

example {p: Prop} : ¬ (p ↔ ¬ p) := by
  intro ⟨pnp,npp⟩
  have np : ¬ p := by
    intro hp
    exact pnp hp hp
  have nnp : ¬ ¬ p := by
    intro hnp
    exact hnp (npp hnp)
  exact nnp np


#check subset_def
#check inter_def
#check mem_setOf
#check inter_def
#check mem_inter_iff

#check union_def
#check mem_union

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def]--expands the definition of subset in the goal
  rw [inter_def, inter_def]--expands the intersections in the goal
  rw [subset_def] at h--expands the subset in the hypotesis
  simp only [mem_setOf]
  --Now we have to prove a logical proposition
  intro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  --first we expand the definitions of subset and intersection everywhere
  simp only [subset_def, mem_inter_iff] at *
  --the result is a logical proposition
  intro x ⟨xs, xu⟩
  exact ⟨h x xs, xu⟩



--
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  λ _ =>
    λ ⟨xs,xu⟩ =>
      ⟨h xs,xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨xs,xu⟩
  exact ⟨h xs,xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x ⟨xs,xu⟩
  constructor
  . exact h xs
  . exact xu
--
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u :=
  λ _ =>
    λ ⟨xs,xtu⟩ =>
      Or.elim xtu
      (λ xt => Or.inl ⟨xs,xt⟩)
      (λ xu => Or.inr ⟨xs,xu⟩)

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x ⟨xs,xtu⟩
  rcases xtu with xt | xu
  . exact Or.inl ⟨xs,xt⟩
  . exact Or.inr ⟨xs,xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs,xt | xu⟩
  . left
    exact ⟨xs,xt⟩
  . right
    exact ⟨xs,xu⟩

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  simp only [subset_def, mem_inter_iff]
  intro x xs_tu
  cases xs_tu.2
  case inl xt =>
    left
    exact ⟨xs_tu.1,xt⟩
  case inr xu =>
    right
    exact ⟨xs_tu.1,xu⟩

--
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) :=
  λ _ =>
    λ xst_su =>
      Or.elim xst_su
        (λ ⟨xs,xt⟩ => ⟨xs,Or.inl xt⟩)
        (λ ⟨xs,xu⟩ => ⟨xs,Or.inr xu⟩)

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  intro x xst_su
  constructor
  . rcases xst_su with xst | xsu
    . exact xst.1
    . exact xsu.1
  . cases xst_su
    case inl xst =>
      exact Or.inl xst.2
    case inr xsu =>
      exact Or.inr xsu.2

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
  rintro x (⟨xs,xt⟩ | ⟨xs,xu⟩)
  . exact ⟨xs,Or.inl xt⟩
  . exact ⟨xs, Or.inr xu⟩


--
example : s ⊆ s ∪ t :=
  λ _ =>
    λ xs =>
      Or.inl xs

example : s ⊆ s ∪ t := by
  intro x xs
  exact Or.inl xs
--
example : s ∩ t ⊆ s :=
  λ _ =>
    λ ⟨xs,_⟩ =>
      xs

example : s ∩ t ⊆ s :=
  λ _ =>
    λ xst =>
      xst.1

example : s ∩ t ⊆ s := by
  intro x xst
  exact xst.1

example : s ∩ t ⊆ s := by
  rw [subset_def]
  intro x xst
  exact xst.1
--
example (h : u ⊆ s) (h' : u ⊆ t) : u ⊆ s ∩ t :=
  λ _ =>
    λ xu =>
      ⟨h xu,h' xu⟩

example (h : u ⊆ s) (h' : u ⊆ t) : u ⊆ s ∩ t := by
  intro x xu
  exact ⟨h xu,h' xu⟩
--
example (h : s ⊆ u) (h' : t ⊆ u) : s ∪ t ⊆ u :=
  λ _ =>
    λ xsu =>
      Or.elim xsu
        (λ xs => h xs)
        (λ xt => h' xt)

example (h : s ⊆ u) (h' : t ⊆ u) : s ∪ t ⊆ u := by
  intro x xst
  rcases xst with xs | xt
  . exact h xs
  . exact h' xt

example (h : s ⊆ u) (h' : t ⊆ u) : s ∪ t ⊆ u := by
  rintro x (xs | xt)
  . exact h xs
  . exact h' xt

--
example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) :=
  λ _ =>
    λ ⟨xs,xtu⟩ =>
      Or.elim xtu
        (λ xt => Or.inl ⟨xs,xt⟩)
        (λ xu => Or.inr ⟨xs,xu⟩)

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := by
  rw [subset_def, inter_def]
  rintro x ⟨xs, xt | xu⟩
  . left
    exact ⟨xs,xt⟩
  . right
    exact ⟨xs,xu⟩

--
example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) :=
  λ _ =>
    λ xst_su =>
      Or.elim xst_su
        (λ xst => ⟨xst.1,Or.inl xst.2⟩)
        (λ xsu => ⟨xsu.1,Or.inr xsu.2⟩)

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := by
  rintro x (xst | xsu )
  . exact ⟨xst.1,Or.inl xst.2⟩
  . exact ⟨xsu.1,Or.inr xsu.2⟩

--

#check Set.diff_eq
#check Set.mem_diff

--
example : (s \ t) \ u ⊆ s \ (t ∪ u) :=
  λ _ =>
    λ xs_ntu =>
      ⟨xs_ntu.1.1 ,
      λ xtu =>
        Or.elim xtu
          (λ xt => xs_ntu.1.2 xt)
          (λ xu => xs_ntu.2 xu)⟩

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x ⟨⟨xs,xnt⟩,xnu⟩
  constructor
  . exact xs
  . intro xtu
    rcases xtu with xt | xu
    . exact xnt xt
    . exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x ⟨⟨xs,xnt⟩,xnu⟩
  exact ⟨xs,λ xtu => Or.elim xtu (λ xt => xnt xt) (λ xu => xnu xu)⟩

--

example : s \(t ∪ u) ⊆ (s \ t) \ u :=
  λ _ =>
    λ ⟨xs,xntu⟩ =>
      ⟨⟨xs,λ xt => xntu (Or.inl xt)⟩,λ xu => xntu (Or.inr xu)⟩


example : s \(t ∪ u) ⊆ (s \ t) \ u := by
  intro x xs_ntu
  constructor
  . constructor
    . exact xs_ntu.1
    . intro xt
      exact xs_ntu.2 (Or.inl xt)
  . intro xu
    exact xs_ntu.2 (Or.inr xu)

example : s \(t ∪ u) ⊆ (s \ t) \ u := by
  simp only [subset_def, mem_diff]
  intro x ⟨xs,xntu⟩
  constructor
  . constructor
    . exact xs
    . intro xt
      exact xntu (Or.inl xt)
  . intro xu
    exact xntu (Or.inr xu)
--


#check ext

example : s ∩ t = t ∩ s :=
  Set.ext λ _ =>
    ⟨λ ⟨xs,xt⟩ => ⟨xt,xs⟩,
    λ ⟨xt,xs⟩ => ⟨xs,xt⟩⟩

example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  . intro ⟨xs,xt⟩ ; exact ⟨xt,xs⟩
  . intro ⟨xt,xs⟩ ; exact ⟨xs,xt⟩

example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  . intro x xst
    exact ⟨xst.2,xst.1⟩
  . intro x xts
    exact ⟨xts.2,xts.1⟩

--
example : s ∪ t = t ∪ s :=
  Set.ext λ _ =>
    ⟨λ xst => Or.elim xst (λ xs => Or.inr xs) (λ xt => Or.inl xt),
    λ xts => Or.elim xts (λ xt => Or.inr xt) (λ xs => Or.inl xs)⟩

example : s ∪ t = t ∪ s := by
  ext x
  constructor
  . intro xst
    rcases xst with xs | xt
    . right
      exact xs
    . left
      exact xt
  . intro xts
    cases xts
    case inl xt =>
      right
      exact xt
    case inr xs =>
      left
      exact xs
--
example (h : s ⊆ t) : s = s ∩ t :=
  Set.ext λ _ =>
    ⟨λ xs =>
      ⟨xs,h xs⟩,
    λ ⟨xs,_⟩ =>
      xs⟩

example (h : s ⊆ t) : s = s ∩ t := by
  ext x
  constructor
  . intro xs
    exact ⟨xs,h xs⟩
  . intro xst
    exact xst.1

example (h : s ⊆ t) : s = s ∩ t := by
  ext x
  simp only [mem_inter_iff]
  constructor
  . intro xs
    constructor
    . assumption
    . exact h xs
  . intro xst
    exact xst.1

--
example (h : s ⊆ t) : t = s ∪ t :=
  Set.ext λ _ =>
    ⟨λ xt =>
      Or.inr xt,
    λ xst =>
      Or.elim xst (λ xs => h xs) (λ xt => xt)⟩

example (h : s ⊆ t) : t = s ∪ t := by
  ext x
  constructor
  . intro xt
    right
    exact xt
  . intro xst
    rcases xst with xs | xt
    . exact h xs
    . exact xt

example (h : s ⊆ t) : t = s ∪ t := by
  ext x
  simp only [union_def, mem_setOf]
  constructor
  . intro xt
    right
    exact xt
  . intro xst
    rcases xst with xs | xt
    . exact h xs
    . exact xt

--
example : s ∩ (s ∪ t) = s :=
  Set.ext
    λ _ =>
      ⟨λ ⟨xs,_⟩ =>
        xs,
      λ xs =>
        ⟨xs,Or.inl xs⟩⟩

example : s ∩ (s ∪ t) = s := by
  ext x
  constructor
  . intro xs_sot
    exact xs_sot.1
  . intro xs
    constructor
    . exact xs
    . exact Or.inl xs

example : s ∩ (s ∪ t) = s := by
  ext x
  simp only [inter_def,union_def, mem_setOf]
  constructor
  . intro xs_sot
    exact xs_sot.1
  . intro xs
    constructor
    . exact xs
    . exact Or.inl xs

--
example : s ∪ s ∩ t = s :=
  Set.ext
    λ _ =>
      ⟨λ xs_st =>
        Or.elim xs_st (λ xs => xs) (λ ⟨xs,_⟩ => xs),
      λ xs =>
        Or.inl xs⟩

example : s ∪ s ∩ t = s := by
  ext x
  constructor
  . rintro (xs | xst)
    . exact xs
    . exact xst.1
  . intro xs
    exact Or.inl xs

example : s ∪ s ∩ t = s := by
  ext x
  simp only [union_def, inter_def, mem_setOf]
  constructor
  . rintro (xs | xst)
    . exact xs
    . exact xst.1
  . intro xs
    exact Or.inl xs

--
example : s \ t ∪ t = s ∪ t :=
  Set.ext
    λ x =>
      ⟨λ xst_t =>
        Or.elim xst_t (λ ⟨xs,_⟩ => Or.inl xs) (λ xt => Or.inr xt),
      λ xs_t =>
        Or.elim xs_t
          (λ xs =>
            Or.elim (Classical.em (x ∈ t))
              (λ xt => Or.inr xt)
              (λ xnt => Or.inl ⟨xs,xnt⟩))
          (λ xt => Or.inr xt)⟩

example : s \ t ∪ t = s ∪ t := by
  ext x
  constructor
  . intro xst_t
    cases xst_t
    case inl xst =>
      exact Or.inl xst.1
    case inr xt =>
      exact Or.inr xt
  . intro xst
    rcases xst with xs | xt
    . cases Classical.em (x ∈ t)
      case inl xt =>
        exact Or.inr xt
      case inr xnt =>
        exact Or.inl ⟨xs,xnt⟩
    . exact Or.inr xt

example : s \ t ∪ t = s ∪ t := by
  ext x
  simp only [union_def, diff_eq, inter_def, mem_setOf]
  constructor
  . intro xst_t
    cases xst_t
    case inl xst =>
      exact Or.inl xst.1
    case inr xt =>
      exact Or.inr xt
  . intro xst
    rcases xst with xs | xt
    . rcases Classical.em (x∈ t) with xt | xnt
      . exact Or.inr xt
      . exact Or.inl ⟨xs,xnt⟩
    . exact Or.inr xt

--
-- Auxiliares
theorem su1 {_: α} {s t : Set α} : s ⊆ s ∪ t ∧ t ⊆ s ∪ t :=
  ⟨λ _ =>
    λ xs =>
      Or.inl xs,
  λ _ =>
    λ xt =>
      Or.inr xt⟩

theorem sy1 {_: α} {s t : Set α} :  s ∩ t ⊆ s ∧ s ∩ t ⊆ t :=
  ⟨λ _ =>
    λ xst =>
      xst.1,
  λ _ =>
    λ xst =>
      xst.2⟩

theorem t1  {x: α} {s t : Set α} (h : s ⊆ t) :  (x ∉ t → x ∉ s) :=
  λ xnt =>
    λ xs =>
      xnt (h xs)

theorem t2 {α : Type*} {s t : Set α} {x : α} :  (x ∉ t → x ∉ s ∩ t) ∧ (x ∉ s → x ∉ s ∩ t) :=
  ⟨λ xnt =>
    λ xst =>
      xnt xst.2,
  λ xns =>
    λ xst =>
      xns xst.1⟩

theorem t3 {α : Type*} {s t : Set α} {x : α} : x ∉ (s ∪ t) ↔ x ∉ s ∧ x ∉ t :=
  ⟨λ xnst =>
    have l1 : s ⊆ s ∪ t ∧ t ⊆ s ∪ t :=
      ⟨λ _ =>
        λ xs =>
          Or.inl xs,
      λ _ =>
        λ xt =>
          Or.inr xt⟩
    ⟨t1 l1.1 xnst, t1 l1.2 xnst⟩,
    --⟨((t1 l1.1) x) xnst, ((t1 l1.2) x) xnst⟩ ,
  λ ⟨xns,xnt⟩ =>
    λ xst =>
      Or.elim xst
        (λ xs => xns xs)
        (λ xt => xnt xt)⟩

theorem t4 {α : Type*} {s t : Set α} {x : α} : x ∉ (s ∩ t) ↔ x ∉ s ∨ x ∉ t :=
  ⟨λ xnst =>
    Or.elim (Classical.em (x ∈ s) )
      (λ xs =>
        Or.elim (Classical.em (x ∈ t))
          (λ xt =>
            False.elim (xnst ⟨xs,xt⟩))
          (λ xnt =>
            Or.inr xnt))
      (λ xns =>
        Or.inl xns),
  λ xns_nt =>
    have ⟨l1,l2⟩ : s ∩ t ⊆ s ∧ s ∩ t ⊆ t :=
      ⟨λ _ =>
        λ xst =>
          xst.1,
      λ _ =>
        λ xst =>
          xst.2⟩
    Or.elim xns_nt
      (λ xns =>
        t1 l1 xns)
      (λ xnt =>
        t1 l2 xnt)⟩

example {α : Type*} {s t : Set α} {x : α} : x ∉ (s ∩ t) ↔ x ∉ s ∨ x ∉ t := by
  constructor
  . intro xnst
    rcases Classical.em (x ∈ s) with xs | xns
    . rcases Classical.em (x ∈ t) with xt | xnt
      . exfalso
        exact xnst ⟨xs,xt⟩
      . exact Or.inr xnt
    . exact Or.inl xns
  . intro xns_nt
    have ⟨l1,l2⟩ : s ∩ t ⊆ s ∧ s ∩ t ⊆ t := by
      constructor
      . intro x xst
        exact xst.1
      . intro x xst
        exact xst.2
    cases xns_nt
    case inl xns =>
      exact t1 l1 xns
    case inr xnt =>
      exact t1 l2 xnt


--
example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) :=
  Set.ext
    λ x =>
      ⟨λ xst_ts =>
        Or.elim xst_ts
          (λ ⟨xs,xnt⟩ =>
            ⟨Or.inl xs,t2.1 xnt⟩)
          (λ ⟨xt,xns⟩ =>
            ⟨Or.inr xt, t2.2 xns⟩),
      λ ⟨xsot,xnst⟩ =>
        Or.elim xsot
          (λ xs =>
            Or.elim (Classical.em (x ∈ t))
              (λ xt =>
                False.elim (xnst ⟨xs,xt⟩))
              (λ xnt =>
                Or.inl ⟨xs,xnt⟩))
          (λ xt =>
            Or.elim (Classical.em (x ∈ s))
              (λ xs =>
                False.elim (xnst ⟨xs,xt⟩))
              (λ xns =>
                Or.inr ⟨xt,xns⟩))⟩

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x
  constructor
  . rintro  (⟨xs,xnt⟩ | ⟨xt,xns⟩)
    . have xnst : x ∉ s ∩ t :=
        λ xst => xnt xst.2
      exact ⟨Or.inl xs, xnst⟩
    . have xnst : x ∉ s ∩ t :=
        λ xst => xns xst.1
      exact ⟨Or.inr xt, xnst⟩
  . rintro ⟨(xs | xt),xnst⟩
    . cases Classical.em (x ∈ t)
      case inl xt =>
        absurd xnst
        exact ⟨xs,xt⟩
      case inr xnt =>
        exact Or.inl ⟨xs,xnt⟩
    . rcases Classical.em (x ∈ s) with xs | xns
      . absurd xnst
        exact ⟨xs,xt⟩
      . exact Or.inr ⟨xt,xns⟩

--
example : ∅ ⊆ s := by
  simp only [subset_def]
  intro x xo
  exfalso
  exact xo
--

#check mem_compl_iff
example : s ⊆ t ↔ s ∩ tᶜ = ∅ :=
  ⟨λ hs_t =>
    Set.ext λ _ =>
      ⟨λ ⟨xs,xtc⟩ =>
        xtc (hs_t xs),
      λ xo =>
        False.elim (xo)⟩,
  λ sytc =>
    λ x =>
      λ xs =>
        Or.elim (Classical.em (x ∈ tᶜ))
          (λ xtc =>
            have l1 : x ∈ s ∩ tᶜ :=
              ⟨xs,xtc⟩
            False.elim (((Set.ext_iff.mp sytc) x).mp l1) )
          (λ xntc =>
            Set.not_mem_compl_iff.mp xntc) ⟩

example : s ⊆ t ↔ s ∩ tᶜ = ∅ := by
  constructor
  . intro hs_t
    ext x
    constructor
    . intro ⟨xs,xtc⟩
      exact xtc (hs_t xs)
    . intro o
      exfalso
      exact o
  . intro xstc x xs
    rcases Classical.em (x ∈ tᶜ) with xtc | xntc
    . have l1 : x ∈ s ∩ tᶜ := by
        exact ⟨xs,xtc⟩
      rw [xstc] at l1
      exfalso
      exact l1
    . rw [not_mem_compl_iff] at xntc
      exact xntc
--
example : s \ (t ∪ u) = (s \ t) ∩ (s \ u) :=
  Set.ext λ _ =>
    ⟨λ ⟨xs,xntu⟩ =>
      ⟨⟨xs, (t3.mp xntu).1⟩,⟨xs,(t3.mp xntu).2⟩⟩,
    λ ⟨⟨xs,xnt⟩,⟨_,xnu⟩⟩ =>
      ⟨xs,t3.mpr ⟨xnt,xnu⟩⟩⟩

example : s \ (t ∪ u) = (s \ t) ∩ (s \ u) := by
  ext x
  constructor
  . intro ⟨xs,xntu⟩
    constructor
    . constructor
      . exact xs
      . exact (t3.mp xntu).1
    . constructor
      . exact xs
      . exact (t3.mp xntu).2
  . intro ⟨xs_nt,xs_nu⟩
    constructor
    . exact xs_nt.1
    . exact t3.mpr ⟨xs_nt.2,xs_nu.2⟩

--
example : s \ (t ∩ u) = (s \ t) ∪ (s \ u) :=
  Set.ext λ _ =>
    ⟨λ ⟨xs,xntu⟩ =>
      Or.elim (t4.mp xntu)
        (λ xnt =>
          Or.inl ⟨xs,xnt⟩)
        (λ xnu =>
          Or.inr ⟨xs,xnu⟩),
    λ xst_su =>
      Or.elim xst_su
        (λ ⟨xs,xnt⟩ =>
          have l1 : t ∩ u ⊆ t :=
            λ _ =>
              λ xtu =>
                xtu.1
          ⟨xs, t1 l1 xnt ⟩)
        (λ ⟨xs,xnu⟩ =>
          have l2 : t ∩ u ⊆ u :=
            λ _ =>
              λ xtu =>
                xtu.2
          ⟨xs,t1 l2 xnu⟩)⟩


example : s \ (t ∩ u) = (s \ t) ∪ (s \ u) := by
  ext x
  simp only [mem_diff,mem_union]
  constructor
  . intro ⟨xs,xntu⟩
    rcases t4.mp xntu with xnt | xnu
    . left
      exact ⟨xs,xnt⟩
    . right
      exact  ⟨xs,xnu⟩
  . rintro (⟨xs,xnt⟩ | ⟨xs,xnu⟩)
    . have l1 : t ∩ u ⊆ t :=
        λ _ =>
          λ xtu =>
            xtu.1
      constructor
      . exact xs
      . exact t1 l1 xnt
    . have l2 : t ∩ u ⊆ u :=
        λ _ =>
          λ xtu =>
            xtu.2
      constructor
      . exact xs
      . exact t1 l2 xnu






/-
example : s ⊆ s ∪ t := sorry

example : s ∩ t ⊆ s := sorry

example (h : u ⊆ s) (h' : u ⊆ t) : u ⊆ s ∩ t := sorry

example (h : s ⊆ u) (h' : t ⊆ u) : s ∪ t ⊆ u := sorry

example : s ∩ (t ∪ u) ⊆ (s ∩ t) ∪ (s ∩ u) := sorry

example : (s ∩ t) ∪ (s ∩ u) ⊆ s ∩ (t ∪ u) := sorry

#check Set.diff_eq
#check Set.mem_diff
example : (s \ t) \ u ⊆ s \ (t ∪ u) := sorry

example : s ∩ t = t ∩ s := by

example (h : s ⊆ t) : s = s ∩ t :=

example (h : s ⊆ t) : t = s ∪ t :=

example : s ∩ (s ∪ t) = s :=

example : s ∪ s ∩ t = s := sorry

example : s \ t ∪ t = s ∪ t :=

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) :=

#check mem_compl_iff
example : s ⊆ t ↔ s ∩ tᶜ = ∅ :=

example : s \ (t ∪ u) = (s \ t) ∩ (s \ u) :=

example : s \ (t ∩ u) = (s \ t) ∪ (s \ u) :=
-/


--Arbitrary unions and intersections

variable {I : Type*}
variable {A B : I → Set α}


#check mem_inter_iff
#check mem_iUnion


example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s :=
  Set.ext λ x =>
    ⟨λ ⟨xs,xiai⟩ =>
      have ⟨i,xai⟩ : ∃ i, x ∈ A i :=
        Set.mem_iUnion.mp xiai
      Set.mem_iUnion.mpr ⟨i, ⟨xai,xs⟩⟩,
    λ xiai_s =>
      have ⟨i,⟨xai,xs⟩⟩ : ∃ i, x ∈ A i ∩ s :=
        Set.mem_iUnion.mp xiai_s
      ⟨xs,Set.mem_iUnion.mpr ⟨i,xai⟩⟩⟩

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  . intro ⟨xs,⟨i,xai⟩⟩
    exact ⟨i,⟨xai,xs⟩⟩
  . intro ⟨i,xai_s⟩
    exact ⟨xai_s.2, ⟨i,xai_s.1⟩⟩

#check mem_iInter
example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i :=
  Set.ext λ x =>
    ⟨λ hai_bi =>
      have l1 : ∀ i, x ∈ A i ∩ B i :=
        Set.mem_iInter.mp hai_bi
      have l2 : (∀ i, x ∈ A i) :=
        λ i =>
          (l1 i).1
      have l3 : (∀ i, x ∈ B i) :=
        λ i =>
          (l1 i).2
      ⟨Set.mem_iInter.mpr l2, Set.mem_iInter.mpr l3⟩,
    λ ⟨hai,hbi⟩ =>
      have l4 : ∀ i, x ∈ A i ∩ B i :=
        λ i =>
          ⟨(Set.mem_iInter.mp hai) i,
          (Set.mem_iInter.mp hbi) i⟩
      Set.mem_iInter.mpr l4⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_iInter, mem_inter_iff]
  constructor
  . intro hxai_bi
    constructor
    . intro i
      exact (hxai_bi i).1
    . intro i
      exact (hxai_bi i).2
  . intro hai_bi i
    constructor
    . exact hai_bi.1 i
    . exact hai_bi.2 i

--
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s :=
  Set.ext λ x =>
    ⟨λ xs_yai =>
       Set.mem_iInter.mpr (λ i =>
        Or.elim xs_yai
          (λ xs =>
            Or.inr xs )
          (λ xai =>
            Or.inl ( (Set.mem_iInter.mp xai) i) ) ) ,
    λ xyai_s =>
      Or.elim (Classical.em (x ∈ s))
        (λ xs =>
          Or.inl xs)
        (λ xns =>
          have l1 : ∀ i, x ∈ A i :=
            λ i =>
              Or.elim ((Set.mem_iInter.mp xyai_s) i)
                (λ xai =>
                  xai)
                (λ xs =>
                  False.elim (xns xs) )
          Or.inr (Set.mem_iInter.mpr l1))⟩

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_iInter,mem_inter_iff,mem_union]
  constructor
  . rintro (xs | xyai) i
    . exact Or.inr xs
    . exact Or.inl  (xyai i )
  . intro xai_s
    by_cases h  : x ∈ s
    . exact Or.inl h
    . have l1 : ∀ i, x ∈ A i := by
        intro i
        rcases (xai_s i) with xai | xs
        . exact xai
        . exfalso
          exact h xs
      exact Or.inr l1

--
#check mem_diff
#check mem_iInter
#check mem_iUnion
example (j : I) : ⋂ i, s \ A i ⊆ s \ ⋃ i, A i :=
    λ x =>
      λ xys_ia =>
        ⟨((Set.mem_iInter.mp xys_ia) j).1,
        λ xuai =>
          have ⟨i,xai⟩ : ∃ i, x ∈ A i :=
            Set.mem_iUnion.mp xuai
          ((Set.mem_iInter.mp xys_ia) i).2 xai⟩


example (j : I) : ⋂ i, s \ A i ⊆ s \ ⋃ i, A i := by
  intro x
  simp only [mem_diff, mem_iInter, mem_iUnion]
  intro xys_ai
  constructor
  . exact (xys_ai j).1
  . intro ⟨i,xai⟩
    exact (xys_ai i).2 xai

--
example : s \ ⋃ i, A i ⊆ ⋂ i, s \ A i :=
  λ _ =>
    λ ⟨xs,xnuai⟩ =>
      Set.mem_iInter.mpr (λ i =>
        ⟨xs,
        λ xai =>
          xnuai (Set.mem_iUnion.mpr ⟨i,xai⟩)⟩)

example : s \ ⋃ i, A i ⊆ ⋂ i, s \ A i := by
  intro x
  simp only [mem_diff, mem_iUnion, mem_iInter]
  intro ⟨xs,xnai⟩ i
  constructor
  . exact xs
  . intro xai
    exact xnai ⟨i,xai⟩


/-
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s :=

#check mem_iInter
example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i :=

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s :=

#check mem_diff
#check mem_iInter
#check mem_iUnion
example (j : I) : ⋂ i, s \ A i ⊆ s \ ⋃ i, A i :=

example : s \ ⋃ i, A i ⊆ ⋂ i, s \ A i :=
-/


end Set
