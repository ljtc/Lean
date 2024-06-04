import Mathlib.Tactic.Use
--import Mathlib.Data.Nat.Basic
--import Mathlib.Data.Nat.Parity
import Mathlib.Data.Real.Basic
--import MIL.Common


section LJ1


--constant p q : Prop
variable (A B C : Prop)
variable (α : Type)
variable (F  G : α → Prop)
variable (p q r : Prop)

--theorem t1: p → q → p :=
--  fun hp : p => fun hq : q => hp
/-theorem t1 :  p → q → p :=
  fun hp : p =>
    fun hq : q =>
  show p from hp

#print t1
-/

example {x y : ℝ} (h0 :x ≤ y)(h1 : ¬ y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  . assumption
  intro h
  apply h1
  rw [h]

--sin modo táctico
example : A → A := fun ha => ha

#check 2


-- ex 10
example : (A → ¬ B) → (B → ¬ A) :=
  λ hanb =>
    λ hb =>
      λ ha =>
        (hanb ha) hb

example : (A → ¬ B) → (B → ¬ A) := by
  intro h hb ha
  exact (h ha) hb

-- ex 9
example : (∀ x , F x ∧ G x) ↔ (∀ x , F x) ∧ (∀ x , G x) :=
  ⟨λ htfg =>
    ⟨λ w => (htfg w).1, λ w => (htfg w).2⟩,
  λ htf_tg =>
    λ w => ⟨htf_tg.1 w, htf_tg.2 w⟩⟩

example : (∀ x , F x ∧ G x) ↔ (∀ x , F x) ∧ (∀ x , G x) := by
  constructor
  . intro h
    constructor
    . intro w
      exact (h w).1 -- F w ∧ G w
    . intro w
      exact (h  w).2
  . intro ⟨hf , hg⟩ w
    exact ⟨hf w , hg w⟩

-- ex 13
example : (∃ x, F x → G x) → ((∀ x, F x )→ ∃ x, G x) :=
  λ ⟨w,hfg⟩ =>
    λ htf => ⟨w,hfg (htf w)⟩

example : (∃ x, F x → G x) → ((∀ x, F x )→ ∃ x, G x) :=
  λ ⟨w,hfg⟩ =>
    λ htf => Exists.intro w (hfg (htf w))

example : (∃ x, F x → G x) → ((∀ x, F x )→ ∃ x, G x) := by
  intro ⟨w, h⟩ h'
  -- h' w dem F w
  -- h h' w dem de G w
  exact ⟨w, h (h' w)⟩


--ex 1
example : (¬ A ∨ B) → (A → B) :=
  λ hnab =>
    λ ha =>
      Or.elim hnab
        (λ hna =>
          False.elim (hna ha))
        (λ hb =>
          hb)

example : (¬ A ∨ B) → (A → B) := by
  intro h ha
  rcases h with r | s
  . contradiction
  . exact s

--ex 2
example : (∃ x, F x) → (¬ ∀ y , ¬ F y) :=
  λ ⟨w,hf⟩ =>
    λ htnf =>
      (htnf w) hf

example : (∃ x, F x) → (¬ ∀ y , ¬ F y) := by
  intro ⟨w,h⟩ g
  exact (g w) h


--ex 3
example : A ∧ B → A :=
  λ hab =>
    hab.1

example : A ∧ B → A := by
  intro h
  exact h.1

--ex 4
example : A → A ∨ B := by
  intro h
  left
  exact h

-- ex 5
example : (¬ A ∨ ¬ B) → ¬ (A ∧ B) := by
  intro h g
  rcases h with na | nb
  . exact na g.left
  . exact nb g.right

--ex 6
example : ¬ (A ∨ B) ↔ ¬ A ∧ ¬ B := by
  constructor
  . intro h
    constructor
    . intro ha
      apply h
      left
      exact ha
    . intro hb
      apply h
      right
      exact hb
  . intro ⟨h,g⟩ j
    rcases j with ja | jb
    . exact h ja
    . exact g jb


--ex 7
example : ((A ∨ C) ∧ (B ∨ C)) ↔ ((A ∧ B) ∨ C) := by
  constructor
  . intro ⟨h, g⟩
    rcases h with ha | hc
    . rcases g with gb | gc
      . left
        exact ⟨ha , gb⟩
      . right
        exact gc
    . right
      exact hc
  . intro h
    constructor
    . rcases h with r | hc
      . left
        exact r.left
      . right
        exact hc
    . rcases h with s | hc
      . left
        exact s.right
      . right
        exact hc

--ex 7 op
example : ((A ∨ C) ∧ (B ∨ C)) ↔ ((A ∧ B) ∨ C) := by
  constructor
  . intro ⟨hac , hbc⟩
    cases hac
    case inl ha =>
      cases hbc
      case inl hb => exact Or.inl ⟨ha, hb⟩
      case inr hc => exact Or.inr hc
    case inr hc =>
      right
      assumption
  . intro habc
    constructor
    . cases habc
      case inl hab => exact Or.inl hab.1
      case inr hc => exact Or.inr hc
    . cases habc
      case inl hab => exact Or.inl hab.2
      case inr hc => exact Or.inr hc


--ex 8

example : (∃ x, ¬ F x) → (¬ ∀ x, F x) :=
  λ ⟨w,hnf⟩ =>
    λ htf =>
      hnf (htf w)

example : (∃ x, ¬ F x) → (¬ ∀ x, F x) := by
  intro ⟨w,h⟩ g
  exact h (g w)

--ex 11

example : (∃ x, A → F x) → (A → ∃ x, F x) :=
  λ ⟨w,haf⟩ =>
    λ ha =>
      ⟨w,haf ha⟩

example : (∃ x, A → F x) → (A → ∃ x, F x) := by
  intro ⟨w,h⟩ ha
  exact ⟨w,(h ha)⟩

--ex 12

example : (∃ x, F x → B) → (∀ x, F x) → B :=
  λ ⟨w,hfb⟩ =>
    λ htf =>
      hfb (htf w)


example : (∃ x, F x → B) → (∀ x, F x) → B := by
  intro ⟨w, h⟩ u
  exact (h (u w))

-- ejercicios 3.10
--ex 1

example (hnnab : ¬ ¬ (A → B)) : A → ¬ ¬ B :=
  λ ha =>
    λ hnb =>
      hnnab (λ hab => hnb (hab ha))

example (hnnab : ¬ ¬ (A → B)) : A →  ¬ ¬ B := by
  intro ha hnb
  exact hnnab (λ hab => hnb (hab ha))






--ex 2

example (hdnb :(¬ ¬ B) → B) : ¬ ¬ (A → B) → (A → B) :=
  λ hnnab =>
    λ ha =>
      have l1 : B :=
      hdnb (λ hnb => hnnab (λ hab => hnb (hab ha) ))
      l1

example (hdnb :(¬ ¬ B) → B) : ¬ ¬ (A → B) → (A → B) := by
  intro hnnab ha
  have l1 : B :=
    hdnb (λ hnb => hnnab (λ hab => hnb (hab ha) ))
  exact l1





--ex 3

example : ¬ ¬ ¬ A ↔ ¬ A :=
  ⟨fun hnnna =>
    fun ha =>
      hnnna (fun hna => (hna ha)),
  fun hna =>
    fun hnna => (hnna hna)⟩


example : ¬ ¬ ¬ A ↔ ¬ A :=
  Iff.intro
  (fun hnnna =>
    fun ha =>
      hnnna (fun hna => (hna ha)))
  (fun hna =>
    fun hnna => (hnna hna))


example : ¬ ¬ ¬ A ↔ ¬ A := by
  constructor
  . intro h g
    apply h
    intro j
    exact (j g)
  . intro h g
    apply g
    exact h


variable (p q r : Prop)

example (h : p ∨ q) : q ∨ p := by
  apply Or.elim h
    (fun hp : p =>
      show q ∨ p from Or.intro_right q hp)
    (fun hq : q =>
      show q ∨ p from Or.intro_left p hq)








--theorem t1 : p → q → p := λ hp : p , λ hq : q, hp

--#print t1

--otro
example {p q r : Prop} : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) :=
  Iff.intro
  (fun hpqr => And.intro (fun hp => (hpqr (Or.inl hp))) (fun hq => (hpqr (Or.inr hq))))
  (fun hpr_qr => fun hpq => Or.elim hpq (fun hp => (hpr_qr.1 hp)) (fun hq => (hpr_qr.2 hq)))

example {p q r : Prop} : ((p ∨ q) → r) ↔ ((p → r) ∧ (q → r)) := by
  constructor
  . intro h
    constructor
    . intro hp
      apply h
      left
      exact hp
    . intro hq
      apply h
      right
      exact hq
  . intro ⟨h,g⟩ j
    rcases j with jp | jq
    . exact (h jp)
    . exact (g jq)

--otro
  example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      apply Or.inl
      apply And.intro
      . exact And.left h
      . exact hq
    . intro hr
      apply Or.inr
      apply And.intro
      . exact And.left h
      . exact hr
  . intro h
    apply Or.elim h
    . intro hpq
      apply And.intro
      . exact And.left hpq
      . apply Or.inl
        exact And.right hpq
    . intro hpr
      apply And.intro
      . exact And.left hpr
      . apply Or.inr
        exact And.right hpr

--ex con términos
example : p ∨ q ↔ q ∨ p :=
  ⟨ fun h => Or.elim h Or.inr Or.inl , fun g => Or.elim g Or.inr Or.inl⟩

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h =>
      h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq))
    (fun g =>
      g.elim (fun gq => Or.inr gq) (fun gp => Or.inl gp))

example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro hpq
    cases hpq
    case inl hp => right; assumption
    case inr hq => left; assumption
  . intro hqp
    rcases hqp with r | s
    . right
      assumption
    . left
      exact s

-- ex t
example : p ∧ q ↔ q ∧ p :=
  ⟨fun h => ⟨h.2,h.1⟩ , fun g => ⟨g.2, g.1⟩⟩

example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h => ⟨h.2,h.1⟩ )
    (fun g => ⟨g.2,g.1⟩ )

example : p ∨ q ↔ q ∨ p := by
  constructor
  . intro hpq
    cases hpq
    case inl hp => right; assumption
    case inr hq => left; assumption
  . intro hqp
    rcases hqp with r | s
    . right
      assumption
    . left
      exact s

example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h => And.intro (And.right h) (And.left h))
    (fun g => And.intro (And.right g) (And.left g))

-- ex
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨fun h => ⟨(h.1).1,⟨(h.1).2,h.2⟩⟩, fun g => ⟨⟨g.1,(g.2).1⟩,(g.2).2⟩⟩

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h => ⟨(h.1).1,⟨(h.1).2,h.2⟩⟩)
    (fun g => ⟨⟨g.1,(g.2).1⟩,(g.2).2⟩)

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (fun h => And.intro ((h.1).1) (And.intro ((h.1).2) (h.2)))
    (fun g => And.intro (And.intro (g.1) ((g.2).1)) ((g.2).2))

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  constructor
  . intro h
    exact ⟨(h.1).1,⟨(h.1).2,h.2⟩⟩
  . intro g
    exact ⟨⟨g.1,(g.2).1⟩,(g.2).2⟩

-- ex
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨fun hpq_r => Or.elim hpq_r (fun hpq => Or.elim hpq (fun hp => Or.inl hp) (fun hq => Or.inr (Or.inl hq))) (fun hr => Or.inr (Or.inr hr)),
  fun hp_qr => Or.elim hp_qr (fun hp => Or.inl (Or.inl hp)) (fun hqr => Or.elim hqr (fun hq => Or.inl (Or.inr hq)) (fun hr => Or.inr hr))⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (fun hpq_r =>
      hpq_r.elim (fun hpq =>
        hpq.elim (fun hp => Or.inl hp) (fun hq => Or.inr (Or.inl hq)) )
      (fun hr => Or.inr (Or.inr hr)))
    (fun hp_qr =>
      hp_qr.elim (fun hp => Or.inl (Or.inl hp))
      (fun hqr => hqr.elim (fun hq => Or.inl (Or.inr hq)) (fun hr => Or.inr hr)))

--example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  constructor
  . intro hpq_r
    cases hpq_r
    case inl hpq =>
      cases hpq
      case inl hp =>
        left
        exact hp
      case inr hq =>
        right
        left
        assumption
    case inr hr =>
      exact Or.inr (Or.inr hr)
  . intro hp_qr
    rcases hp_qr with hp | hqr
    . left
      left
      exact hp
    . rcases hqr with hq | hr
      . exact Or.inl (Or.inr hq)
      . right ; assumption

-- dist 1
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨fun hp_qr => Or.elim hp_qr.2 (fun hq => Or.inl ⟨hp_qr.1,hq⟩) (fun hr => Or.inr ⟨hp_qr.1,hr⟩),
  fun hpq_pr => Or.elim hpq_pr (fun hpq => ⟨hpq.1,Or.inl hpq.2⟩) (fun hpr => ⟨hpr.1,Or.inr hpr.2⟩)⟩

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun hp_qr =>
      Or.elim hp_qr.2 (fun hq => Or.inl (And.intro (hp_qr.1) (hq)))
      (fun hr => Or.inr (And.intro (hp_qr.1) (hr))))
    (fun hpq_pr =>
      Or.elim hpq_pr (fun hpq => And.intro (hpq.1) (Or.inl hpq.2))
      (fun hpr => And.intro (hpr.1) (Or.inr hpr.2)))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    Iff.intro
    (fun hp_qr =>
      Or.elim hp_qr.2 (fun hq => Or.inl (⟨hp_qr.1,hq⟩))
      (fun hr => Or.inr (⟨hp_qr.1,hr⟩)))
    (fun hpq_pr =>
      Or.elim hpq_pr (fun hpq => ⟨hpq.1,Or.inl hpq.2⟩)
      (fun hpr => ⟨hpr.1,Or.inr hpr.2⟩))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro h
    cases h.2
    case inl hq =>
      left
      exact ⟨h.1,hq⟩
    case inr hr =>
      exact Or.inr (And.intro (h.1) (hr))
  . intro g
    rcases g with gpq | gpr
    . constructor
      . exact gpq.1
      . exact Or.inl (gpq.2)
    . apply And.intro (gpr.1) (Or.inr gpr.2)

-- dist 2

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨fun hp_qr => Or.elim hp_qr (fun hp => ⟨Or.inl hp,Or.inl hp⟩) (fun hqr => ⟨Or.inr hqr.1,Or.inr hqr.2⟩),
  fun hpq_pr => Or.elim hpq_pr.1 (fun hp => Or.inl hp) (fun hq => Or.elim hpq_pr.2 (fun gp => Or.inl gp) (fun hr => Or.inr ⟨hq,hr⟩))⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (fun hp_qr => Or.elim hp_qr (fun hp => And.intro (Or.inl hp) (Or.inl hp)) (fun hqr => And.intro (Or.inr hqr.1) (Or.inr hqr.2)))
  (fun hpq_pr => Or.elim hpq_pr.1 (fun hp => Or.inl hp) (fun hq => Or.elim hpq_pr.2 (fun gp => Or.inl gp) (fun hr => Or.inr (And.intro (hq) (hr)))))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  constructor
  . intro hp_qr
    rcases hp_qr with hp | hqr
    . constructor
      . left
        exact hp
      . exact Or.inl hp
    . constructor
      . right
        exact hqr.1
      . exact Or.inr hqr.2
  . intro hpq_pr
    cases hpq_pr.1
    case inl hp =>
      left
      exact hp
    case inr hq =>
      cases hpq_pr.2
      case inl gp =>
        exact Or.inl gp
      case inr hr =>
        right
        exact ⟨hq,hr⟩

-- other prop

example : (p → (q → r)) ↔ ((p ∧ q) → r) :=
  ⟨fun hpqr => fun hpq => (hpqr hpq.1) hpq.2 , fun gpqr => fun hp => fun hq => (gpqr ⟨hp,hq⟩)⟩

example : (p → (q → r)) ↔ ((p ∧ q) → r) :=
  Iff.intro
    (fun hpqr => fun hpq => (hpqr hpq.1) hpq.2 )
    (fun gpqr => fun hp => fun hq => (gpqr (And.intro (hp) (hq))))

example : (p → (q → r)) ↔ ((p ∧ q) → r) := by
  constructor
  . intro hpqr gpq
    exact (hpqr gpq.1) gpq.2
  . intro gpqr gp gq
    exact (gpqr (And.intro (gp) (gq)))

--

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨fun hpqr => ⟨fun hp => (hpqr (Or.inl hp)), fun hq => (hpqr (Or.inr hq))⟩,
  fun hpr_qr => fun hpq => Or.elim hpq (fun hp => (hpr_qr.1 hp)) (fun hq => (hpr_qr.2 hq))⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  (fun hpqr => And.intro (fun hp => (hpqr (Or.inl hp))) (fun hq => (hpqr (Or.inr hq))))
  (fun hpr_qr => fun hpq => Or.elim hpq (fun hp => ((And.left hpr_qr) hp)) (fun hq => (hpr_qr.right hq)))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  constructor
  . intro hpqr
    constructor
    . intro hp
      exact (hpqr (Or.inl hp))
    . intro hq
      exact (hpqr (Or.inr hq))
  . intro hpr_qr hpq
    cases hpq
    case inl hp =>
      exact (hpr_qr.1 hp)
    case inr hq =>
      exact (hpr_qr.2 hq)




example : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  ⟨fun hnpq => ⟨fun hp => (hnpq (Or.inl hp)),fun hq => (hnpq (Or.inr hq))⟩,
  fun hnp_nq => fun hpq => Or.elim hpq (fun hp => (hnp_nq.1 hp)) (fun hq => (hnp_nq.2 hq))⟩

example : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q :=
  Iff.intro
  (fun hnpq => And.intro (fun hp => (hnpq (Or.inl hp))) (fun hq => (hnpq (Or.inr hq))))
  (fun hnp_nq => fun hpq => hpq.elim (fun hp => (hnp_nq.1 hp)) (fun hq => (hnp_nq.2 hq)))

example : ¬ (p ∨ q) ↔ ¬ p ∧ ¬ q := by
  constructor
  . intro hnpq
    constructor
    . intro hp
      exact (hnpq (Or.inl hp))
    . intro hq
      exact (hnpq (Or.inr hq))
  . intro hnp_nq hnpq
    rcases hnpq with hp | hq
    . exact (hnp_nq.1 hp)
    . exact (hnp_nq.2 hq)

--

example : ¬ p ∨ ¬ q → ¬ (p ∧ q) :=
  fun hnp_nq => fun hpq => hnp_nq.elim (fun hnp => (hnp hpq.1)) (fun hnq => (hnq hpq.2))

example : ¬ p ∨ ¬ q → ¬ (p ∧ q) := by
  intro hnp_nq hpq
  cases hnp_nq
  case inl hnp =>
    exact (hnp hpq.1)
  case inr hnq =>
    exact (hnq hpq.2)

--

example : ¬ (p ∧ ¬ p) :=
  fun hp_np => absurd hp_np.1 hp_np.2

example : ¬ (p ∧ ¬ p) := by
  intro hp_np
  exact hp_np.2 hp_np.1

--

example : p ∧ ¬ q → ¬ (p → q) :=
  fun hp_nq => fun hpq => False.elim (hp_nq.2 (hpq hp_nq.1))

example : p ∧ ¬ q → ¬ (p → q) := by
  intro hp_nq hpq
  exact hp_nq.2 (hpq hp_nq.1)

--

example : ¬ p → (p → q) :=
  fun hnp => fun hp => False.elim (hnp hp)

example : ¬ p → (p → q) := by
  intro hnp hp
  exfalso
  exact hnp hp

--

example : (¬ p ∨ q) → (p → q) :=
  fun hnp_q => fun hp => Or.elim hnp_q (fun hnp => False.elim (hnp hp)) (fun hq => hq)

example : (¬ p ∨ q) → (p → q) := by
  intro hnp_q hp
  cases hnp_q
  case inl hnp =>
    exfalso
    exact hnp hp
  case inr hq =>
    exact hq

--

example : p ∨ False ↔ p :=
  ⟨fun hpf => Or.elim hpf (fun hp => hp) (fun hf => False.elim (hf)),
  fun hp => Or.inl hp⟩

example : p ∨ False ↔ p :=
  Iff.intro
  (fun hpf => Or.elim hpf (fun hp => hp) (fun hf => False.elim (hf)))
  (fun hp => Or.inl hp)

example : p ∨ False ↔ p := by
  constructor
  . intro hpf
    rcases hpf with hp | hf
    . exact hp
    . exfalso
      exact hf
  . intro hp
    left
    exact hp

--

example : p ∧ False ↔ False :=
  ⟨fun hpf => False.elim (hpf.2), fun hf => False.elim (hf)⟩

example : p ∧ False ↔ False :=
  Iff.intro
  (fun hpf => False.elim (hpf.2))
  (fun hf => False.elim (hf))

example : p ∧ False ↔ False := by
  constructor
  . intro hpf
    exact hpf.2
  . intro hf
    exfalso
    exact hf

--

example : (p → q) → (¬ q → ¬ p) :=
  fun hpq => fun hnq => fun hp => False.elim (hnq (hpq hp))

example : (p → q) → (¬ q → ¬ p) := by
  intro hpq hnq hp
  exact hnq (hpq hp)

--



example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h0 h1 =>
    contrapose! h1
    exact le_antisymm h0 h1



end LJ1



/-

Clásico

-/


section Lclasica

open Classical

variable (p q r : Prop)

#check Classical.em p


theorem dne {p : Prop} (h : ¬¬p) : p :=
  Or.elim (Classical.em p )
    (fun hp : p => hp)
    (fun hnp : ¬p => absurd hnp h)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun hp_qr => Or.elim (Classical.em p)
    (fun hp => Or.elim (hp_qr hp) (fun hq => Or.inl (fun _ => hq)) (fun hr => Or.inr (fun _ => hr)))
    (fun hnp => Or.inl (fun hp => absurd hp hnp))

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hp_qr
  rcases Classical.em p with hp | hnp
  . cases (hp_qr hp)
    case inl hq =>
      exact (Or.inl (fun _ => hq))
    case inr hr =>
      exact (Or.inr (fun _ => hr))
  . left
    intro hp
    exfalso
    exact hnp hp

--

example : ¬ (p ∧ q) → ¬ p ∨ ¬ q :=
  fun hnpq => Or.elim (Classical.em p)
    (fun hp => Or.elim (Classical.em q) (fun hq => False.elim (hnpq ⟨hp,hq⟩)) (fun hnq => Or.inr hnq))
    (fun hnp => Or.inl hnp)

example : ¬ (p ∧ q) → ¬ p ∨ ¬ q :=
  fun hnpq => Or.elim (Classical.em p)
    (fun hp => Or.elim (Classical.em q) (fun hq => False.elim (hnpq (And.intro (hp) (hq)))) (fun hnq => Or.inr hnq))
    (fun hnp => Or.inl hnp)

example : ¬ (p ∧ q) → ¬ p ∨ ¬ q := by
  intro hnpq
  cases Classical.em p
  case inl hp =>
    cases Classical.em q
    case inl hq =>
      left
      exfalso
      exact (hnpq ⟨hp,hq⟩)
    case inr hnq =>
      right
      exact hnq
  case inr hnp =>
    left
    exact hnp

--

example : ¬ (p → q) → p ∧ ¬ q :=
  fun hnpq =>
    Or.elim (Classical.em p)
      (fun hp => ⟨hp,fun hq => (hnpq (fun _ => hq))⟩)
      (fun hnp => False.elim (hnpq (fun hp => absurd hp hnp)))


example : ¬ (p → q) → p ∧ ¬ q :=
  fun hnpq =>
    Or.elim (Classical.em p)
      (fun hp => And.intro (hp) (fun hq => (hnpq (fun _ => hq))))
      (fun hnp => False.elim (hnpq (fun hp => absurd hp hnp)))



example : ¬ (p → q) → p ∧ ¬ q := by
  intro hnpq
  rcases Classical.em p with hp | hnp
  . constructor
    . exact hp
    . intro hq
      exact (hnpq (fun _ => hq))
  . constructor
    . exfalso
      apply hnpq
      intro hp
      exact absurd hp hnp
    . intro hq
      apply hnpq
      intro _
      exact hq



--
example : (p → q) → (¬ p ∨ q) :=
   fun hpq => Or.elim (Classical.em p) (fun hp => Or.inr (hpq hp)) (fun hnp => Or.inl hnp)

example : (p → q) → (¬ p ∨ q) := by
  intro hpq
  cases Classical.em p
  case inl hp =>
    exact Or.inr (hpq hp)
  case inr hnp =>
    exact Or.inl hnp

--

example : (¬ q → ¬ p) → (p → q) :=
  fun hnq_np =>
    fun hp =>
      Or.elim (Classical.em q) (fun hq => hq) (fun hnq => False.elim ((hnq_np hnq) hp))

example : (¬ q → ¬ p) → (p → q) := by
  intro hnq_np hp
  cases Classical.em q
  case inl hq =>
    exact hq
  case inr hnq =>
    exfalso
    exact ((hnq_np hnq) hp)

--

example : p ∨ ¬ p :=
  Or.elim (Classical.em p) (fun hp => Or.inl hp) (fun hnp => Or.inr hnp)

example : p ∨ ¬ p := by
  rcases Classical.em p with hp | hnp
  . exact Or.inl hp
  . exact Or.inr hnp

--

example : (((p → q) → p) → p) :=
  fun hpqp =>
    Or.elim (Classical.em p)
      (fun hp => hp)
      (fun hnp => Or.elim (Classical.em q)
        (fun hq => False.elim (hnp (hpqp (fun _ => hq))))
        (fun _ => (hpqp (fun hp => absurd hp hnp))) )

example : (((p → q) → p) → p) := by
  intro hpqp
  cases Classical.em p
  case inl hp =>
    exact hp
  case inr hnp =>
    apply hpqp
    intro hp
    exact absurd hp hnp


end Lclasica



/-
Cuantificadores
-/

section Quantifiers

variable (α : Prop) (p q : α → Prop)

--
example : (∀ x ,p x ∧ q x) ↔ (∀ x,p x) ∧ (∀ x,q x) :=
  ⟨fun htpq => ⟨fun ha => (htpq ha).1,fun ha => (htpq ha).2⟩,
  fun htp_tq => fun ha => ⟨htp_tq.1 ha,htp_tq.2 ha⟩⟩

example : (∀ x ,p x ∧ q x) ↔ (∀ x,p x) ∧ (∀ x,q x) :=
  Iff.intro
  (fun htpq => And.intro (fun ha => (htpq ha).1) (fun ha => (htpq ha).2))
  (fun htp_tq => fun ha => And.intro (htp_tq.1 ha) (htp_tq.2 ha))

example : (∀ x ,p x ∧ q x) ↔ (∀ x,p x) ∧ (∀ x,q x) := by
  constructor
  . intro htpq
    constructor
    . intro ha
      exact (htpq ha).1
    . intro ha
      exact (htpq ha).2
  . intro htp_tq ha
    exact ⟨htp_tq.1 ha,htp_tq.2 ha⟩

--

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun htpq =>
    fun htp =>
      fun ha => ((htpq ha) (htp ha))

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro htpq htp ha
  exact ((htpq ha) (htp ha))

--

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun htp_tq =>
    Or.elim htp_tq
      (fun htp => fun ha => Or.inl (htp ha))
      (fun htq => fun ha => Or.inr (htq ha))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro htp_tq ha
  rcases htp_tq with htp | htq
  . left
    exact (htp ha)
  . right
    exact (htq ha)

----- ejemplo
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    (fun w =>
     fun hw : p w ∧ q w =>
     show ∃ x, q x ∧ p x from ⟨w, hw.right, hw.left⟩)




end Quantifiers

/-
Clásico con cuantificadores
-/

section ClassicalQ

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

theorem neg_y  {r t : Prop} : ¬ (r ∨ t) ↔ ¬ r ∧ ¬ t :=
  ⟨λ hnab =>
    (Or.elim (Classical.em r)
      (λ ha => False.elim (hnab (Or.inl ha)) )
      (λ hna => (Or.elim (Classical.em t))
        (λ hb => False.elim (hnab (Or.inr hb)))
        (λ hnb => ⟨hna,hnb⟩))),
  λ hna_nb =>
    λ hab =>
      Or.elim hab
        (λ ha => False.elim (hna_nb.1 ha) )
        (λ hb => False.elim (hna_nb.2 hb))⟩


theorem contrap {s t : Prop} : (s → t) ↔ (¬ t → ¬ s) :=
  ⟨λ hst =>
    λ hnt =>
      λ hs =>
        False.elim (hnt (hst hs)),
  λ hntns =>
    λ hs =>
      Or.elim (Classical.em t)
        (λ ht => ht)
        (λ hnt => False.elim ((hntns hnt) hs))⟩

theorem cont {s t : Prop} : ¬ (s → t) ↔ (s ∧ ¬ t) :=
  ⟨λ hnst =>
    Or.elim (Classical.em s)
      (λ hs => ⟨hs,λ ht => hnst (λ _ => ht)⟩)
      (λ hns => False.elim (hnst (λ hs => absurd hs hns )) ),
  λ ⟨hs,hnt⟩ =>
    λ hst =>
      False.elim (hnt (hst hs))⟩

example : ¬ (∃ x, p x) ↔ ∀ x, ¬ p x := by
  constructor
  . intro hnep w hp
    exact hnep ⟨w,hp⟩
  . intro htnp ⟨x,hpx⟩
    exact (htnp x) hpx

theorem ce_neg {α : Type} {s : α → Prop} : (¬ (∃ x, s x)) ↔ ∀ x, ¬ s x :=
  ⟨λ henp =>
    λ x =>
      λ hp =>
        (henp ⟨x,hp⟩),
  λ htnp =>
    λ ⟨x,hpx⟩ =>
      (htnp x) hpx⟩

example {s : Prop} : ¬ ¬ s ↔ s := by
  constructor
  . intro hnns
    rcases Classical.em s with hs | hns
    . exact hs
    . exfalso
      exact hnns hns
  . intro hs hns
    exact hns hs

theorem dob_neg {s : Prop} : ¬ ¬ s ↔ s :=
  ⟨λ hnns =>
    Or.elim (Classical.em s)
      (λ hs => hs)
      (λ hns => False.elim (hnns hns)),
  λ hs =>
    λ hns =>
      hns hs⟩

#check dob_neg

example :  ¬ (∃ x, ¬ p x) ↔ ∀ x, p x := by
  constructor
  . intro h
    have h1 : ∀ x, p x:=
      λ x =>
        have h2 : p x :=
          dob_neg.mp (((ce_neg.mp) h) x)
        h2
    exact h1
  . intro g ⟨x,npx⟩
    exact npx (g x)

theorem neg_f {s : α → Prop} : ¬ (∀ x, s x) → ∃ x, ¬ s x :=
  byContradiction
    (λ h1 =>
      have h2 : ∀ x, s x :=
        λ x =>
          have h3 : s x :=
            dob_neg.mp ((ce_neg.mp (cont.mp h1).2) x)
          h3
      (cont.mp h1).1 h2)

theorem cf_neg {α : Type} {s : α → Prop} : ¬ (∀ x, s x) ↔ ∃ x, ¬ s x :=
  ⟨byContradiction
    (λ h1 =>
      have h2 : ∀ x, s x :=
        λ x =>
          have h3 : s x :=
            dob_neg.mp ((ce_neg.mp (cont.mp h1).2) x)
          h3
      (cont.mp h1).1 h2),
  λ ⟨x,hnsx⟩ =>
    λ hts =>
      hnsx (hts x)⟩

example : ¬ (∀ x, p x) ↔ ∃ x, ¬ p x := by
  constructor
  . contrapose!
    intro htp w
    exact htp w
  . intro ⟨x,npx⟩ htp
    exact npx (htp x)


--
example : (∃ _ : α, r) → r :=
  fun ⟨_,hr⟩ => hr

example : (∃ _ : α, r) → r :=
  fun her => Exists.elim her (fun _ => fun hr => hr)

example : (∃ _ : α, r) → r := by
  intro ⟨_,hr⟩
  exact hr

--
example (a : α) : r → (∃ _ : α, r) :=
  fun hr => Exists.intro a hr

example (a : α) : r → (∃ _ : α, r) := by
  intro hr
  exact ⟨a,hr⟩

--
example : (∃ x, p x) ∧ r → (∃ x, p x ∧ r) :=
  λ ⟨⟨x,px⟩,hr⟩ =>
    ⟨x,⟨px,hr⟩⟩


example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (fun ⟨x,pxr⟩ => And.intro (Exists.intro (x) (pxr.1)) (pxr.2))
  (fun ⟨⟨hx,hpx⟩,hr⟩ => Exists.intro hx (And.intro (hpx) (hr)))

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  ⟨fun ⟨w,hp,hr⟩ => ⟨⟨w,hp⟩,hr⟩,
  fun ⟨⟨hx,hpx⟩,hpr⟩ => ⟨hx,hpx,hpr⟩⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=  by
  constructor
  . intro ⟨w,hp,hr⟩
    constructor
    . exact ⟨w,hp⟩
    . exact hr
  . intro ⟨⟨w,hp⟩,hr⟩
    exact ⟨w,hp,hr⟩

--

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (fun ⟨x,pqx⟩ => Or.elim pqx
    (fun hep => Or.inl (Exists.intro x hep)) (fun heq => Or.inr (Exists.intro x heq)))
  (fun hep_eq => Or.elim hep_eq
    (fun ⟨x,px⟩ => Exists.intro x (Or.inl px)) (fun ⟨x,qx⟩ => Exists.intro x (Or.inr qx)))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  ⟨fun ⟨w,hpq⟩ => Or.elim hpq (fun hp => Or.inl ⟨w,hp⟩) (fun hq => Or.inr ⟨w,hq⟩),
  fun hep_eq => Or.elim hep_eq (fun ⟨w,hp⟩ => ⟨w,Or.inl hp⟩) (fun ⟨w,hq⟩ => ⟨w,Or.inr hq⟩)⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  . intro ⟨w,hpq⟩
    rcases hpq with hp | hq
    . left
      exact ⟨w,hp⟩
    . right
      exact ⟨w,hq⟩
  . intro hep_eq
    cases hep_eq
    case inl hep =>
      obtain ⟨x,px⟩:=hep
      exact ⟨x,Or.inl px⟩
    case inr heq =>
      obtain ⟨x,qx⟩:= heq
      exact ⟨x,Or.inr qx⟩

--

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  ⟨fun htp => fun ⟨x,npx⟩ => (npx (htp x)),
  fun hnenp =>
    fun w =>
      Or.elim (Classical.em (p w))
        (fun hp => hp)
        (fun hnp => False.elim (hnenp ⟨w,hnp⟩))⟩


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
  (fun htp => fun ⟨x,npx⟩ => (npx (htp x)))
  (fun hnenp =>
    fun w =>
      Or.elim (Classical.em (p w))
        (fun hp => hp)
        (fun hnp => False.elim (hnenp (Exists.intro (w) (hnp)))))


example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := by
  constructor
  . intro htp ⟨w,hnp⟩
    exact (hnp (htp w))
  -- Cl
  . intro hnenp w
    rcases Classical.em (p w) with hp | hnp
    . exact hp
    . exfalso
      exact (hnenp ⟨w,hnp⟩)


--
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  ⟨λ ⟨hx,hpx⟩ =>
    λ htnp =>
      (htnp hx) hpx,
  λ hntnp =>
    have ⟨x,hnnp⟩ : ∃ x, ¬ ¬ p x :=
      (cf_neg.mp hntnp)
    have ⟨x,hp⟩ : ∃ x, p x :=
      ⟨x,dob_neg.mp hnnp⟩
    ⟨x,hp⟩⟩

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (fun ⟨hx,hpx⟩ =>
    fun htnp =>
      (htnp hx) hpx)
  (fun hntnp =>
    have ⟨x,hnnp⟩ : ∃ x, ¬ ¬ p x :=
      (cf_neg.mp hntnp)
    have ⟨x,hp⟩ : ∃ x, p x :=
      ⟨x,dob_neg.mp hnnp⟩
    Exists.intro (x) (hp))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := by
  constructor
  . intro ⟨hx,hpx⟩ htnp
    exact ((htnp hx) hpx)
  . intro hntnp
    have ⟨x,hnnp⟩ : ∃ x, ¬ ¬ p x :=
      (cf_neg.mp hntnp)
    have ⟨x,hp⟩ : ∃ x, p x :=
      ⟨x,dob_neg.mp hnnp⟩
    exact ⟨x,hp⟩


--

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  ⟨fun hnep =>
    fun w =>
      fun hp =>
        (hnep ⟨w,hp⟩),
  fun htnp =>
    fun ⟨x,hp⟩ => ((htnp x) hp)⟩

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := by
  constructor
  . intro hnep w hp
    exact (hnep ⟨w,hp⟩)
  . intro htnp ⟨x,hp⟩
    exact (htnp x) hp


--

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  ⟨λ hntp =>
    cf_neg.mp hntp,
  λ ⟨w,hnp⟩ =>
    λ htp =>
      hnp (htp w)⟩

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := by
  constructor
  . contrapose!
    . intro htp w
      exact (htp w)
  . intro ⟨w,hnp⟩ htp
    exact hnp (htp w)


--

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  ⟨λ htpr =>
    λ ⟨w,hp⟩ =>
      (htpr w) hp,
  λ hep_r =>
    λ w =>
      λ hp =>
        hep_r ⟨w,hp⟩⟩

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := by
  constructor
  . intro htpr ⟨w,hp⟩
    exact (htpr w) hp
  . intro hepr w hp
    exact hepr ⟨w,hp⟩


--

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  ⟨λ ⟨w,hpr⟩ =>
    λ htp =>
      hpr (htp w),
  byContradiction (λ h1 =>
    have l1 : ∀ x, p x :=
      λ w =>
        (cont.mp ((ce_neg.mp (cont.mp h1).2) w)).1
    have l2 : ¬ r :=
      (cont.mp ((ce_neg.mp (cont.mp h1).2) a)).2
    l2 ((cont.mp h1).1 l1))⟩


example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := by
  constructor
  . intro ⟨w,hpr⟩ htp
    exact hpr (htp w)
  . intro htp_r
    by_contra! htpnr
    have lem : ∀ x, p x := by
      intro w
      exact (htpnr w).1
    exact (htpnr a).2 (htp_r lem)




--

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  ⟨λ ⟨w,hrp⟩ =>
    λ hr =>
      ⟨w,(hrp hr)⟩,
  byContradiction (λ h1 =>
    have ⟨l1,l2⟩ : (r → ∃ x, p x) ∧ ∀ x, r ∧ ¬ p x:=
      have l3 : ∀ x, r ∧ ¬ p x:=
        λ w =>
          cont.mp ((ce_neg.mp (cont.mp h1).2) w)
      ⟨(cont.mp h1).1,l3⟩
    have ⟨x,px⟩ : ∃ x, p x:=
      l1 (l2 a).1
    (l2 x).2 px )⟩

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := by
  constructor
  . intro ⟨w,hrp⟩ hr
    exact ⟨w,(hrp hr)⟩
  . intro hr_ep
    by_contra h'
    push_neg at h'
    obtain ⟨w,pw⟩:= (hr_ep (h' a).1)
    exact (h' w).2 pw



--

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  ⟨λ htpq =>
    ⟨λ w => (htpq w).1,λ w => (htpq w).2⟩,
  λ htp_tq =>
    λ w => ⟨htp_tq.1 w,htp_tq.2 w⟩⟩

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro htpq
    constructor
    . intro w
      exact (htpq w).1
    . intro w
      exact (htpq w).2
  . intro htp_tq w
    exact ⟨htp_tq.1 w,htp_tq.2 w⟩

---

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  λ htpq =>
    λ htp =>
      λ w =>
        (htpq w) (htp w)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := by
  intro htpq htp w
  exact (htpq w) (htp w)

--

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  λ htp_tq =>
    λ w =>
      Or.elim htp_tq
        (λ htp => Or.inl (htp w))
        (λ htq => Or.inr (htq w))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro htptq w
  cases htptq
  case inl htp =>
    exact Or.inl (htp w)
  case inr htq =>
    exact Or.inr (htq w)

--

example : α → ((∀ _ : α, r) ↔ r) :=
  λ a =>
    ⟨λ htr =>
      htr a,
    λ hr =>
      λ _ =>
        hr⟩

example : α → ((∀ _ : α, r) ↔ r) := by
  intro a
  constructor
  . intro htr
    exact htr a
  . intro hr _
    exact hr

--


open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  ⟨byContradiction (λ h1 =>
    have ⟨h1,⟨x,hnp⟩,h3⟩ : (∀ x, p x ∨ r) ∧ (∃ x, ¬ p x) ∧ ¬ r :=
      ⟨(cont.mp h1).1,⟨cf_neg.mp (neg_y.mp (cont.mp h1).2).1,(neg_y.mp (cont.mp h1).2).2⟩ ⟩
    Or.elim (h1 x)
      (λ hpx => hnp hpx)
      (λ hr => h3 hr)),
  λ htp_r =>
    λ w =>
      Or.elim htp_r
        (λ htp =>
          Or.inl (htp w))
        (λ hr =>
          Or.inr hr)⟩


example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := by
  constructor
  . contrapose!
    intro ⟨⟨w,hnp⟩,hnr⟩
    exact ⟨w,hnp,hnr⟩
  . intro htpr w
    rcases htpr with htp | hr
    . exact Or.inl (htp w)
    . exact Or.inr hr


--

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  ⟨λ htrp =>
    λ hr =>
      λ w =>
        (htrp w) hr,
  λ hrtp =>
    λ w =>
      λ hr =>
        (hrtp hr) w⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := by
  constructor
  . intro htrp hr w
    exact (htrp w) hr
  . intro hrtp w hr
    exact (hrtp hr) w

--





variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := by
--  exact (h barber).1
  have nos : ¬ shaves barber barber := by
    intro g
    exact ((h barber).1 g) g
  have s : shaves barber barber := by
    exact (h barber).2 nos
  exact nos s









/-
example : (∃ x : α, r) → r := sorry
example (a : α) : r → (∃ x : α, r) := sorry
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry



example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry


variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
-/

end ClassicalQ
