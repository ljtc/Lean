section misdebrayes

variable(a b c : Prop)
variable(α : Type)
variable(F G : α → Prop)
example : ¬ ¬ ¬ a → ¬ a := λ aimpfimpfimpf => (λ ha => aimpfimpfimpf (λ aimpf => aimpf ha))
example : ¬ a → ¬ ¬ ¬ a := λ na => λ aimpfimpf => aimpfimpf na
example : a → a := fun ha => ha
example : (a ∧ b) → a := fun hayb => hayb.1
example : (a ∧ b) → a := fun h => And.left h
example : (a ∧ b ) → b := fun h => h.right
example : (a ∧ b ) → b := fun hayb => hayb.2
example : a → a ∨ b := fun ha => Or.inl ha
example : b→ a ∨ b := fun hb => Or.inr hb
--example : a → a ∨ b := fun ha => left ha
example : p ∧ q → q ∧ p := fun h => ⟨And.right h, And.left h⟩
--example : p ∧ q → q ∧ p := λ h . (And.intro (And.right h) (And.left h) )
example : p ∧ q → q ∧ p := λ h => And.intro (And.right h) (And.left h)
--example : p ∧ q → q ∧ p := λ h => And.intro And.right h And.left h
example : p ∧ q → q ∧ p := λ h => ⟨ h.2, h.1 ⟩
example : p ∨ q → q ∨ p := fun h => (Or.elim h Or.inr Or.inl)
example : p ∨ q → q ∨ p := λ h => h.elim (λ hp => Or.inr hp) (λ hq => Or.inl hq)
--example : p ∧ q → q ∧ p := λ h => (And.intro And.right h And.left h)
example : p ∧ q ↔ q ∧ p := ⟨ fun hi => ⟨ hi.2 , hi.1 ⟩, fun hd => ⟨ hd.2, hd.1 ⟩⟩
example : p ∨ q → q ∨ p := by
  intro h
  apply Or.elim h
  . intro hp
    apply Or.inr hp
  . intro hq
    apply Or.inl hq
example : p ∨ q ↔ q ∨ p := by -- Modo mas tactico , categorico
  constructor
  . intro hpoq
    cases hpoq
    case inl => right ; assumption
    case inr hq => left ; exact hq
  . intro hqop
    rcases hqop with hq | hp
    . right
      exact hq
    . left
      assumption
example : p ∧ q ↔ q ∧ p := --Natural Deduction fuertemente
  Iff.intro
  (fun h => And.intro (And.right h) (And.left h))
  (fun h => And.intro (And.right h) (And.left h))
example : p ∧ q ↔ q ∧ p := by
  constructor
  . exact λ h => ⟨ h.right , h.left ⟩
  . exact λ h => ⟨ h.right, h.left⟩

example : p ∧ q ↔ q ∧ p := by
  constructor
  . exact fun h => And.intro (h.right)  (h.left)
  . exact λ h => ⟨ h.right, h.left⟩

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h =>
      h.elim (fun hp => Or.inr hp) (fun hq => Or.inl hq))
    (fun h =>
      h.elim (fun hq => Or.inr hq) (fun hp => Or.inl hp))

--example : p ∨ q → q ∨ p := fun h => (h.elim (λ hp => Or.inr hp) (λ hq => Or.inl hq))
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := ⟨ fun h => ⟨ (h.1).1 , ⟨ (h.1.2),h.2⟩⟩ , fun h => ⟨ ⟨ h.1, (h.2.1)⟩, (h.2).2⟩⟩
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := ⟨ fun h => Or.elim h (λ hpoq => Or.elim hpoq (Or.inl) (λ hq=>Or.inr (Or.inl hq))) (λ hr => Or.inr (Or.inr hr)) , fun h => h.elim (λ hp => (Or.inl (Or.inl hp))) (λ qor => qor.elim (λ hq => Or.inl (Or.inr hq)) (λ hr=> Or.inr hr))⟩
example : ¬ a ∨ b → (a → b) := by
  intro h
  intro ha
  apply Or.elim h
  . intro na
    exfalso
    exact na ha
  . intro hb
    exact hb
example : (∃ x , F x)→ ¬ ∀ y , ¬ F y := by
  intro ⟨ w , h⟩  k
  exact (k w) h
example : (a ∧ b) → a := by
  intro h
  exact h.1
example : (a ∧ b) → b := by
  intro h
  exact h.2
example : a → a ∨ b := by
  intro h
  exact Or.inl h
example : b → a ∨ b := by
  intro h
  exact Or.inr h
example : a → a := by
  intro h
  exact h
end misdebrayes

section PropositionsandProofs

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := ⟨λ h => ⟨ h.2, h.1⟩ ,λ h => ⟨ h.2, h.1⟩⟩

example : p ∨ q ↔ q ∨ p := ⟨ λ h=> h.elim (Or.inr ) (Or.inl),λ h=> h.elim (Or.inr ) (Or.inl)⟩

example : p ∨ q ↔ q ∨ p := ⟨ λ h => h.elim Or.inr Or.inl, λ h=> h.elim Or.inr Or.inl⟩

-- associativity of ∧ and ∨

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := ⟨λ h=> ⟨ h.1.1, ⟨h.1.2,h.2 ⟩⟩ , λ h=> ⟨⟨ h.1,h.2.1⟩,h.2.2 ⟩⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := ⟨ λ h=> h.elim (λ poq => poq.elim (Or.inl) (λ hq => Or.inr (Or.inl hq))) (λ hr => Or.inr (Or.inr hr)), λ h=> h.elim (λ hp=> Or.inl (Or.inl hp)) (λ qor=> qor.elim (λ hq=> Or.inl (Or.inr hq)) (λ hr=>Or.inr hr))⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := ⟨ λ h => h.2.elim (λ hq=> Or.inl ⟨ h.1, hq⟩) (λ hr=> Or.inr ⟨h.1, hr ⟩) , λ h => h.elim (λ pyq => ⟨pyq.1 , Or.inl pyq.2 ⟩) (λ pyr=> ⟨ pyr.1, Or.inr pyr.2⟩ )⟩

--example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := ⟨ λ h => h.2.elim (Or.inl ⟨ h.1, hq⟩) (Or.inr ⟨h.1, _ ⟩) , λ h => h.elim ⟨ _.1 , Or.inl _.2 ⟩ ⟨_.1, Or.inr _.2 ⟩⟩

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := ⟨ λ h => h.2.elim (λ hq => Or.inl ⟨ h.1, hq⟩) (λ hr => Or.inr ⟨h.1, hr ⟩) , λ h => Or.elim h (λ pyq => ⟨ pyq.1, Or.inl (pyq.2) ⟩) (λ pyr => ⟨pyr.1, Or.inr (pyr.2) ⟩)⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := ⟨ λ h => h.elim (λ hp => ⟨Or.inl hp, Or.inl hp ⟩) (λ qyr => ⟨Or.inr qyr.1, Or.inr qyr.2 ⟩),  λ h => h.1.elim (λ hp => Or.inl hp) (λ hq => h.2.elim (λ hp=> Or.inl hp) (λ hr => Or.inr ⟨hq, hr⟩ ))  ⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := ⟨ λ h => λ pyq => ((h pyq.1) pyq.2), λ hpyq => λ hp => λ hq => (hpyq ⟨hp, hq ⟩)⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := ⟨ λ h => ⟨ λ hp => h (Or.inl hp), λ hq => h (Or.inr hq)⟩,  λ h=> λ poq => poq.elim (h.1) (h.2)⟩

example : ((p ∨ q) → r) → (p → r) ∧ (q → r) := λ h => ⟨ λ hp => h (Or.inl hp), λ hq => h (Or.inr hq)⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := ⟨ λ h => ⟨λ hp => h (Or.inl hp) , λ hq => h (Or.inr hq) ⟩ , λ npynq => λ poq => poq.elim (npynq.1) (npynq.2) ⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) := λ h=> h.elim (λ np=> λ pyq=> np pyq.1 ) (λ nq => λ pyq => nq pyq.2)

example : ¬(p ∧ ¬p) := λ pyn => pyn.2 pyn.1

example : p ∧ ¬q → ¬(p → q) := λ pyn => λ pimplicaq => pyn.2 (pimplicaq pyn.1)

example : ¬p → (p → q) := λ np => λ hp => False.elim (np hp)

example : (¬p ∨ q) → (p → q) := λ npoq => λ hp => npoq.elim (λ np => False.elim (np hp) ) (λ hq =>  hq)

example : p ∨ False ↔ p := ⟨ λ pofalso => Or.elim pofalso (λ hp => hp ) (λ False => False.elim), λ hp => Or.inl hp⟩

example : p ∨ False ↔ p := ⟨ λ h=> h.elim (λ hp => hp) (λ False => False.elim), λ hp => Or.inl hp⟩

example : p ∧ False ↔ False := ⟨ λ pyfalso => pyfalso.2, λ falso => False.elim falso ⟩

example : (p → q) → (¬q → ¬p) := λ pimplicaq => λ nq => λ hp => nq (pimplicaq hp)

theorem hamilton (p q r : Prop): (p → (q → r)) → ((p → q) → (p → r)):= λ pqr => λ pimplicaq => λ hp => (pqr hp) (pimplicaq hp)

theorem hamilton1 (p: Prop) : (p → (p → False)) → ((p → p) → (p → False)) := λ pimpnp => λ _ => λ hp => (pimpnp hp) hp

theorem hamilton2  : (p → ¬ p) → ¬ p := λ pimpnp => λ hp => (pimpnp hp) hp

theorem hamilton3 (p: Prop)  : (p → ¬ p) → ¬ p := λ pimpnp => λ hp => (pimpnp hp) hp

example : (p→ ¬ p) → ¬ p := hamilton3 (p: Prop)

/-Prove ¬(p ↔ ¬p) without using classical logic-/
theorem p_iff_nop (p : Prop) : ¬(p ↔ ¬p) := λ pssinp => (hamilton3 (p:Prop) pssinp.1) (pssinp.2 (hamilton3 (p:Prop) pssinp.1))

theorem p_iff_nop2 (p : Prop) : ¬(p ↔ ¬p) := λ pssinp => ( (λ pimpnp => λ hp => (pimpnp hp) hp) pssinp.1) (pssinp.2 ((λ pimpnp => λ hp => (pimpnp hp) hp) pssinp.1))

end PropositionsandProofs

section logicaclasica
open Classical

theorem exfalso1 : ¬ p → (p → q) := λ nop => λ hp => False.elim (nop hp)

theorem hilbert1 : q → (p→ q) := λ hhq => (λ _ => hhq)

theorem hilbert2 : q → (p→ p ∧ q) := λ hhq => λ hhp => ⟨hhp, hhq⟩

theorem hilbert5 : p ∧ q → p → q := λ pyq => λ _ => pyq.2

--theorem hilbert3 : q → (p→ q) := λ hhq => λ hhp => (⟨hhp, hhq⟩).2

--theorem hilbert4 : q → (p→ q) := λ hhq => λ hhp => ((λ hhp => hhp) => hhq) hhp

--Hacer como dice Eduardo o sea Or.elim (em B ∨ C) () ()

example : (p→ q ∨ r) → ((p → q) ∨ (p → r)) := fun h => Or.elim (Classical.em q) (fun hq => Or.inl (fun _ => hq) ) (λ nq => Or.inr (λ hp => (h hp).elim (λ hq => (False.elim (nq hq))) (λ hr => hr)))

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := λ h => Or.elim (Classical.em (q ∨ r)) (λ qor => qor.elim (λ hq => Or.inl (λ _ => hq)) (λ hr => Or.inr (λ _ => hr))) (λ noqor => Or.inl ( (λ nop => λ hp => False.elim (nop hp)) (((λ aimpb => λ nob => λ ha => nob (aimpb ha)) h) noqor) ))

example : (p→ q ∨ r) → ((p → q) ∨ (p → r)) := λ h => Or.elim (Classical.em p) (λ hp => Or.elim (h hp) (λ hq => Or.inl (λ _ => hq)) (λ hr => Or.inr ( λ _ => hr))) (λ nop => Or.inl ((λ np => λ hp => False.elim (np hp)) nop))

example : ¬(p ∧ q) → ¬p ∨ ¬q := λ h => Or.elim (Classical.em p) (λ hp => Or.elim (Classical.em q) (λ hq => Or.inr (λ hq => (h ⟨hp, hq⟩))) (λ nq => Or.inr nq )) (λ np => Or.inl np)

example : ¬(p → q) → p ∧ ¬q :=λ h=> Or.elim (Classical.em p) (λ hp => Or.elim (Classical.em q) (λ hq => False.elim (h ((λ hhq => λ hhp => hhq) hq))) (λ nq => ⟨hp, nq⟩)) (λ np => False.elim (h ((λ nnp=> λ hhp => False.elim (nnp hhp)) np)))

example : (p → q) → (¬p ∨ q) := λ h => Or.elim (Classical.em p) (λ hp => Or.inr (h hp)) (λ np => Or.inl np)

example : (¬q → ¬p) → (p → q) := λ h=> λ hp => Or.elim (Classical.em q) (λ hpp => hpp) (λ nq => False.elim ((h nq) hp) )

example : (¬ q→ ¬ p) → (p →   q) := λ h=> Or.elim (Classical.em q) (λ hq=> λ hp=> hq ) (λ nq => λ hp => False.elim ((h nq) hp ))

example : p ∨ ¬p := Or.elim (Classical.em p) (λ hp => Or.inl hp) (λ np=> Or.inr np)
/-
Me parece que esta propiedad no es un tautología.
No debería ser demostrable.
Tomar p verdadero y q falso
-/
example : (((p → q) → p) → p) := λ h=> Or.elim (Classical.em p) (λ hp => hp ) (λ np => h ((λ notp => λ hp => ((False.elim (notp hp)) : q)) np))

end logicaclasica

/-Section 4 Quantifiers and Equality-/
section ex41
variable (α : Type) (p q : α → Prop)
variable (a b : Prop)
variable (x:α)

/-
Ahora una section dedicada a los clasicos de Takeuti
-/

example: a ∨ b ↔ ¬ (¬ a ∧ ¬ b) := ⟨ λ h=> h.elim (λ hp=> λ npynq=> npynq.1 hp) (λ hp=> λ npynq=> npynq.2 hp), λ nnpynq=> Or.elim (em a) (λ ha=> Or.inl ha) (λ na=>Or.elim (em b) (λ hb=> Or.inr hb) (λ nb=> False.elim (nnpynq ⟨na, nb⟩)))⟩

example : a→ b ↔ ¬ a ∨ b := ⟨ λ ab=> Or.elim (em a) (λ ha=> Or.inr (ab ha)) (λ na=> Or.inl na), λ noaob=> Or.elim noaob (λ na=> λ ha => False.elim (na ha)) (λ hb=> λ _ => hb) ⟩

example : (∃ x, p x ) ↔ ¬ (∀ y , ¬ p y) := ⟨ λ ⟨ t, hp⟩ => λ paratodo=> (paratodo t) hp, λ paratodoan => Or.elim (em (∃ x , p x)) (λ h=> h) (λ exan=> )⟩

--example : (¬ )

/-

aqui termina la section de clasicos de Takeuti
-/



example : (∀ x, p x ∧ q x) → (∀ x, p x) ∧ (∀ x, q x) := λ h=> ⟨λ (x:α) => (h (x:α)).1, λ (x:α) => (h (x:α)).2⟩

example : (∀ x, p x) ∧ (∀ x, q x) → (∀ x, p x ∧ q x) := λ h=> λ (x:α) => ⟨ h.1 (x:α), h.2 (x:α) ⟩

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := ⟨ λ h=> ⟨λ (x:α) => (h (x:α)).1, λ (x:α) => (h (x:α)).2⟩, λ h=> λ (x:α) => ⟨ h.1 (x:α), h.2 (x:α) ⟩ ⟩

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := λ h => λ anyxpx => λ (x:α) => (h (x:α)) (anyxpx (x:α))

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := λ h=> h.elim (λ anyxpx=> λ (x:α) => Or.inl (anyxpx (x:α))) (λ anyxqx => λ (x:α) => Or.inr (anyxqx (x:α)))
end ex41



section classic41
open Classical

variable (α : Type) (p q : α → Prop)
variable (r b c : Prop)




example : (∃ x : α, r) → r := λ ⟨ _, h⟩ => h

example : (∃ _ : α, r) → r := λ ⟨ _, h⟩ => h


example (a : α) : r → (∃ x : α, r) := λ hr => ⟨(a:α), hr⟩

example : (∃ x, p x ∧ r)→ (∃ x, p x) ∧ r := λ ⟨t, h ⟩=>⟨⟨t,h.1⟩,h.2⟩

example : (∃ x, p x) ∧ r → (∃ x, p x ∧ r) := λ ⟨ ⟨ t, h⟩ , hr⟩=> ⟨t,⟨h,hr⟩⟩

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := ⟨ λ ⟨ t, pxyr⟩ => ⟨⟨ t, pxyr.1⟩,pxyr.2⟩,λ ⟨ ⟨t, hp⟩,hr⟩=>⟨ t, ⟨ hp, hr⟩⟩⟩

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := ⟨ λ ⟨ t, poq⟩=> Or.elim poq (λ hp=>Or.inl (⟨t,hp⟩)) (λ hq=> Or.inr ⟨t, hq⟩), λ epoeq => Or.elim epoeq (λ ⟨t, hp⟩=> ⟨t, Or.inl hp⟩) (λ ⟨ t, hq⟩=> ⟨t, Or.inr hq⟩)⟩

example : (∀ x , p x) → ¬ (∃ x , ¬ p x) := λ anyxp=>λ ⟨t, np⟩=> np (anyxp t)

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := ⟨ λ anyxp=>λ ⟨t, np⟩=> np (anyxp t), λ h=> λ (hx:α) => Or.elim (Classical.em (p hx)) (λ hp=> hp) (λ np => False.elim (h ⟨ hx, np⟩))⟩

example : (∃ x, p x) → ¬ (∀ x, ¬ p x) :=  λ ⟨ t, hp⟩=> λ anyxnp => (anyxnp t ) hp

example :  ¬ (∀ x, ¬ p x) → (∃ x, p x):= sorry --λ nanyxnp => λ (hx:α) => Or.elim (em (p hx)) (λ hp => ⟨(hx:α), hp⟩) (λ np => False.elim (nanyxnp (λ (hx:α) => np)))

example :  ¬ (∀ x, ¬ p x) → (∃ x, p x):= sorry --λ n=> (λ (hx:α) => Or.elim (em (p (hx:α))) (λ hp=> ⟨(hx:α),hp⟩) (λ np => False.elim (n (λ (hx:α)=> np))))

theorem lema : ¬ (∃ x, ¬ p x) → (∀ x , p x) := λ h=> λ (hx:α) => Or.elim (Classical.em (p hx)) (λ hp=> hp) (λ np => False.elim (h ⟨ hx, np⟩))
--seems we need double negation elimination

theorem douneg : ¬ ¬ b→ b:=λ nnb=> Or.elim (Classical.em b) (λ hb=>hb) (λ nb=> False.elim (nnb nb))

theorem lema2 : ¬ (∃ x, p x) → (∀ x ,¬ p x) := λ h=> λ (hx:α)=> Or.elim (Classical.em (p hx)) (λ hp=>False.elim (h ⟨(hx:α),hp⟩)) (λ nnp=> (λ (hx:α) => nnp))

theorem lema2prima : (¬ ∃ x, p x ) → (∀ x , ¬ p x) := λ h => (λ x => Or.elim (Classical.em (p x)) (λ hp => False.elim (h ⟨ x, hp ⟩)) (λ np => np))

--example :  ¬ (∀ x, ¬ p x) → (∃ x, p x) := λ nx => λ (a:α) => Or.elim (em (p a) ) (λ hp=>hp) (λ np=> False.elim (nx (λ a=>np )))

--or just contrapositive

theorem contrapositive : (¬ b→ ¬ c)→ (c→ b):=λ nbtonc=> λ hc=> Or.elim (Classical.em b) (λ hb=> hb) (λ nb=> False.elim ((nbtonc nb) hc))

--Estos son unos lemas que necesitamos

example : (¬ ∃ x, ¬ p x)→ (∀ x, p x) := (λ h => λ x => Or.elim (em (p x)) (λ hp=> hp) (λ np=> False.elim (h ⟨ x, np⟩ )))

example : (∃ x , ¬ p x) → (∃ x , p x → r) := (λ ⟨ wit, prueba⟩ => ⟨ wit, (λ pruebap => False.elim (prueba pruebap))⟩)


--double negation elimination
example : (¬ ¬ r)→ r:= (λ nnr => Or.elim (em r ) (λ hr => hr) (λ nr => False.elim (nnr nr)))

--contrapositiva
example : (r → B) → (¬ B → ¬ r) := (λ rab=> λ nb=> λ hipr=> nb (rab hipr ))


--y ya aqui juntamos los lemas
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := ⟨ λ ⟨ t, par⟩  => λ anyx =>  par (anyx t)  ,
λ allxr => Or.elim (em (∀ x, p x)) (λ si => ⟨ (a:α) , (λ sr=> λ _ => sr) (allxr si)⟩ )
( λ no =>
 ((λ ⟨wit, pruebadenop⟩ => ⟨wit, λ pruebap => False.elim (pruebadenop pruebap)⟩)
  ((λ nnk => Or.elim (em (∃ x, ¬ p x) ) (λ hk => hk) (λ nk => False.elim (nnk nk))) --es curioso que aqui hay que decirle que proposicion queremos para hacer double negation elimination
   (( (λ rab=> λ nb=> λ hipr=> nb (rab hipr))  --contrapositiva
      (λ h => λ x => Or.elim (em (p x)) (λ hp=> hp) (λ np=> False.elim (h (⟨ x, np⟩)))) --no existe no a para todo
    ) no
   )
 ))
)⟩


example : ¬ (b ∨ c) ↔ ¬ b ∧ ¬ c := ⟨ ⟨λ h => , ⟩, ⟩

example :  ¬ (∀ x, ¬ p x) → (∃ x, p x) := λ nx=> Or.elim (em (∃ x , p x)) (λ h=> h) (λ hn=> False.elim (nx (lema2 hn)))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry

example : (¬ ∀ x, p x) → (∃ x, ¬ p x) := sorry -- λ anyimpf => Or.elim (em (p x)) (λ hp => False.elim (anyimpf (λ (hx:α) => p hx))) ()

example :  (∃ x, ¬ p x) → (¬ ∀ x, p x):= λ ⟨t, hnp⟩ => λ any=> hnp (any t)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

example : (∀ x, p x → r) → (∃ x, p x) → r := λ any => λ ⟨ t, hp⟩ => (any t) hp

example : ((∃ x , p x) → r) → (∀ x , p x → r) := λ e=> λ (hx:α) => λ hp => e (⟨ (hx:α), hp⟩)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r := ⟨ λ any => λ ⟨ t, hp⟩ => (any t) hp, λ e=> λ (hx:α) => λ hp => e (⟨ (hx:α), hp⟩)⟩

example (a : α) : (∃ x, p x → r) → (∀ x, p x) → r := λ ⟨ t, im⟩ => λ any =>  im (any t)

example (a:α): (p x → r) → (¬ r→ ¬ p x) := λ pimpq => λ nq => λ hp => nq (pimpq hp)

example (a:α) : (¬ p x → (p x → r)) := λ pimpf => λ hp => False.elim (pimpf hp)

example (a:α) : ((∀ x, p x)→ r)→ (∃ x, p x → r) := λ h=> Or.elim (em r) (λ hr=>⟨ (a:α),λ hp => hr ⟩) (λ rimpf => )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry

example : (∃ x , p x)→ (∃ x , r→ p x) := λ ⟨t, hp⟩=>⟨t, λ hhr=> hp⟩

example : (∃ x , ¬ p x )→ (∃ x, p x → r):= (λ ⟨ w, nope⟩=> ⟨ w, λ yep => False.elim (nope yep)⟩)

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry
end classic41

section Section42
open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

--example : ¬ (∀ x , p x)→ (∃ x, ¬ p x) := λ nforany => λ (hx:α) => Or.elim (em (p (hx:α))) (λ sip => False.elim (nforany (λ (gx:α) => p (gx:α)))) (λ nop => Exists.intro p (hx:α))

example : α → ((∀ x : α, r) ↔ r) := λ h => ⟨ λ anyxr => anyxr (h), λ hr => λ (hx:α) => hr ⟩

example : (∀ x, p x) ∨ r → (∀ x, p x ∨ r) := λ h=> h.elim (λ foranyxpx=> λ (hx:α) => Or.inl (foranyxpx (hx:α)) ) (λ hr=> λ (hx:α)=> Or.inr hr)

--example : (∀ x, p x ∨ r) → (∀ x, p x ) ∨ r := λ foranyxpxorr=> Or.elim (em (∀ x, p x)) (λ si=> Or.inl si) (λ no => )

example : (∀ x, p x ∨ r) → (∀ x, p x ) ∨ r := λ forever=> Or.elim (Classical.em r) (λ hr=> Or.inr hr) (λ nr => Or.inl (λ (hx:α) => Or.elim (forever (hx:α)) (λ kj => kj) (λ nor => False.elim (nr nor))))

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := ⟨λ forever=> Or.elim (Classical.em r) (λ hr=> Or.inr hr) (λ nr => Or.inl (λ (hx:α) => Or.elim (forever (hx:α)) (λ kj => kj) (λ nor => False.elim (nr nor)))) , λ h=> h.elim (λ foranyxpx=> λ (hx:α) => Or.inl (foranyxpx (hx:α)) ) (λ hr=> λ (hx:α)=> Or.inr hr)⟩

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := ⟨ λ foranyxrimppx => λ hr => λ (hx:α)=> (foranyxrimppx (hx:α)) hr, λ rimpanyxpx=> λ (hx:α) => λ hr => (rimpanyxpx hr ) (hx:α)⟩



section Section43
variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := p_iff_nop (shaves barber barber) (h barber)
end Section43



section Section44
