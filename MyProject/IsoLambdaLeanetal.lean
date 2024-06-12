/-
λ h =>  es  intro h
(a t)   es  apply a h


Brouwer-Heyting-Kolmogorov

· Una prueba de a ∧ b es:
En BHK                          En Lean
un par ⟨ha, hb⟩                 constructor
                                . exact ha
                                . exact hb

· Una demostración de a ∨ b es:
⟨i, x⟩, donde o bien
i=1 y x=ha  o                   left; exact ha
i=2 y x=hb                      right; exact hb

· Una demostración de a → b es:
λ ha => hb                      intro ha
fun ha ↦ hb                     exact hb

· En ambos casos ¬a está definido como a → False
· En Lean una demostración de True es trivial

Sean α : Type y a : α → Prop (una fórmula con una variable libre de tipo α)

· Una demostración de ∃ x, a x es:
⟨w, hw⟩, donde                  use w
w : α y hw : (a w)              exact hw

hw : (a w) significa que hw es una demostración de la proposición (a w)

· Una dem de ∀ x, a x es:
λ (w : α) ↦ hw                  intro w
fun (w : α) => hw               exact hw

-/
