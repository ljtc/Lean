/-
λ h =>  es  intro h
(a t)   es  apply a h


Brouwer-Heyting-Kolmogorov

Una prueba de es en BHK y en lean es

a ∧ b es un par ⟨ pa, pb⟩  es  constructor
                               . pa
                               . pb

a ∨ b es un par ⟨ i, x⟩ donde o bien i es uno y
x=pa o
i=2
y x=pb                       en lean: left; pa o right; pb




-/
