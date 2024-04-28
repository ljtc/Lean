section LJ1
variable (α : Type)
variable (a b c : Prop)
variable (F : α → Prop)

#check False
#check Or.intro_left

example : ¬a ∨ b → (a → b) := by
  intro h ha
  apply Or.elim h
  . intro hna
    exact (hna ha).elim
  . intro hb
    assumption

example : a ∧ b → a := by
  intro ⟨ha, _⟩
  assumption

example : a → a ∨ b := by
  intro ha
  apply Or.inl ha

example : (¬a ∨ ¬b) → ¬(a ∧ b) := by
  intro h ⟨ha, hb⟩
  apply Or.elim h
  . intro hna
    exact hna ha
  . intro hnb
    have : b ∧ ¬b := ⟨hb, hnb⟩
    exact this.2 this.1

example (h : a → c) (h' : b → c) : a ∨ b → c := by
  intro h
  cases h
  case inr hb =>
    exact h' hb
  case inl ha =>
    exact h ha

end LJ1
