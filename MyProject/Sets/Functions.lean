import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := sorry

example : f '' (s ∪ t) = f '' s ∪ f '' t := sorry

example : s ⊆ f ⁻¹' (f '' s) := sorry

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := sorry

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := sorry

example : f '' (f ⁻¹' u) ⊆ u := sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := sorry

#print Injective
example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := sorry


variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; constructor
  . intro h
    simp at h
    rcases h with ⟨x, ⟨i, xai⟩, fxy⟩
    simp
    use i, x, xai, fxy
  . intro h
    simp at h
    rcases h with ⟨i, x, xai, fxy⟩
    simp
    use x; constructor
    . use i
    . assumption

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := sorry

end
