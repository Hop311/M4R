import M4R.Set.Finite.Perm

namespace M4R

  structure Finset (α : Type _) where
    elements : UnorderedList α
    nodup    : elements.nodup

  class Fintype (α : Type _) where
    (elems    : Finset α)
    (complete : ∀ x : α, x ∈ elems.elements)

  class Infinite (α : Type _) : Prop where
    notfinite : Fintype α → false

  namespace Finset
  
    instance FinsetMem : Mem α (Finset α) where mem := fun x f => x ∈ f.elements

    instance FinsetSizeOf : SizeOf (Finset α) where sizeOf := fun f => f.elements.sizeOf
    
    def length (f : Finset α) : Nat := f.elements.length

    protected def toSet (f : Finset α) : Set α := Set.toSet f

    protected def ext (f₁ f₂ : Finset α) : f₁.elements = f₂.elements → f₁ = f₂ :=
      match f₁, f₂ with
      | ⟨_, _⟩, ⟨_, _⟩ => by rw [Finset.mk.injEq]; exact id

  end Finset

end M4R