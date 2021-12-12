import M4R.Set.Finite.Perm

namespace M4R

  structure Finset (α : Type _) where
    elems : UnorderedList α
    nodup : elems.nodup

  class Fintype (α : Type _) where
    (elems    : Finset α)
    (complete : ∀ x : α, x ∈ elems.elems)

  class Infinite (α : Type _) : Prop where
    notfinite : Fintype α → false

  namespace Finset
  
    instance FinsetMem : Mem α (Finset α) where mem := fun x f => x ∈ f.elems

    instance FinsetSizeOf : SizeOf (Finset α) where sizeOf := fun f => f.elems.sizeOf
    
    def length (f : Finset α) : Nat := f.elems.length

    protected def toSet (f : Finset α) : Set α := Set.toSet f

    protected def ext (f₁ f₂ : Finset α) : f₁.elems = f₂.elems → f₁ = f₂ :=
      match f₁, f₂ with
      | ⟨_, _⟩, ⟨_, _⟩ => by rw [Finset.mk.injEq]; exact id
    
    protected def Empty : Finset α := ⟨UnorderedList.Empty α, Pairwise.nil⟩
    protected def Universal [Fintype α] : Finset α := Fintype.elems

  end Finset

end M4R