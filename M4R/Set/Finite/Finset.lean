import M4R.Set.Finite.Perm

namespace M4R

  structure Finset (α : Type _) where
    elements : UnorderedList α
    nodup    : elements.nodup

  class Fintype (α : Type _) where
    (elems    : Finset α)
    (complete : ∀ x : α, x ∈ elems.elements)

  namespace Finset
  
    instance FinsetMem : Mem α (Finset α) where mem := fun x f => x ∈ f.elements

    instance FinsetSizeOf : SizeOf (Finset α) where sizeOf := fun f => f.elements.sizeOf
    
    def length (f : Finset α) : Nat := f.elements.length

    protected def toSet (f : Finset α) : Set α := Set.toSet f
  end Finset

end M4R