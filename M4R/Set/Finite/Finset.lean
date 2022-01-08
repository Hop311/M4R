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
    instance FinsetCoe : Coe (Finset α) (UnorderedList α) where coe := Finset.elems
  
    instance FinsetMem : Mem α (Finset α) where mem := fun x f => x ∈ f.elems

    instance FinsetSizeOf : SizeOf (Finset α) where sizeOf := fun f => f.elems.sizeOf
    
    def length (f : Finset α) : Nat := f.elems.length

    protected def toSet (f : Finset α) : Set α := Set.toSet f

    protected def ext (f₁ f₂ : Finset α) : f₁.elems = f₂.elems → f₁ = f₂ :=
      match f₁, f₂ with
      | ⟨_, _⟩, ⟨_, _⟩ => by rw [Finset.mk.injEq]; exact id
    
    protected def Empty : Finset α := ⟨UnorderedList.Empty, Pairwise.nil⟩
    protected def Universal [Fintype α] : Finset α := Fintype.elems

    protected def map (f : α → β) (s : Finset α) : UnorderedList β := s.elems.map f
    protected def map_inj {f : α → β} (hf : Function.injective f) (s : Finset α) : Finset β :=
      ⟨s.elems.map f, s.elems.nodup_map hf s.nodup⟩

    protected def fold (f : α → β → α) (hcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂) :
      (init : α) → Finset β → α := fun init s => UnorderedList.fold f hcomm init s.elems

  end Finset
  
  namespace Set

    def to_finset (s : Set α) [ft : Fintype s] : Finset α :=
      ⟨(@Finset.Universal s ft).elems.map Subtype.val, by
        apply UnorderedList.nodup_map; apply Set.elementExt; exact Finset.Universal.nodup;⟩

  end Set

  def finite (s : Set α) : Prop := Nonempty (Fintype s)
  def infinite (s : Set α) : Prop := ¬ finite s

  namespace finite
  
      noncomputable def to_fintype {s : Set α} (h : finite s) : Fintype s :=
        Classical.choice h

      noncomputable def to_finset {s : Set α} (h : finite s) : Finset α :=
        @Set.to_finset _ _ h.to_fintype

  end finite
end M4R