import M4R.Set.Finite.UnorderedList

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

    @[simp] theorem val_inj {s t : Finset α} : s.elems = t.elems ↔ s = t :=
      ⟨match s, t with | ⟨_, _⟩, ⟨_, _⟩ => by rw [Finset.mk.injEq]; exact id, congrArg _⟩

    theorem ext_iff {s₁ s₂ : Finset α} : s₁ = s₂ ↔ ∀ a, a ∈ s₁ ↔ a ∈ s₂ :=
      val_inj.symm.trans (UnorderedList.nodup_ext s₁.nodup s₂.nodup)

    protected theorem ext {s₁ s₂ : Finset α} : (∀ a, a ∈ s₁ ↔ a ∈ s₂) → s₁ = s₂ :=
      ext_iff.mpr

    theorem antisymm {s₁ s₂ : Finset α} (H₁ : s₁ ⊆ s₂) (H₂ : s₂ ⊆ s₁) : s₁ = s₂ :=
      Finset.ext fun a => ⟨@H₁ a, @H₂ a⟩

    protected def Empty : Finset α := ⟨∅, Pairwise.nil⟩
    protected def Universal [Fintype α] : Finset α := Fintype.elems

    instance EmptyFinsetEmptyCollection : EmptyCollection (Finset α) where
      emptyCollection := Finset.Empty

    protected def singleton (a : α) : Finset α := ⟨UnorderedList.singleton a, Pairwise.singleton _ a⟩

    protected def map (f : α → β) (s : Finset α) : UnorderedList β := s.elems.map f
    protected def map_inj {f : α → β} (hf : Function.injective f) (s : Finset α) : Finset β :=
      ⟨s.elems.map f, s.elems.nodup_map hf s.nodup⟩

    def fold (f : α → β → α) (hcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂) :
      (init : α) → Finset β → α := fun init s => UnorderedList.fold f hcomm init s.elems

    namespace fold
      variable (f : α → β → α) (hcomm : ∀ (a : α) (b₁ b₂ : β), f (f a b₂) b₁ = f (f a b₁) b₂)
      
      @[simp] theorem empty (init : α) : Finset.fold f hcomm init ∅ = init := rfl

      @[simp] theorem singleton (init : α) (b : β) : fold f hcomm init (Finset.singleton b) = f init b := rfl

    end fold
  end Finset

  def Fintype.empty : Fintype (∅ : Set α) where
    elems := ∅
    complete := fun ⟨x, hx⟩ => by contradiction

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