import M4R.Set.Finite.UnorderedList

namespace M4R

  structure Finset (α : Type _) where
    elems : UnorderedList α
    nodup : elems.nodup

  class Fintype (α : Type _) where
    (elems    : Finset α)
    (complete : ∀ x : α, x ∈ elems.elems)

  namespace Finset
    instance FinsetCoe : Coe (Finset α) (UnorderedList α) where coe := Finset.elems

    instance FinsetMem : Mem α (Finset α) where mem := fun x f => x ∈ f.elems

    instance FinsetSizeOf : SizeOf (Finset α) where sizeOf := fun f => f.elems.sizeOf

    def length (f : Finset α) : Nat := f.elems.length

    protected def toSet (f : Finset α) : Set α := Set.toSet f
    protected def ext_Set (f : Finset α) : ∀ x, x ∈ f ↔ x ∈ f.toSet := fun x => ⟨id, id⟩

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
    
    noncomputable def union (s₁ s₂ : Finset α) : Finset α :=
      ⟨s₁.elems.ndunion s₂.elems, UnorderedList.nodup_ndunion s₁.elems s₂.nodup⟩

    noncomputable instance FinsetUnion : Union (Finset α) where union := union

    @[simp] theorem mem_union {a : α} {s₁ s₂ : Finset α} : a ∈ s₁ ∪ s₂ ↔ a ∈ s₁ ∨ a ∈ s₂ :=
      UnorderedList.mem_ndunion
  
    noncomputable def filter (p : α → Prop) (s : Finset α) : Finset α := ⟨UnorderedList.filter p s.elems, 
      UnorderedList.nodup_filter p s.2⟩

    @[simp] theorem filter_val (p : α → Prop) (s : Finset α) : (s.filter p).elems = s.elems.filter p := rfl

    @[simp] theorem mem_filter {s : Finset α} {a : α} : a ∈ s.filter p ↔ a ∈ s ∧ p a := UnorderedList.mem_filter

  end Finset

  namespace Set

    def to_finset (s : Set α) [Fintype s] : Finset α :=
      ⟨(@Finset.Universal s).elems.map Subtype.val, by
        apply UnorderedList.nodup_map; apply Set.elementExt; exact Finset.Universal.nodup;⟩

    @[simp] theorem mem_to_finset {s : Set α} [Fintype s] {a : α} : a ∈ s.to_finset ↔ a ∈ s :=
      ⟨fun h => by let ⟨⟨x, hx⟩, _, h'⟩ := UnorderedList.map.mem_map.mp h; rw [←h']; exact hx,
      fun h => UnorderedList.map.mem_map.mpr ⟨⟨a, h⟩, Fintype.complete _, rfl⟩⟩
      
    @[simp] theorem mem_to_finset_val {s : Set α} [Fintype s] {a : α} : a ∈ s.to_finset.elems ↔ a ∈ s :=
      mem_to_finset

  end Set

  namespace Fintype

    protected instance Empty : Fintype (∅ : Set α) where
      elems := ∅
      complete := fun ⟨x, hx⟩ => by contradiction

    protected def subtype {p : α → Prop} (s : Finset α) (H : ∀ x : α, x ∈ s ↔ p x) : Fintype {x // p x} :=
      ⟨⟨UnorderedList.pmap Subtype.mk s.elems fun x => (H x).mp,
        UnorderedList.nodup_pmap (fun a _ b _ => congrArg Subtype.val) s.nodup⟩,
      fun ⟨x, px⟩ => UnorderedList.mem_pmap.mpr ⟨x, (H x).mpr px, rfl⟩⟩

    protected def of_finset {p : Set α} (s : Finset α) (H : ∀ x, x ∈ s ↔ x ∈ p) : Fintype p :=
      Fintype.subtype s H
    
    protected noncomputable instance union (s t : Set α) [Fintype s] [Fintype t] : Fintype (s ∪ t : Set α) :=
      Fintype.of_finset (s.to_finset ∪ t.to_finset) (fun x =>
        ⟨fun h => by
          have := UnorderedList.mem_ndunion.mp h
          simp only [Set.mem_to_finset_val] at this
          exact this,
        fun h => 
          Finset.mem_union.mpr (Or.elim h
            (fun h' => Or.inl (Set.mem_to_finset.mpr h'))
            (fun h' => Or.inr (Set.mem_to_finset.mpr h')))⟩)
  
    protected noncomputable instance sep (s : Set α) (p : α → Prop) [Fintype s] :
      Fintype (Subtype ({a ∈ s | p a} : Set α)) :=
        Fintype.of_finset (s.to_finset.filter p) (fun _ => by
          simp only [Finset.mem_filter, Set.mem_to_finset]; exact Iff.refl _)

    protected noncomputable instance intersection (s t : Set α) [Fintype s] : Fintype (s ∩ t : Set α) :=
      Fintype.sep s t

    protected noncomputable instance subset {s t : Set α} [Fintype t] (h : s ⊆ t) : Fintype s := by
      rw [←Set.intersection.inter_eq_self_of_subset_right h]
      exact Fintype.intersection t s
  
  end Fintype

  inductive finite (s : Set α) : Prop
  | intro : Fintype s → finite s

  def infinite (s : Set α) : Prop := ¬ finite s

  def Finset.to_finite (f : Finset α) : finite (f.toSet) :=
    finite.intro (Fintype.of_finset f f.ext_Set)

  namespace finite

    theorem iff_exists_fintype {s : Set α} : finite s ↔ Nonempty (Fintype s) :=
      ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩      

    noncomputable def to_fintype {s : Set α} (h : finite s) : Fintype s :=
      Classical.choice (iff_exists_fintype.mp h)

    noncomputable def to_finset {s : Set α} (h : finite s) : Finset α :=
      @Set.to_finset _ s h.to_fintype

    theorem subset {s t : Set α} (ht : finite t) (h : s ⊆ t) : finite s := 
      finite.intro (@Fintype.subset _ s t ht.to_fintype h)

    theorem union {s t : Set α} (hs : finite s) (ht : finite t) : finite (s ∪ t) :=
      finite.intro (@Fintype.union _ s t hs.to_fintype ht.to_fintype)
    
    theorem intersection {s : Set α} (hs : finite s) (t : Set α) : finite (s ∩ t) :=
      finite.intro (@Fintype.intersection _ s t hs.to_fintype)

    theorem intersection' (s : Set α) {t : Set α} (ht : finite t) : finite (s ∩ t) := by
      rw [Set.intersection.comm]; exact intersection ht s

  end finite
end M4R