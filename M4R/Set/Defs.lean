import M4R.Set.MemStructure

namespace M4R

    def Set (α : Type u) : Type u := α → Prop

    class Singleton (α : Type _) extends Inhabited α where single (a : α) : a = default

  namespace Set

    protected def mem (a : α) (s : Set α) := s a
    instance SetMem : Mem α (Set α) where mem := Set.mem

    instance PredToSet : Coe (α → Prop) (Set α) where coe := id
    instance SetToSubtype {α : Type u} : CoeSort (Set α) (Type u) where coe := Subtype

    def inclusion {s : Set α} : ↑s → α := fun x => x.val

    abbrev toSet (b : β) [Mem α β] : Set α := { x | x ∈ b }

    /- Set relations/operations -/
    protected def union (s₁ s₂ : Set α) : Set α := {x | x ∈ s₁ ∨ x ∈ s₂}
    instance SetUnion : Union (Set α) where union := Set.union

    protected def intersection (s₁ s₂ : Set α) : Set α := {x | x ∈ s₁ ∧ x ∈ s₂}
    instance SetIntersection : Intersection (Set α) where intersection := Set.intersection

    protected def minus (s₁ s₂ : Set α) : Set α := {x | x ∈ s₁ ∧ x ∉ s₂}
    instance SetSetMinus : SetMinus (Set α) where setminus := Set.minus

    protected def complement (s : Set α) : Set α := {x | x ∉ s}
    instance SetComplement : Complement (Set α) where complement := Set.complement

    protected def product (s₁ : Set α) (s₂ : Set β): Set (α × β) := {p | p.fst ∈ s₁ ∧ p.snd ∈ s₂}
    protected def insert (a : α) (s : Set α) : Set α := {x | x = a ∨ x ∈ s}

    protected def equivalent (s₁ s₂ : Set α) : Prop := ∀ a, a ∈ s₁ ↔ a ∈ s₂

    protected def Empty : Set α := fun _ => False
    protected def Universal : Set α := fun _ => True

    instance EmptySetEmptyCollection : EmptyCollection (Set α) where
      emptyCollection := Set.Empty

    def disjoint (s₁ s₂ : Set α) : Prop := s₁ ∩ s₂ = ∅

    class SUnion (α : Type u) where
      sUnion : Set α → α
    prefix:110 "⋃₀" => SUnion.sUnion

    class SIntersection (α : Type u) where
      sIntersection : Set α → α
    prefix:110 "⋂₀" => SIntersection.sIntersection

    def SoSUnion (s : Set (Set α)) : Set α := {x | ∃ ss ∈ s, x ∈ ss}
    instance SetSUnion : SUnion (Set α) where sUnion := SoSUnion
    def SoSIntersection (s : Set (Set α)) : Set α := {x | ∀ ss ∈ s, x ∈ ss}
    instance SetSIntersection : SIntersection (Set α) where sIntersection := SoSIntersection

    def toSetSet (s : Set α) (f : α → Set β) : Set (Set β) := {b | ∃ a ∈ s, f a = b}

  end Set
end M4R