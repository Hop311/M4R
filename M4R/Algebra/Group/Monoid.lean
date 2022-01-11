import M4R.Algebra.Group.Basic

namespace M4R

  class Monoid (α : Type _) extends Zero α, Add α where
    add_zero  : ∀ a : α, a + 0 = a
    zero_add  : ∀ a : α, 0 + a = a
    add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)

  class CommMonoid (α : Type _) extends Monoid α where
    add_comm  : ∀ a b : α, a + b = b + a

  structure SubMonoid (α : Type _) [Monoid α] where
    subset     : Set α
    has_zero   : 0 ∈ subset
    add_closed : ∀ a ∈ subset, ∀ b ∈ subset,  a + b ∈ subset
  instance SubMonoidMem [Monoid α] : Mem α (SubMonoid α) where mem := fun x S => x ∈ S.subset
  
  namespace Monoid

    protected instance ofGroup (α : Type _) [Group α] : Monoid α where
      add_zero := Group.add_zero
      zero_add := Group.zero_add
      add_assoc := Group.add_assoc

    protected def toGroup [Monoid α] [Neg α] (h : ∀ a : α, a + (-a) = 0) : Group α where
      add_zero := add_zero
      add_assoc := add_assoc
      add_neg := h

  end Monoid

  namespace CommMonoid

    protected instance ofAbelianGroup (α : Type _) [AbelianGroup α] : CommMonoid α where
      toMonoid := Monoid.ofGroup α
      add_comm := AbelianGroup.add_comm

    protected def toAbelianGroup [CommMonoid α] [Neg α] (h : ∀ a : α, a + (-a) = 0) : AbelianGroup α where
      toGroup := Monoid.toGroup h
      add_comm := CommMonoid.add_comm

    theorem add_right_comm [CommMonoid α] (a b c : α) : a + b + c = a + c + b := by
      rw [Monoid.add_assoc, add_comm b, ←Monoid.add_assoc]
    theorem add_left_comm [CommMonoid α] (a b c : α) : a + (b + c) = b + (a + c) := by
      rw [←Monoid.add_assoc, add_comm a, Monoid.add_assoc]
  
  end CommMonoid

  namespace SubMonoid
    open Monoid
    open CommMonoid

    def Self (α : Type _) [Monoid α] : SubMonoid α where
      subset   := Set.Universal
      has_zero := trivial
      add_closed := by intros; trivial

    protected instance toMonoid [Monoid α] (s : SubMonoid α) : Monoid ↑s.subset where
      zero := ⟨0, s.has_zero⟩
      add := fun ⟨x, hx⟩ ⟨y, hy⟩ => ⟨x + y, s.add_closed x hx y hy⟩
      add_zero := fun ⟨a, _⟩ => Set.elementExt (add_zero a)
      zero_add := fun ⟨a, _⟩ => Set.elementExt (zero_add a)
      add_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (add_assoc a b c)

    protected instance toCommMonoid [CommMonoid α] (s : SubMonoid α) : CommMonoid ↑s.subset where
      toMonoid := s.toMonoid
      add_comm := fun ⟨a, _⟩ ⟨b, _⟩ => Set.elementExt (add_comm a b)
  
  end SubMonoid

  instance TrivialMonoid [Singleton α] : CommMonoid α where
    add_zero := by intro a; simp only [HAdd.hAdd, Add.add]; exact (Singleton.single a).symm
    zero_add := by intro a; simp only [HAdd.hAdd, Add.add]; exact (Singleton.single a).symm
    add_assoc := by intro a b c; simp only [HAdd.hAdd, Add.add]
    add_comm := by intro a b; simp only [HAdd.hAdd, Add.add]

  instance NatMonoid : CommMonoid Nat where
    add_zero := Nat.add_zero
    zero_add := Nat.zero_add
    add_assoc := Nat.add_assoc
    add_comm := Nat.add_comm

end M4R
