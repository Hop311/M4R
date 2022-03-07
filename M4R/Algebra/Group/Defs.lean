import M4R.Set

namespace M4R

  class Monoid (α : Type _) extends Zero α, Add α where
    add_zero  : ∀ a : α, a + 0 = a
    zero_add  : ∀ a : α, 0 + a = a
    add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)

  class CommMonoid (α : Type _) extends Monoid α where
    add_comm  : ∀ a b : α, a + b = b + a

  class Group (α : Type _) extends Monoid α, Neg α where
    add_neg   : ∀ a : α, a + (-a) = 0

  protected def Group.sub [Group α] (a b : α) : α := a + (-b)
  instance Group.GroupSub [Group α] : Sub α where sub := Group.sub

  class AbelianGroup (α : Type _) extends Group α, CommMonoid α

  structure SubMonoid (α : Type _) [Monoid α] where
    subset     : Set α
    has_zero   : 0 ∈ subset
    add_closed : ∀ a ∈ subset, ∀ b ∈ subset,  a + b ∈ subset
  instance SubMonoidMem [Monoid α] : Mem α (SubMonoid α) where mem := fun x S => x ∈ S.subset

  structure SubGroup (α : Type _) [Group α] extends SubMonoid α where
      neg_closed : ∀ a ∈ subset, -a ∈ subset
  instance SubGroupMem [Group α] : Mem α (SubGroup α) where mem := fun x S => x ∈ S.subset

  protected instance Monoid.Trivial [Singleton α] : Monoid α where
    zero      := Inhabited.default
    add       := fun _ _ => Inhabited.default
    add_zero  := fun a => by rw [Singleton.single a]; rfl
    zero_add  := fun a => by rw [Singleton.single a]; rfl
    add_assoc := by intros; rfl

  protected instance CommMonoid.Trivial [Singleton α] : CommMonoid α where
    add_comm := by intros; rfl

  protected instance Group.Trivial [Singleton α] : Group α where
    neg     := fun _ => Inhabited.default
    add_neg := by intros; rfl

  protected instance AbelianGroup.Trivial [Singleton α] : AbelianGroup α where
    add_comm := CommMonoid.Trivial.add_comm

end M4R
