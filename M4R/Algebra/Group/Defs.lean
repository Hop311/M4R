import M4R.Function
import M4R.Numbers

namespace M4R

  class Group (α : Type _) extends Zero α, Add α, Neg α where
      add_zero  : ∀ a : α, a + 0 = a
      add_assoc : ∀ a b c : α, (a + b) + c = a + (b + c)
      add_neg   : ∀ a : α, a + (-a) = 0

  class AbelianGroup (α : Type _) extends Group α where
      add_comm (a b : α) : a + b = b + a

  structure SubGroup (α : Type _) [Group α] where
      subset     : Set α
      has_zero   : 0 ∈ subset
      add_closed : ∀ a ∈ subset, ∀ b ∈ subset,  a + b ∈ subset
      neg_closed : ∀ a ∈ subset, -a ∈ subset
  instance SubGroupMem [Group α] : Mem α (SubGroup α) where mem := fun x S => x ∈ S.subset
  
  namespace Group

    protected def sub [Group α] (a b : α) : α := a + (-b)
    instance GroupSub [Group α] : Sub α where sub := Group.sub

  end Group

  protected instance AbelianGroup.Trivial (α : Type _) [Singleton α] : AbelianGroup α where
    zero := Inhabited.default
    add := fun _ _ => Inhabited.default
    neg := fun _ => Inhabited.default
    add_zero := by intro a; rw [Singleton.single a]; rfl
    add_assoc := by intros; rfl
    add_neg := by intros; rfl
    add_comm := by intros; rfl

  protected instance Group.Trivial [Singleton α] : Group α := (AbelianGroup.Trivial α).toGroup

  instance IntAbelianGroup : AbelianGroup Int where
    add_zero := Int.add_zero
    add_neg := Int.add_neg
    add_assoc := Int.add_assoc
    add_comm := Int.add_comm

end M4R