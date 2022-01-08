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

    protected def mul_nat [Group α] (n : Nat) (a : α) : α :=
      match n with
      | Nat.zero   => 0
      | Nat.succ m => (Group.mul_nat m a) + a
    instance GroupHMulNat [Group α] : HMul Nat α α where hMul := Group.mul_nat

    protected def mul_int [Group α] (n : Int) (a : α) : α :=
      match n with
      | Int.ofNat m   => m * a
      | Int.negSucc m => -(Nat.succ m * a)
    instance GroupHMulInt [Group α] : HMul Int α α where hMul := Group.mul_int

/-
  ### Instances
-/
    instance GroupInhabited [Group α] : Inhabited α where default := 0
    instance TrivialGroup [Singleton α] : Group α where
      zero := Inhabited.default
      add := fun _ _ => Inhabited.default
      neg := fun _ => Inhabited.default
      add_zero := by intro a; rw [Singleton.single a]; rfl
      add_assoc := by intro a b c; rw [Singleton.single a, Singleton.single b, Singleton.single c]; rfl
      add_neg := by intro a; rfl

    instance IntAbelianGroup : AbelianGroup Int where
      add_zero := Int.add_zero
      add_neg := Int.add_neg
      add_assoc := Int.add_assoc
      add_comm := Int.add_comm

  end Group
end M4R