import M4R.Function

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
      add_closed : ∀ a b, a ∈ subset → b ∈ subset → a + b ∈ subset
      neg_closed : ∀ a, a ∈ subset → -a ∈ subset

  structure GHomomorphism (α : Type _) (β : Type _) [Group α] [Group β] where
    hom           : α → β
    preserve_zero : hom 0 = 0
    preserve_add  : ∀ a b, hom (a + b) = hom a + hom b
    preserve_neg  : ∀ a, hom (-a) = -hom a

  structure GIsomorphism (α : Type _) (β : Type _) [Group α] [Group β] extends GHomomorphism α β where
    bij : Function.bijective hom

  def GHomomorphism.kernel [Group α] [Group β] (gh : GHomomorphism α β) : Set α := Function.fibre gh.hom 0

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
      | Int.negSucc m => (Nat.succ m) * (-a)
    instance GroupHMulInt [Group α] : HMul Int α α where hMul := Group.mul_int

  end Group
end M4R