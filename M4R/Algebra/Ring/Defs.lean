import M4R.Algebra.Group

namespace M4R

  class NonCommutativeRing (α : Type _) extends AbelianGroup α, One α, Mul α where
    mul_one           : ∀ a : α, a * 1 = a
    one_mul           : ∀ a : α, 1 * a = a
    mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
    mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
    mul_distrib_right : ∀ a b c : α, (a + b) * c = a * c + b * c

  class NonTrivialNonCommutativeRing (α : Type _) extends NonCommutativeRing α where
    one_neq_zero : (1 : α) ≠ 0

  class Ring (α : Type _) extends NonCommutativeRing α where
    mul_comm         : ∀ a b : α, a * b = b * a

  class NonTrivialRing (α : Type _) extends Ring α, NonTrivialNonCommutativeRing α

  structure SubRing (α : Type _) [NonCommutativeRing α] extends SubGroup α where
      has_one    : 1 ∈ subset
      mul_closed : ∀ a b, a ∈ subset → b ∈ subset → a * b ∈ subset

  namespace Ring
    protected def ofNat [NonCommutativeRing α] (n : Nat) : α :=
      match n with
      | Nat.zero   => 0
      | Nat.succ m => match m with
        | Nat.zero => 1
        | _        => (Ring.ofNat m) + 1
    @[defaultInstance high]
    instance RingOfNat [NonCommutativeRing α] (n : Nat) : OfNat α n where ofNat := Ring.ofNat n
    
    protected def pow_nat [Ring α] (a : α) (n : Nat) : α :=
      match n with
      | Nat.zero   => 1
      | Nat.succ m => match m with
        | Nat.zero => a
        | _        => (Ring.pow_nat a m) * a
    instance RingPowNat [Ring α] : Pow α Nat where pow := Ring.pow_nat

    def divides [Ring α] (a b : α) : Prop := ∃ c, a * c = b
    instance [Ring α] : Divides α where
      divides := divides

    def isUnit [Ring α] (a : α) : Prop := a ÷ 1
    --noncomputable def unitInverse [Ring α] (a : α) (h : isUnit a) : α := Classical.choose h
    
    def associates [Ring α] (a b : α) : Prop := ∃ c, isUnit c ∧ a * c = b
    instance [Ring α] : RingEq α where
      ringeq := associates

    def nonZeroNonUnit [Ring α] (a : α) : Prop := a ≠ 0 ∧ ¬isUnit a
    def irreducible [Ring α] (a : α) : Prop := nonZeroNonUnit a ∧ ∀ x y, x * y = a → (isUnit x ∨ isUnit y)

  end Ring
end M4R
