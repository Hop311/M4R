import M4R.Algebra.Group

namespace M4R

  class NCSemiring (α : Type _) extends CommMonoid α, One α, Mul α where
    mul_one           : ∀ a : α, a * 1 = a
    one_mul           : ∀ a : α, 1 * a = a
    mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
    mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
    mul_distrib_right : ∀ a b c : α, (a + b) * c = a * c + b * c
    mul_zero          : ∀ a : α, a * 0 = 0
    zero_mul          : ∀ a : α, 0 * a = 0

  class Semiring (α : Type _) extends NCSemiring α where
    mul_comm  : ∀ a b : α, a * b = b * a

  class NCRing (α : Type _) extends NCSemiring α, Group α

  class Ring (α : Type _) extends NCRing α, Semiring α

  class NonTrivialNCSemiring (α : Type _) extends NCSemiring α, NonTrivial α

  class NonTrivialSemiring (α : Type _) extends Semiring α, NonTrivialNCSemiring α

  class NonTrivialNCRing (α : Type _) extends NCRing α, NonTrivialNCSemiring α

  class NonTrivialRing (α : Type _) extends Ring α, NonTrivialNCRing α

  structure SubSemiring (α : Type _) [NCSemiring α] extends SubMonoid α where
    has_one    : 1 ∈ subset
    mul_closed : ∀ a ∈ subset, ∀ b ∈ subset,  a * b ∈ subset

  structure SubRing (α : Type _) [NCRing α] extends SubSemiring α, SubGroup α

  namespace NCSemiring
    protected def ofNat [NCSemiring α] (n : Nat) : α :=
      match n with
      | Nat.zero   => 0
      | Nat.succ m => match m with
        | Nat.zero => 1
        | _        => (NCSemiring.ofNat m) + 1
    @[defaultInstance high]
    instance RingOfNatCoe [NCSemiring α] : Coe Nat α where coe := NCSemiring.ofNat

    protected def pow_nat [NCSemiring α] (a : α) (n : Nat) : α :=
      match n with
      | Nat.zero   => 1
      | Nat.succ m => match m with
        | Nat.zero => a
        | _        => (NCSemiring.pow_nat a m) * a
    instance RingPowNat [NCSemiring α] : Pow α Nat where pow := NCSemiring.pow_nat

    theorem all_trivial [NCSemiring α] (h10 : (1 : α) = 0) (x : α) : x = 0 := by
      rw [←mul_one x, h10, mul_zero]

  end NCSemiring

  namespace Semiring

    def divides [Semiring α] (a b : α) : Prop := ∃ c, a * c = b
    instance [Semiring α] : Divides α where
      divides := divides

    def isUnit [Semiring α] (a : α) : Prop := a ÷ 1

    def associates [Semiring α] (a b : α) : Prop := ∃ c, isUnit c ∧ a * c = b
    instance SemiringAssociateEq [Semiring α] : RingEq α where
      ringeq := associates

    def nonZeroNonUnit [Semiring α] (a : α) : Prop := a ≠ 0 ∧ ¬isUnit a
    def irreducible [Semiring α] (a : α) : Prop :=
      nonZeroNonUnit a ∧ ∀ x y, x * y = a → (isUnit x ∨ isUnit y)

  end Semiring

  protected instance NCRing.toAbelianGroup [NCRing α] : AbelianGroup α where
    add_comm := CommMonoid.add_comm

end M4R
