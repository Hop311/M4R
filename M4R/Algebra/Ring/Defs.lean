import M4R.Algebra.Group

namespace M4R

  class Ring (α : Type _) extends AbelianGroup α, One α, Mul α where
      mul_one          : ∀ a : α, a * 1 = a
      mul_assoc        : ∀ a b c : α, (a * b) * c = a * (b * c)
      mul_distrib_left : ∀ a b c : α, a * (b + c) = a * b + a * c
      mul_comm         : ∀ a b : α, a * b = b * a

  namespace Ring
    protected def ofNat [r : Ring α] (n : Nat) : α :=
      match n with
      | Nat.zero   => 0
      | Nat.succ m => match m with
        | Nat.zero => 1
        | _        => (Ring.ofNat m) + 1
    @[defaultInstance high]
    instance RingOfNat [Ring α] (n : Nat) : OfNat α n where ofNat := Ring.ofNat n
    
    def divides [Ring α] (a b : α) : Prop := ∃ c, a * c = b
    def isUnit [Ring α] (a : α) : Prop := divides a 1
    def associates [Ring α] (a b : α) : Prop := ∃ c, isUnit c ∧ a * c = b
    def nonZeroNonUnit [Ring α] (a : α) : Prop := a ≠ 0 ∧ ¬isUnit a
    def irreducible [Ring α] (a : α) : Prop :=  nonZeroNonUnit a → ∀ x y, x * y = a → (isUnit x ∨ isUnit y)

  end Ring
end M4R
