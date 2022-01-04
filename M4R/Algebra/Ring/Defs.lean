import M4R.Algebra.Group

namespace M4R

  class NCRing (α : Type _) extends AbelianGroup α, One α, Mul α where
    mul_one           : ∀ a : α, a * 1 = a
    one_mul           : ∀ a : α, 1 * a = a
    mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
    mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
    mul_distrib_right : ∀ a b c : α, (a + b) * c = a * c + b * c

  class NonTrivialNCRing (α : Type _) extends NCRing α where
    one_neq_zero : (1 : α) ≠ 0

  class Ring (α : Type _) extends NCRing α where
    mul_comm         : ∀ a b : α, a * b = b * a

  class NonTrivialRing (α : Type _) extends Ring α, NonTrivialNCRing α

  structure NCSubRing (α : Type _) [NCRing α] extends SubGroup α where
      has_one    : 1 ∈ subset
      mul_closed : ∀ a ∈ subset, ∀ b ∈ subset, a * b ∈ subset
  instance NCSubRingMem [NCRing α] : Mem α (NCSubRing α) where mem := fun x S => x ∈ S.subset
  
  structure SubRing (α : Type _) [Ring α] extends NCSubRing α
  instance SubRingMem [Ring α] : Mem α (SubRing α) where mem := fun x S => x ∈ S.subset

  namespace Ring
    protected def ofNat [NCRing α] (n : Nat) : α :=
      match n with
      | Nat.zero   => 0
      | Nat.succ m => match m with
        | Nat.zero => 1
        | _        => (Ring.ofNat m) + 1
    @[defaultInstance high]
    instance RingOfNat [NCRing α] (n : Nat) : OfNat α n where ofNat := Ring.ofNat n
    
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
  
  class NCField (α : Type _) extends NonTrivialNCRing α where
    inv     : ∀ {a : α}, a ≠ 0 → α
    mul_inv : ∀ {a : α}, (h : a ≠ 0) → a * (inv h) = 1
    inv_mul : ∀ {a : α}, (h : a ≠ 0) → (inv h) * a = 1

  class Field (α : Type _) extends NCField α, Ring α

  class NCIntegralDomain (α : Type _) extends NonTrivialNCRing α where
    integral : ∀ {a b : α}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  
  class IntegralDomain (α : Type _) extends NCIntegralDomain α, Ring α

end M4R
