import M4R.Algebra.Ring.Defs

namespace M4R

  class NCSemiring (α : Type _) extends CommMonoid α, One α, Mul α where
    mul_one           : ∀ a : α, a * 1 = a
    one_mul           : ∀ a : α, 1 * a = a
    mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
    mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
    mul_distrib_right : ∀ a b c : α, (a + b) * c = a * c + b * c

  class Semiring (α : Type _) extends NCSemiring α where
    mul_comm  : ∀ a b : α, a * b = b * a

  structure SubSemiring (α : Type _) [NCSemiring α] extends SubMonoid α where
    has_one    : 1 ∈ subset
    mul_closed : ∀ a ∈ subset, ∀ b ∈ subset,  a * b ∈ subset
  instance SubSemiringMem [NCSemiring α] : Mem α (SubSemiring α) where mem := fun x S => x ∈ S.subset
  
  namespace NCSemiring

    protected instance ofNCRing (α : Type _) [NCRing α] : NCSemiring α where
      toCommMonoid := CommMonoid.ofAbelianGroup α
      mul_one := NCRing.mul_one
      one_mul := NCRing.one_mul
      mul_assoc := NCRing.mul_assoc
      mul_distrib_left := NCRing.mul_distrib_left
      mul_distrib_right := NCRing.mul_distrib_right

    protected def toNCRing [s : NCSemiring α] [Neg α] (h : ∀ a : α, a + (-a) = 0) : NCRing α where
      toAbelianGroup := CommMonoid.toAbelianGroup h
      mul_one := NCSemiring.mul_one
      one_mul := NCSemiring.one_mul
      mul_assoc := NCSemiring.mul_assoc
      mul_distrib_left := NCSemiring.mul_distrib_left
      mul_distrib_right := NCSemiring.mul_distrib_right

  end NCSemiring
  
  namespace Semiring

    protected instance ofRing (α : Type _) [Ring α] : Semiring α where
      toNCSemiring := NCSemiring.ofNCRing α
      mul_comm := Ring.mul_comm

    protected def toRing [s : Semiring α] [Neg α] (h : ∀ a : α, s.add a (-a) = s.zero) : Ring α where
      toNCRing := NCSemiring.toNCRing h
      mul_comm := Semiring.mul_comm

  end Semiring

  namespace SubSemiring
    open NCSemiring
    open Semiring

    def Self (α : Type _) [NCSemiring α] : SubSemiring α where
      toSubMonoid := SubMonoid.Self α
      has_one := trivial
      mul_closed := by intros; trivial

    protected instance toNCSemiring [NCSemiring α] (s : SubSemiring α) : NCSemiring ↑s.subset where
      toCommMonoid := s.toSubMonoid.toCommMonoid
      one := ⟨1, s.has_one⟩
      mul := fun ⟨a, ha⟩ ⟨b, hb⟩ => ⟨a * b, s.mul_closed a ha b hb⟩
      mul_one := fun ⟨a, _⟩ => Set.elementExt (mul_one a)
      one_mul := fun ⟨a, _⟩ => Set.elementExt (one_mul a)
      mul_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_assoc a b c)
      mul_distrib_left := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_distrib_left a b c)
      mul_distrib_right := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_distrib_right a b c)

    protected instance toSemiring [Semiring α] (s : SubSemiring α) : Semiring ↑s.subset where
      toNCSemiring := s.toNCSemiring
      mul_comm := fun ⟨a, _⟩ ⟨b, _⟩ => Set.elementExt (mul_comm a b)
  
  end SubSemiring

  instance NatSemiring : Semiring Nat where
    mul_one := Nat.mul_one
    one_mul := Nat.one_mul
    mul_assoc := Nat.mul_assoc
    mul_distrib_left := Nat.left_distrib
    mul_distrib_right := Nat.right_distrib
    mul_comm := Nat.mul_comm
    
end M4R