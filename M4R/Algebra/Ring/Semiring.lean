import M4R.Algebra.Ring.Defs

namespace M4R

  namespace NCSemiring

    protected instance Product (α₁ : Type _) (α₂ : Type _) [NCSemiring α₁] [NCSemiring α₂] : NCSemiring (α₁ × α₂) where
      one               := (1, 1)
      mul               := fun (a₁, a₂) (b₁, b₂) => (a₁ * b₁, a₂ * b₂)
      mul_one           := fun (a₁, a₂) => by simp [HMul.hMul, Mul.mul]; exact ⟨mul_one a₁, mul_one a₂⟩
      one_mul           := fun (a₁, a₂) => by simp [HMul.hMul, Mul.mul]; exact ⟨one_mul a₁, one_mul a₂⟩
      mul_assoc         := fun (a₁, a₂) (b₁, b₂) (c₁, c₂) => by
        simp [HMul.hMul, Mul.mul];exact ⟨mul_assoc a₁ b₁ c₁, mul_assoc a₂ b₂ c₂⟩
      mul_distrib_left  := fun (a₁, a₂) (b₁, b₂) (c₁, c₂) => by
        simp [HMul.hMul, Mul.mul, HAdd.hAdd, Add.add]; exact ⟨mul_distrib_left a₁ b₁ c₁, mul_distrib_left a₂ b₂ c₂⟩
      mul_distrib_right := fun (a₁, a₂) (b₁, b₂) (c₁, c₂) => by
        simp [HMul.hMul, Mul.mul, HAdd.hAdd, Add.add]; exact ⟨mul_distrib_right a₁ b₁ c₁, mul_distrib_right a₂ b₂ c₂⟩
      mul_zero          := fun (a₁, a₂) => by
        simp [HMul.hMul, Mul.mul, Monoid.product_zero]; exact ⟨mul_zero a₁, mul_zero a₂⟩
      zero_mul          := fun (a₁, a₂) => by
        simp [HMul.hMul, Mul.mul, Monoid.product_zero]; exact ⟨zero_mul a₁, zero_mul a₂⟩

    protected class constructor_ncsr (α : Type _) extends CommMonoid.constructor_cm α, One α, Mul α where
      mul_one           : ∀ a : α, a * 1 = a
      one_mul           : ∀ a : α, 1 * a = a
      mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
      mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
      mul_distrib_right : ∀ a b c : α, (a + b) * c = a * c + b * c
      mul_zero          : ∀ a : α, a * 0 = 0
      zero_mul          : ∀ a : α, 0 * a = 0

    protected instance construct {α : Type _} (c : NCSemiring.constructor_ncsr α) : NCSemiring α where
      toCommMonoid := CommMonoid.construct c.toconstructor_cm
      mul_one           := c.mul_one
      one_mul           := c.one_mul
      mul_assoc         := c.mul_assoc
      mul_distrib_left  := c.mul_distrib_left
      mul_distrib_right := c.mul_distrib_right
      mul_zero          := c.mul_zero
      zero_mul          := c.zero_mul

    protected def to_constructor (α : Type _) [NCSemiring α] : NCSemiring.constructor_ncsr α where
      toconstructor_cm := CommMonoid.to_constructor α
      mul_one           := NCSemiring.mul_one
      one_mul           := NCSemiring.one_mul
      mul_assoc         := NCSemiring.mul_assoc
      mul_distrib_left  := NCSemiring.mul_distrib_left
      mul_distrib_right := NCSemiring.mul_distrib_right
      mul_zero          := NCSemiring.mul_zero
      zero_mul          := NCSemiring.zero_mul

  end NCSemiring

  namespace Semiring

    protected instance Product (α₁ : Type _) (α₂ : Type _) [Semiring α₁] [Semiring α₂] : Semiring (α₁ × α₂) where
      mul_comm := fun (a₁, a₂) (b₁, b₂) => by simp [HMul.hMul, Mul.mul]; exact ⟨mul_comm a₁ b₁, mul_comm a₂ b₂⟩

    protected class constructor_sr (α : Type _) extends CommMonoid.constructor_cm α, One α, Mul α where
      mul_one           : ∀ a : α, a * 1 = a
      mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
      mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
      mul_zero          : ∀ a : α, a * 0 = 0
      mul_comm          : ∀ a b : α, a * b = b * a

    protected instance construct {α : Type _} (c : Semiring.constructor_sr α) : Semiring α where
      toCommMonoid := CommMonoid.construct c.toconstructor_cm
      mul_one           := c.mul_one
      one_mul           := fun a => by rw [c.mul_comm]; exact c.mul_one a
      mul_assoc         := c.mul_assoc
      mul_distrib_left  := c.mul_distrib_left
      mul_distrib_right := fun a b _ => by rw [c.mul_comm, c.mul_comm a, c.mul_comm b]; exact c.mul_distrib_left _ _ _
      mul_zero          := c.mul_zero
      zero_mul          := fun a => by rw [c.mul_comm]; exact c.mul_zero a
      mul_comm          := c.mul_comm

    protected def to_constructor (α : Type _) [Semiring α] : Semiring.constructor_sr α where
      toconstructor_cm := CommMonoid.to_constructor α
      mul_one           := NCSemiring.mul_one
      mul_assoc         := NCSemiring.mul_assoc
      mul_distrib_left  := NCSemiring.mul_distrib_left
      mul_zero          := NCSemiring.mul_zero
      mul_comm          := Semiring.mul_comm

  end Semiring

  instance NatSemiring : Semiring Nat := Semiring.construct
    {
      add_zero          := Nat.add_zero
      add_assoc         := Nat.add_assoc
      add_comm          := Nat.add_comm
      mul_one           := Nat.mul_one
      mul_assoc         := Nat.mul_assoc
      mul_distrib_left  := Nat.left_distrib
      mul_zero          := Nat.mul_zero
      mul_comm          := Nat.mul_comm
    }

end M4R