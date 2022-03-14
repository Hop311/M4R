import M4R.Algebra.Ring.Semiring

namespace M4R

  namespace NCRing
    open Group NCSemiring

    protected instance Product (α₁ : Type _) (α₂ : Type _) [NCRing α₁] [NCRing α₂] : NCRing (α₁ × α₂) where
      toNeg := (Group.Product α₁ α₂).toNeg
      add_neg := (Group.Product α₁ α₂).add_neg

    protected instance multi_product {ι : Type _} (fι : ι → Type _) [∀ i, NCRing (fι i)] : NCRing (MultiProd fι) where
      toNeg   := (Group.multi_product fι).toNeg
      add_neg := (Group.multi_product fι).add_neg

    theorem neg_mul [NCRing α] (a b : α) : -a * b = -(a * b) := by
      rw [←add_right_cancel _ _ (a * b), neg_add, ←mul_distrib_right, neg_add, zero_mul]
    theorem mul_neg [NCRing α] (a b : α) : a * -b = -(a * b) := by
      rw [←add_right_cancel _ _ (a * b), neg_add, ←mul_distrib_left, neg_add, mul_zero]

    theorem neg_one_mul [NCRing α] (a : α) : -1 * a = -a := by
      rw [neg_mul, one_mul]
    theorem neg_one_mul_add [NCRing α] (a b : α) : -1 * (a + b) = -a + -b := by
      rw [mul_distrib_left, neg_one_mul, neg_one_mul]
    theorem neg_one_mul_add' [NCRing α] (a b : α) : -1 * (a + b) = -b + -a := by
      rw [neg_one_mul, neg_add_distrib]

    protected class constructor_ncr (α : Type _) extends Group.constructor_g α, One α, Mul α where
      mul_one           : ∀ a : α, a * 1 = a
      one_mul           : ∀ a : α, 1 * a = a
      mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
      mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
      mul_distrib_right : ∀ a b c : α, (a + b) * c = a * c + b * c

    protected instance construct {α : Type _} (c : NCRing.constructor_ncr α) : NCRing α where
      toNCSemiring := NCSemiring.construct
        {
          toconstructor_cm  := {
            add_zero  := c.add_zero
            add_assoc := c.add_assoc
            add_comm  := fun a b => (Group.construct c.toconstructor_g).neg_inj (by
              rw [(Group.construct c.toconstructor_g).neg_add_distrib]
              have : ∀ a : α, -a = -1 * a := fun a => by
                rw [←(Group.construct c.toconstructor_g).add_right_cancel _ _ a,
                  (Group.construct c.toconstructor_g).neg_add]
                conv => rhs rhs rw [←c.one_mul a]
                rw [←c.mul_distrib_right, (Group.construct c.toconstructor_g).neg_add,
                  ←(Group.construct c.toconstructor_g).add_right_cancel _ _ (0 * a),
                  ←c.mul_distrib_right, c.add_zero, (Group.construct c.toconstructor_g).zero_add]
              rw [this (b + a), c.mul_distrib_left, ←this, ←this])
          }
          mul_one           := c.mul_one
          one_mul           := c.one_mul
          mul_assoc         := c.mul_assoc
          mul_distrib_left  := c.mul_distrib_left
          mul_distrib_right := c.mul_distrib_right
          mul_zero          := fun a => by
            rw [←(Group.construct c.toconstructor_g).add_right_cancel _ _ (a * 0),
              ←c.mul_distrib_left]
            conv => rhs rw [(Group.construct c.toconstructor_g).zero_add]
            rw [c.add_zero]
          zero_mul          := fun a => by
            rw [←(Group.construct c.toconstructor_g).add_right_cancel _ _ (0 * a),
              ←c.mul_distrib_right]
            conv => rhs rw [(Group.construct c.toconstructor_g).zero_add]
            rw [c.add_zero]
        }
      toNeg := (Group.construct c.toconstructor_g).toNeg
      add_neg := (Group.construct c.toconstructor_g).add_neg

    protected def to_constructor (α : Type _) [NCRing α] : NCRing.constructor_ncr α where
      toconstructor_g   := Group.to_constructor α
      mul_one           := NCSemiring.mul_one
      one_mul           := NCSemiring.one_mul
      mul_assoc         := NCSemiring.mul_assoc
      mul_distrib_left  := NCSemiring.mul_distrib_left
      mul_distrib_right := NCSemiring.mul_distrib_right

  end NCRing

  namespace Ring
    open NCSemiring

    protected instance Product (α₁ : Type _) (α₂ : Type _) [Ring α₁] [Ring α₂] : Ring (α₁ × α₂) where
      toNCRing := NCRing.Product α₁ α₂
      mul_comm := (Semiring.Product α₁ α₂).mul_comm

    protected instance multi_product {ι : Type _} (fι : ι → Type _) [∀ i, Ring (fι i)] : Ring (MultiProd fι) where
      mul_comm := (Semiring.multi_product fι).mul_comm

    protected class constructor_r (α : Type _) extends AbelianGroup.constructor_ab α, One α, Mul α where
      mul_one           : ∀ a : α, a * 1 = a
      mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
      mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
      mul_comm          : ∀ a b : α, a * b = b * a

    protected instance construct {α : Type _} (c : Ring.constructor_r α) : Ring α where
      toNCRing := NCRing.construct
        {
          mul_one           := c.mul_one
          one_mul           := fun a => by rw [c.mul_comm]; exact c.mul_one a
          mul_assoc         := c.mul_assoc
          mul_distrib_left  := c.mul_distrib_left
          mul_distrib_right := fun a b _ => by rw [c.mul_comm, c.mul_comm a, c.mul_comm b]; exact c.mul_distrib_left _ _ _
        }
      mul_comm := c.mul_comm

    protected def to_constructor (α : Type _) [Ring α] : Ring.constructor_r α where
      toconstructor_ab  := AbelianGroup.to_constructor α
      mul_one           := NCSemiring.mul_one
      mul_assoc         := NCSemiring.mul_assoc
      mul_distrib_left  := NCSemiring.mul_distrib_left
      mul_comm          := Semiring.mul_comm

  end Ring

  instance IntRing : NonTrivialRing Int where
    toRing := Ring.construct
      {
        add_zero          := Int.add_zero
        add_assoc         := Int.add_assoc
        add_neg           := Int.add_neg
        add_comm          := Int.add_comm
        mul_one           := Int.mul_one
        mul_assoc         := Int.mul_assoc
        mul_distrib_left  := Int.mul_distrib_left
        mul_comm          := Int.mul_comm
      }
    toNonTrivial := IntNonTrivial

end M4R
