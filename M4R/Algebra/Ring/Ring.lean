import M4R.Algebra.Ring.Semiring

namespace M4R

  namespace NCRing
    open Group
    open NCSemiring

    protected instance Product (α₁ : Type _) (α₂ : Type _) [NCRing α₁] [NCRing α₂] : NCRing (α₁ × α₂) where
      toNeg := (Group.Product α₁ α₂).toNeg
      add_neg := (Group.Product α₁ α₂).add_neg

    theorem neg_mul [NCRing α] (a b : α) : -a * b = -(a * b) := by
      rw [←add_right_cancel _ _ (a * b), neg_add, ←mul_distrib_right, neg_add, zero_mul]
    theorem mul_neg [NCRing α] (a b : α) : a * -b = -(a * b) := by
      rw [←add_right_cancel _ _ (a * b), neg_add, ←mul_distrib_left, neg_add, mul_zero]

    protected class constructor_ncr (α : Type _) extends AbelianGroup.constructor_ab α, One α, Mul α where
      mul_one           : ∀ a : α, a * 1 = a
      one_mul           : ∀ a : α, 1 * a = a
      mul_assoc         : ∀ a b c : α, (a * b) * c = a * (b * c)
      mul_distrib_left  : ∀ a b c : α, a * (b + c) = a * b + a * c
      mul_distrib_right : ∀ a b c : α, (a + b) * c = a * c + b * c

    protected instance construct {α : Type _} (c : NCRing.constructor_ncr α) : NCRing α where
      toNCSemiring := NCSemiring.construct
        {
          mul_one           := c.mul_one
          one_mul           := c.one_mul
          mul_assoc         := c.mul_assoc
          mul_distrib_left  := c.mul_distrib_left
          mul_distrib_right := c.mul_distrib_right
          mul_zero          := fun a => by
            rw [←(AbelianGroup.construct c.toconstructor_ab).add_right_cancel _ _ (a * 0),
              ←c.mul_distrib_left, c.add_zero, (AbelianGroup.construct c.toconstructor_ab).zero_add]
          zero_mul          := fun a => by
            rw [←(AbelianGroup.construct c.toconstructor_ab).add_right_cancel _ _ (0 * a),
              ←c.mul_distrib_right, c.add_zero, (AbelianGroup.construct c.toconstructor_ab).zero_add]
        }
      toNeg := (AbelianGroup.construct c.toconstructor_ab).toNeg
      add_neg := (AbelianGroup.construct c.toconstructor_ab).add_neg

  end NCRing

  namespace Ring
    open NCSemiring

    protected instance Product (α₁ : Type _) (α₂ : Type _) [Ring α₁] [Ring α₂] : Ring (α₁ × α₂) where
      toNCRing := NCRing.Product α₁ α₂
      mul_comm := (Semiring.Product α₁ α₂).mul_comm

    theorem divides_self [Ring α] (a : α) : a ÷ a := ⟨1, mul_one a⟩
    theorem divides_zero [Ring α] (a : α) : a ÷ 0 := ⟨0, mul_zero a⟩
    theorem divides_add [Ring α] {a b c : α} : a ÷ b → a ÷ c → a ÷ (b + c)
    | ⟨x, axb⟩, ⟨y, ayc⟩ => ⟨x + y, by rw [mul_distrib_left, axb, ayc]⟩
    theorem divides_mul [Ring α] {a b : α} (c : α) : a ÷ b → a ÷ (b * c)
    | ⟨x, axb⟩ => ⟨x * c, by rw [←mul_assoc, axb]⟩
    theorem divides_mul' [Ring α] {a c : α} (b : α) : a ÷ c → a ÷ (b * c) := by
      rw [mul_comm]; exact divides_mul b

    theorem isUnit_1 [Ring α] : isUnit (1 : α) := ⟨1, show 1 * 1 = 1 by rw [mul_one]⟩
    theorem notUnit_0 [Ring α] : (0 : α) ≠ (1 : α) → ¬isUnit (0 : α) := by
      intro h₁ ⟨_, h₂⟩; rw [zero_mul] at h₂; exact h₁ h₂
    theorem unit_mul [Ring α] {a b : α} : isUnit a → isUnit b → isUnit (a * b)
    | ⟨x, xs⟩, ⟨y, ys⟩ => by
      apply Exists.intro (y * x); rw [mul_assoc, ←mul_assoc b, ys, one_mul, xs];
    theorem divides_unit [Ring α] {a b : α} : isUnit b → a ÷ b → isUnit a := by
      intro ub ab;
      let ⟨binv, bbinv⟩ := Classical.indefiniteDescription _ ub;
      let ⟨c, ac⟩ := Classical.indefiniteDescription _ ab;
      exact ⟨c * binv, by rw [←mul_assoc, ac, bbinv];⟩
    theorem unit_divides [Ring α] : ∀ a b : α, isUnit a → a ÷ b := by
      intro a b ⟨c, ac⟩; exact ⟨c * b, by rw [←mul_assoc, ac, one_mul];⟩

    def unit_set (α : Type _) [Ring α] : Set α := {x | isUnit x}

    noncomputable def unit_inv [Ring α] {a : α} (h : isUnit a) : α :=
      Classical.choose h
    theorem mul_unit_inv [Ring α] {a : α} (h : isUnit a) : a * unit_inv h = 1 :=
      Classical.choose_spec h
    theorem unit_inv_mul [Ring α] {a : α} (h : isUnit a) : unit_inv h * a = 1 := by
      rw [mul_comm]; exact mul_unit_inv h

    noncomputable instance UnitGroup [Ring α] : Group ↑(unit_set α) := Group.construct
    {  
      zero := ⟨1, ⟨1, by rw [mul_one]⟩⟩
      add := fun a b => ⟨a.val * b.val, unit_mul a.property b.property⟩
      neg := fun ⟨x, xs⟩ => ⟨unit_inv xs, x, unit_inv_mul xs⟩
      add_zero := fun ⟨a, _⟩ => Set.elementExt (mul_one a)
      add_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_assoc a b c)
      add_neg := fun ⟨a, as⟩ => Set.elementExt (mul_unit_inv as)
    }

    theorem pow_nat_succ [Ring α] (a : α) (x : Nat) : a ^ (Nat.succ x) = a^x * a :=
      match x with
      | Nat.zero => by simp only [HPow.hPow, Pow.pow, NCSemiring.pow_nat, one_mul]
      | Nat.succ k  => rfl

    theorem pow_nat_one [Ring α] (n : Nat) : (1 : α)^n = 1 := by
      induction n with
      | zero      => rfl
      | succ k ih => rw [pow_nat_succ, ih, one_mul];
    theorem pow_nat_0 [Ring α] (a : α) : a ^ (0 : Nat) = 1 := rfl
    theorem pow_nat_1 [Ring α] (a : α) : a ^ (1 : Nat) = a := rfl

    theorem pow_nat_add_distrib [Ring α] (a : α) (m n : Nat) : a^(m + n) = a^m * a^n := by
      induction n with
      | zero      => rw [Nat.add_zero, pow_nat_0, mul_one]
      | succ k ih => rw [Nat.add_succ, pow_nat_succ, pow_nat_succ, ←mul_assoc, ih]
    
    theorem pow_nat_mul_distrib [Ring α] (a b : α) (m : Nat) : (a * b)^m = a^m * b^m := by
      induction m with
      | zero      => simp only [Nat.zero_eq, pow_nat_0, mul_one]
      | succ k ih => simp only [pow_nat_succ, ←mul_assoc, ih, mul_comm]

    theorem pow_nat_comp [Ring α] (a : α) (m n : Nat) : (a^m)^n = a^(m*n) := by 
      induction m with
      | zero => rw [Nat.zero_mul, pow_nat_0, pow_nat_one]
      | succ k ih => rw [pow_nat_succ, Nat.succ_mul, pow_nat_mul_distrib, ih, pow_nat_add_distrib]

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
    one_neq_zero := by simp

end M4R
