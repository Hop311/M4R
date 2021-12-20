import M4R.Algebra.Ring.Defs

namespace M4R
  namespace Ring
    open Group
    open AbelianGroup
    open NonCommutativeRing


    theorem mul_zero [NonCommutativeRing α] (a : α) : a * 0 = 0 := by
      rw [←add_right_cancel _ _ (a * 0), zero_add, ←mul_distrib_left, zero_add]
    theorem zero_mul [NonCommutativeRing α] (a : α) : 0 * a = 0 := by
      rw [←add_right_cancel _ _ (0 * a), zero_add, ←mul_distrib_right, zero_add]

    theorem neg_mul [NonCommutativeRing α] (a b : α) : -a * b = -(a * b) := by
      rw [←add_right_cancel _ _ (a * b), neg_add, ←mul_distrib_right, neg_add, zero_mul]
    theorem mul_neg [NonCommutativeRing α] (a b : α) : a * -b = -(a * b) := by
      rw [←add_right_cancel _ _ (a * b), neg_add, ←mul_distrib_left, neg_add, mul_zero]

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


    /-def unit_set (α : Type _) [Ring α] : Set α := {x | isUnit x}
    instance UnitGroup [Ring α] : Group ↑(unit_set α) where
      zero := ⟨1, ⟨1, by rw [mul_one]⟩⟩
      add := fun a b => ⟨a.val * b.val, unit_mul a.property b.property⟩
      neg := fun ⟨x, xs⟩ => by
        let ⟨y, xy⟩ := Classical.indefiniteDescription (fun c => x * c = 1) xs;
        exact ⟨y, ⟨x, by rw [mul_comm]; exact xy⟩⟩
      add_zero := by intro a; apply Set.ext; exact mul_one a.val;
      add_assoc := by intro a b c; apply Set.ext; exact mul_assoc a.val b.val c.val
      add_neg := by
        intro a; apply Set.ext; simp [Set.inclusion, HAdd.hAdd, Add.add, Neg.neg];-/
      
    theorem pow_nat_succ [Ring α] (a : α) (x : Nat) : a ^ (Nat.succ x) = a^x * a :=
      match x with
      | Nat.zero => by simp [HPow.hPow, Pow.pow, Ring.pow_nat, one_mul]
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
      | zero      => simp [pow_nat_0, mul_one]
      | succ k ih => simp [pow_nat_succ, ←mul_assoc, ih, mul_comm]

    theorem pow_nat_comp [Ring α] (a : α) (m n : Nat) : (a^m)^n = a^(m*n) := by 
      induction m with
      | zero => rw [Nat.zero_mul, pow_nat_0, pow_nat_one]
      | succ k ih => rw [pow_nat_succ, Nat.succ_mul, pow_nat_mul_distrib, ih, pow_nat_add_distrib]

  end Ring
end M4R