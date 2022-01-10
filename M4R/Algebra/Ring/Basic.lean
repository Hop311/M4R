import M4R.Algebra.Ring.Defs

namespace M4R
  section
    open NonTrivialNCRing
    open NonTrivialRing
    open NCField

    def Ring.is_NonTrivial (α : Type _) [Ring α] : Prop := (1 : α) ≠ 0
    def Ring.is_NonTrivial.toNonTrivialRing [Ring α] (h : is_NonTrivial α) : NonTrivialRing α where
      one_neq_zero := h
    theorem NonTrivialRing.to_is_NonTrivial [NonTrivialRing α] : Ring.is_NonTrivial α := one_neq_zero

    def Ring.is_Field (α : Type _) [Ring α] : Prop := is_NonTrivial α ∧ ∀ {a : α}, (h : a ≠ 0) → ∃ b, a * b = 1
    noncomputable def Ring.is_Field.toField [Ring α] (h : is_Field α) : Field α where
      one_neq_zero := h.left
      mul_comm := mul_comm
      inv := fun ha => Classical.choose (h.right ha)
      mul_inv := fun ha => Classical.choose_spec (h.right ha)
      inv_mul := fun ha => by rw [mul_comm]; exact Classical.choose_spec (h.right ha)
    theorem Field.to_is_Field [Field α] : Ring.is_Field α :=
      ⟨one_neq_zero, fun ha => ⟨inv ha, mul_inv ha⟩⟩

    def Ring.is_IntegralDomain (α : Type _) [Ring α] : Prop := is_NonTrivial α ∧ ∀ {a b : α}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
    def Ring.is_IntegralDomain.toIntegralDomain [Ring α] (h : is_IntegralDomain α) : IntegralDomain α where
      one_neq_zero := h.left
      mul_comm := mul_comm
      integral := h.right
    theorem IntegralDomain.to_is_IntegralDomain [i : IntegralDomain α] : Ring.is_IntegralDomain α :=
      ⟨i.one_neq_zero, i.integral⟩
  end
  namespace NCRing
    open Group

    theorem mul_zero [NCRing α] (a : α) : a * 0 = 0 := by
      rw [←add_right_cancel _ _ (a * 0), zero_add, ←mul_distrib_left, zero_add]
    theorem zero_mul [NCRing α] (a : α) : 0 * a = 0 := by
      rw [←add_right_cancel _ _ (0 * a), zero_add, ←mul_distrib_right, zero_add]

    theorem neg_mul [NCRing α] (a b : α) : -a * b = -(a * b) := by
      rw [←add_right_cancel _ _ (a * b), neg_add, ←mul_distrib_right, neg_add, zero_mul]
    theorem mul_neg [NCRing α] (a b : α) : a * -b = -(a * b) := by
      rw [←add_right_cancel _ _ (a * b), neg_add, ←mul_distrib_left, neg_add, mul_zero]

  end NCRing

  namespace Ring
    open NCRing

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

    noncomputable instance UnitGroup [Ring α] : Group ↑(unit_set α) where
      zero := ⟨1, ⟨1, by rw [mul_one]⟩⟩
      add := fun a b => ⟨a.val * b.val, unit_mul a.property b.property⟩
      neg := fun ⟨x, xs⟩ => ⟨unit_inv xs, x, unit_inv_mul xs⟩
      add_zero := fun ⟨a, _⟩ => Set.elementExt (mul_one a)
      add_assoc := fun ⟨a, _⟩ ⟨b, _⟩ ⟨c, _⟩ => Set.elementExt (mul_assoc a b c)
      add_neg := fun ⟨a, as⟩ => Set.elementExt (mul_unit_inv as)
      
    theorem pow_nat_succ [Ring α] (a : α) (x : Nat) : a ^ (Nat.succ x) = a^x * a :=
      match x with
      | Nat.zero => by simp only [HPow.hPow, Pow.pow, Ring.pow_nat, one_mul]
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

  end Ring

  namespace NCField
    open NCRing
    open NonTrivialNCRing

    instance toNonTrivialRing (α : Type _) [Field α] : NonTrivialRing α where
      one_neq_zero := Field.toNCField.one_neq_zero

    theorem inv_nonzero [NCField α] : ∀ {a : α}, (h : a ≠ 0) → inv h ≠ 0 := by
      intro a h hi;
      have := mul_inv h
      rw [hi, mul_zero] at this
      exact one_neq_zero this.symm

    theorem mul_right_cancel [NCField α] {a b c : α} (h : c ≠ 0) : a * c = b * c ↔ a = b :=
      ⟨fun hab => by rw [←mul_one a, ←mul_one b, ←mul_inv h, ←mul_assoc, ←mul_assoc, hab],
        fun hab => by rw [hab]⟩

    theorem inv_inv [NCField α] : ∀ {a : α}, (h : a ≠ 0) → inv (inv_nonzero h) = a :=
      fun h => by rw [←mul_right_cancel (inv_nonzero h), inv_mul, mul_inv]

    theorem integral [NCField α] : ∀ {a b : α}, a ≠ 0 → b ≠ 0 → a * b ≠ 0 := by
      intro a b ha hb hab;
      rw [←zero_mul b, mul_right_cancel hb] at hab
      exact ha hab

    theorem inv_of_mul [NCField α] {a b : α} (ha : a ≠ 0) (hb : b ≠ 0) :
      inv (integral ha hb) = (inv hb) * (inv ha) := by
        rw [←mul_right_cancel ha, mul_assoc, inv_mul, mul_one, ←mul_right_cancel hb, inv_mul, mul_assoc]
        exact inv_mul (integral ha hb)

  end NCField

  open NonTrivialRing
  open NCField

  instance IntegralDomain.toNonTrivialRing (α : Type _) [IntegralDomain α] : NonTrivialRing α where
      one_neq_zero := IntegralDomain.toNCIntegralDomain.one_neq_zero

  instance NCField.toNCIntegralDomain (α : Type _) [NCField α] : NCIntegralDomain α where
    integral := NCField.integral

  def Field.to_is_IntegralDomain (α : Type _) [Field α] : Ring.is_IntegralDomain α :=
    ⟨one_neq_zero, integral⟩

  instance Field.toIntegralDomain (α : Type _) [Field α] : IntegralDomain α :=
    (to_is_IntegralDomain α).toIntegralDomain

end M4R