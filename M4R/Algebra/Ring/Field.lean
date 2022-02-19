import M4R.Algebra.Ring.Defs

namespace M4R

  class NCField (α : Type _) extends NonTrivialNCRing α where
    inv     : ∀ {a : α}, a ≠ 0 → α
    mul_inv : ∀ {a : α}, (h : a ≠ 0) → a * (inv h) = 1
    inv_mul : ∀ {a : α}, (h : a ≠ 0) → (inv h) * a = 1

  class Field (α : Type _) extends NCField α, Ring α

  class NCIntegralDomain (α : Type _) extends NonTrivialNCRing α where
    integral : ∀ {a b : α}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  
  class IntegralDomain (α : Type _) extends NCIntegralDomain α, Ring α

  namespace NCField
    open NCSemiring
    open NonTrivial

    instance toNonTrivialRing (α : Type _) [Field α] : NonTrivialRing α where
      toNonTrivial := Field.toNCField.toNonTrivial

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

  open NonTrivial
  open NCField

  def Ring.is_NonTrivial (α : Type _) [Ring α] : Prop := (1 : α) ≠ 0
  def Ring.is_NonTrivial.toNonTrivialRing [Ring α] (h : is_NonTrivial α) : NonTrivialRing α where
    toNonTrivial.one_neq_zero := h
  theorem NonTrivialRing.to_is_NonTrivial [NonTrivialRing α] : Ring.is_NonTrivial α := NonTrivial.one_neq_zero

  def Ring.is_Field (α : Type _) [Ring α] : Prop := is_NonTrivial α ∧ ∀ {a : α}, (h : a ≠ 0) → ∃ b, a * b = 1
  noncomputable def Ring.is_Field.toField [Ring α] (h : is_Field α) : Field α where
    toNonTrivial.one_neq_zero := h.left
    mul_comm := mul_comm
    inv := fun ha => Classical.choose (h.right ha)
    mul_inv := fun ha => Classical.choose_spec (h.right ha)
    inv_mul := fun ha => by rw [mul_comm]; exact Classical.choose_spec (h.right ha)
  theorem Field.to_is_Field [Field α] : Ring.is_Field α :=
    ⟨one_neq_zero, fun ha => ⟨inv ha, mul_inv ha⟩⟩

  def Ring.is_IntegralDomain (α : Type _) [Ring α] : Prop := is_NonTrivial α ∧ ∀ {a b : α}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  def Ring.is_IntegralDomain.toIntegralDomain [Ring α] (h : is_IntegralDomain α) : IntegralDomain α where
    toNonTrivial.one_neq_zero := h.left
    mul_comm := mul_comm
    integral := h.right
  theorem IntegralDomain.to_is_IntegralDomain [i : IntegralDomain α] : Ring.is_IntegralDomain α :=
    ⟨i.toNonTrivial.one_neq_zero, i.integral⟩

  instance IntegralDomain.toNonTrivialRing (α : Type _) [IntegralDomain α] : NonTrivialRing α where
      toNonTrivial := IntegralDomain.toNCIntegralDomain.toNonTrivial
  instance NCField.toNCIntegralDomain (α : Type _) [NCField α] : NCIntegralDomain α where
    integral := NCField.integral
  def Field.to_is_IntegralDomain (α : Type _) [Field α] : Ring.is_IntegralDomain α :=
    ⟨one_neq_zero, integral⟩
  instance Field.toIntegralDomain (α : Type _) [Field α] : IntegralDomain α :=
    (to_is_IntegralDomain α).toIntegralDomain

end M4R