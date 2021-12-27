import M4R.Algebra.Ring.Quotient
import M4R.Set

namespace M4R

    class NCIntegralDomain (α : Type _) extends NonTrivialNCRing α where
      integral : ∀ {a b : α}, a ≠ 0 → b ≠ 0 → a * b ≠ 0
  
    class IntegralDomain (α : Type _) extends NCIntegralDomain α, Ring α

    instance IntegralDomain.toNonTrivialRing (α : Type _) [IntegralDomain α] : NonTrivialRing α where
      one_neq_zero := IntegralDomain.toNCIntegralDomain.one_neq_zero

    instance NCField.toNCIntegralDomain (α : Type _) [NCField α] : NCIntegralDomain α where
      integral := NCField.integral

    instance Field.toIntegralDomain (α : Type _) [Field α] : IntegralDomain α where
      integral := NCField.integral
      mul_comm := Field.mul_comm

    -- UnorderedList.prod not yet defined
    /-class UFD (α : Type _) extends IntegralDomain α where
      factors : α → UnorderedList α
      factorsProd : ∀ {a : α}, (factors a).prod ≗ a --∀ {a : α}, a ≠ 0 → (factors a).prod ≗ a
      irreducible_factors : ∀ {a : α}, a ≠ 0 →  ∀ x ∈ factors a, irreducible x
      unique : ∀ {f g : UnorderedList α},
        (∀ x ∈ f, irreducible x) → (∀ x ∈ g, irreducible x) → f.prod ≗ g.prod → UnorderedList.rel associates f g-/

    class PID (α : Type _) extends IntegralDomain α where
      pid : ∀ I : Ideal α, Ideal.is_principal I

    class EuclideanDomain (α : Type _) extends IntegralDomain α where
      norm : α → Nat  -- norm 0 ? this is often not included so that deg can be a norm without worrying about deg 0 = -∞
      div_remainder (a b : α) : b ≠ 0 → ∃ q r, a = q * b + r ∧ (r = 0 ∨ norm r < norm b)
    
end M4R