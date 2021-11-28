import M4R.Algebra.Ring.Quotient

namespace M4R
  namespace Ring
  
    class IntegralDomain (α : Type _) extends Ring α where
    integral : ∀ a b : α, a ≠ 0 → b ≠ 0 → a * b ≠ 0

    class PrincipalIdealDomain (α : Type _) extends IntegralDomain α where
      pid : ∀ I : Ideal α, Ideal.is_principal I

    class EuclideanDomain (α : Type _) extends IntegralDomain α where
      norm : α → Nat  -- norm 0 ? this is often not included so that deg can be a norm without worrying about deg 0 = -∞
      div_remainder (a b : α) : b ≠ 0 → ∃ q r, a = q * b + r ∧ (r = 0 ∨ norm r < norm b)

    class Field (α : Type _) extends Ring α where
      one_neq_zero : (1 : α) ≠ 0
      inverses     : ∀ a : α, a = 0 ∨ isUnit a
      
  end Ring
end M4R