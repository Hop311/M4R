import M4R.Algebra.Ring.Quotient
import M4R.Algebra.Ring.MaxPrimeIdeal
import M4R.Algebra.Ring.Prod

namespace M4R
  open Semiring Ideal

  class UFD (α : Type _) extends IntegralDomain α where
    factors : {a : α} → a ≠ 0 → UnorderedList α
    factorsProd : ∀ {a : α}, (h : a ≠ 0) → (factors h).prod ≗ a
    irreducible_factors : ∀ {a : α}, (h : a ≠ 0) → ∀ x ∈ factors h, irreducible x
    unique : ∀ {f g : UnorderedList α}, (∀ x ∈ f, irreducible x) → (∀ x ∈ g, irreducible x) → f.prod ≗ g.prod → UnorderedList.rel associates f g

  class PID (α : Type _) extends IntegralDomain α where
    pid : ∀ I : Ideal α, Ideal.is_principal I

  class EuclideanDomain (α : Type _) extends IntegralDomain α where
    norm : α → Nat  -- norm 0 ? this is often not included so that deg can be a norm without worrying about deg 0 = -∞
    div_remainder (a b : α) : b ≠ 0 → ∃ q r, a = q * b + r ∧ (r = 0 ∨ norm r < norm b)

end M4R
