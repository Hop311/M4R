import M4R.Algebra.Ring.MaxPrimeIdeal

namespace M4R
  open Monoid
  open NCSemiring
  open Ring

  namespace Ideal

    def is_radical [Ring α] (I : Ideal α) : Prop := ∀ (x : α) (n : Nat), n ≠ 0 → x^n ∈ I → x ∈ I

    def rad [Ring α] (I : Ideal α) : Ideal α where
      subset := {x | ∃ n : Nat, n ≠ 0 ∧ x^n ∈ I}
      has_zero := ⟨1, Nat.one_ne_zero, by rw [pow_nat_1]; exact I.has_zero⟩
      add_closed := by
        intro a b ⟨m, hm, ham⟩ ⟨n, hn, hbn⟩; exact ⟨m+n-1, ⟨by 
          rw [←Nat.sub_self 1]; intro h; sorry, by sorry⟩ ⟩
      mul_closed := fun a b ⟨m, ⟨hm, hbm⟩⟩ => ⟨m, ⟨hm, by rw [pow_nat_mul_distrib]; exact I.mul_closed (a^m) hbm⟩⟩

    protected theorem rad.is_radical [Ring α] (I : Ideal α) : I.rad.is_radical :=
      fun x n hn ⟨m, hm, hx⟩ => ⟨n * m, (Nat.mul_neq_zero _ _).mpr ⟨hn, hm⟩,
        by rw [←pow_nat_comp]; exact hx⟩

    theorem radical_prime_intersection [Ring α] (I : Ideal α) : I.rad = ⋂₀ {J | I ⊆ J ∧ J.is_prime} := by
      sorry

  end Ideal

  namespace Ring
    open QuotientRing

    def nil_radical (α : Type _) [Ring α] : Ideal α := Ideal.ZeroIdeal.rad

    def is_reduced (α : Type _) [Ring α] : Prop := nil_radical α = Ideal.ZeroIdeal

    theorem reduced_reduced (α : Type _) [Ring α] : is_reduced (QClass (nil_radical α)) := by
      sorry

    noncomputable def jacobson_radical (α : Type _) [Ring α] : Ideal α := ⋂₀ {J | J.is_maximal}

    theorem jacobson_radical.units [Ring α] :
      ∀ x : α, x ∈ jacobson_radical α ↔ ↑{y : α | ∃ a, 1 + a * x = y} ⊆ unit_set α := by
        sorry

  end Ring
end M4R