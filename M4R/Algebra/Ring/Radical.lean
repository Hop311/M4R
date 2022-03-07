import M4R.Algebra.Ring.MaxPrimeIdeal
import M4R.Algebra.Ring.Prod

namespace M4R
  open Monoid
  open NCSemiring
  open Semiring

  namespace Ideal

    def is_radical [Ring α] (I : Ideal α) : Prop := ∀ (x : α) (n : Nat), n ≠ 0 → x^n ∈ I → x ∈ I

    def rad [Ring α] (I : Ideal α) : Ideal α where
      subset     := {x | ∃ n : Nat, n ≠ 0 ∧ x^n ∈ I}
      has_zero   := ⟨1, Nat.one_ne_zero, by rw [pow_nat_1]; exact I.has_zero⟩
      add_closed := by
        intro a b ⟨m, hm, ham⟩ ⟨n, hn, hbn⟩; exact ⟨m+n-1,
          ⟨by
            apply Nat.ge_one_iff_ne_zero.mp
            apply Nat.le_of_succ_le_succ
            rw [Nat.sub_one, Nat.succ_pred_eq_of_pos (Nat.add_zero 0 ▸
              (Nat.add_lt_add (Nat.pos_iff_ne_zero.mpr hm) (Nat.pos_iff_ne_zero.mpr hn)))]
            exact Nat.add_le_add (Nat.ge_one_iff_ne_zero.mpr hm) (Nat.ge_one_iff_ne_zero.mpr hn),
          by
            rw [Semiring.binomial, Finset.map_sum.antidiagonal_eq_range, Finset.range_eq_range',
              Finset.map_sum.range'_split m (by
                rw [Nat.sub_one, Nat.succ_pred_eq_of_pos (Nat.add_zero 0 ▸
                  Nat.add_lt_add (Nat.pos_iff_ne_zero.mpr hm) (Nat.pos_iff_ne_zero.mpr hn))]
                exact Nat.le_add_right m n)]
            exact I.add_closed (Ideal.div_mem.mpr ⟨b^n, hbn,
              Finset.map_sum.prop_sum _ _ _ (divides_zero _) (fun k hk =>
                ⟨((m + n - 1).choose k) * a ^ k * b ^ (m - 1 - k), by
                  rw [Semiring.mul_comm, NCSemiring.mul_assoc, ←NCSemiring.pow_nat_add_distrib]
                  have : m - 1 - k + n = m + n - 1 - k := by
                    rw [Nat.add_sub_comm (Nat.ge_one_iff_ne_zero.mpr hm), Nat.add_sub_comm (by
                      apply Nat.lt_succ_if_le.mp
                      rw [Nat.sub_one, Nat.succ_pred_eq_of_pos (Nat.pos_iff_ne_zero.mpr hm), ←Nat.zero_add m]
                      exact (Finset.range'.mem_range'.mp hk).right)]
                  rw [this]⟩) (@divides_add _ _ (b^n))⟩)
              (Ideal.div_mem.mpr ⟨a^m, ham,
              Finset.map_sum.prop_sum _ _ _ (divides_zero _) (fun k hk =>
                ⟨((m + n - 1).choose k) * a ^ (k - m) * b ^ (m + n - 1 - k), by
                  rw [Semiring.mul_comm, NCSemiring.mul_assoc, Semiring.mul_comm _ (a^m),
                    NCSemiring.mul_assoc, ←NCSemiring.mul_assoc (a^_),
                    ←NCSemiring.pow_nat_add_distrib, ←NCSemiring.mul_assoc,
                    Nat.sub_add_cancel (Nat.zero_add m ▸ (Finset.range'.mem_range'.mp hk).left)]⟩)
                  (@divides_add _ _ (a^m))⟩)⟩⟩
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
