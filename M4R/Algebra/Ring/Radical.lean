import M4R.Algebra.Ring.MaxPrimeIdeal
import M4R.Algebra.Ring.Prod

namespace M4R
  open Monoid NCSemiring Semiring

  namespace Ideal
    variable [Ring α] (I : Ideal α)

    protected def is_radical : Prop := ∀ (x : α) (n : Nat), n ≠ 0 → x^n ∈ I → x ∈ I

    def radical : Ideal α where
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

    namespace radical
      protected theorem is_radical : I.radical.is_radical :=
        fun x n hn ⟨m, hm, hx⟩ => ⟨n * m, (Nat.mul_neq_zero _ _).mpr ⟨hn, hm⟩,
          by rw [←pow_nat_comp]; exact hx⟩

      protected theorem sub_self : I ⊆ I.radical := fun x hx =>
        ⟨1, Nat.one_ne_zero, NCSemiring.pow_nat_1 x ▸ hx⟩

    end radical

    protected theorem is_radical.eq_rad {I : Ideal α} (hI : I.is_radical) : I.radical = I :=
      Ideal.antisymm (fun x hx => let ⟨n, hn0, hxn⟩ := hx; hI x n hn0 hxn) (radical.sub_self I)

    theorem subset_radical {I J : Ideal α} (h : I ⊆ J) : I.radical ⊆ J.radical :=
      fun x ⟨n, hn0, hxn⟩ => ⟨n, hn0, h hxn⟩

    theorem prime_radical {I : Ideal α} (hI : I.is_prime) : I.is_radical := fun x n hn hxn => by
      induction n with
      | zero   => contradiction
      | succ n ih =>
        byCases hn' : n = 0
        { rw [hn', pow_nat_1] at hxn; exact hxn }
        { exact Or.elim (hI.right (x^n) x (pow_nat_succ x n ▸ hxn)) (ih hn') id }

  end Ideal

  namespace Ring
    open QuotientRing
    variable (α : Type _) [Ring α]

    def nil_radical : Ideal α := (0 : Ideal α).radical

    def is_reduced : Prop := nil_radical α = 0

    abbrev reduced := QClass (nil_radical α)

    theorem reduced_reduced : is_reduced (reduced α) :=
      Ideal.is_zero_ideal.mpr fun a ⟨n, hn0, han⟩ =>
        @Quotient.ind α (QSetoid _) (fun (x : QClass _) => x^n = 0 → x = 0) (fun x (hxn : toQuotient _ _ ^ n = 0) =>
          let ⟨m, hm0, hxnm⟩ : x^n ∈ nil_radical α := is_zero.mp (preserve_pow_nat _ x n ▸ hxn)
          is_zero.mpr ⟨n * m, (Nat.mul_neq_zero n m).mpr ⟨hn0, hm0⟩, pow_nat_comp x n m ▸ hxnm⟩) a han

    noncomputable def jacobson_radical : Ideal α := ⋂₀ {J | J.is_maximal}

    theorem jacobson_radical.units : ∀ x : α, x ∈ jacobson_radical α ↔
      ↑{y : α | ∃ a, 1 + a * x = y} ⊆ unit_set α := by
        sorry

  end Ring
end M4R
