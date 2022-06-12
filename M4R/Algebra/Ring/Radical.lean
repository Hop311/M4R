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

      theorem subset {I J : Ideal α} (h : I ⊆ J) : I.radical ⊆ J.radical :=
        fun x ⟨n, hn0, hxn⟩ => ⟨n, hn0, h hxn⟩

      protected theorem of_unit (α) [Ring α] : (1 : Ideal α).radical = 1 :=
        unit_ideal_in (radical.sub_self 1)

      protected theorem repeat : I.radical.radical = I.radical :=
        Ideal.ext'.mpr fun x => ⟨fun ⟨n, hn, m, hm, hxm⟩ => ⟨n * m, (Nat.mul_neq_zero n m).mpr ⟨hn, hm⟩,
          pow_nat_comp x n m ▸ hxm⟩, (radical.sub_self _ ·)⟩

      protected theorem add (J : Ideal α) : (I + J).radical = (I.radical + J.radical).radical :=
        Ideal.ext'.mpr fun x => ⟨fun ⟨n, hn, i, hi, j, hj, hij⟩ => ⟨n, hn, i, radical.sub_self I hi, j,
          radical.sub_self J hj, hij⟩, fun ⟨n, hn, i, hi, j, hj, hij⟩ => radical.repeat _ ▸ ⟨n, hn, hij ▸
            (I + J).radical.add_closed (radical.subset (Ideal.add.subset I J) hi) (radical.subset (Ideal.add.subset' I J) hj)⟩⟩

      protected theorem eq_unit_ideal_iff {I : Ideal α} : I.radical = 1 ↔ I = 1 :=
        ⟨fun h => let ⟨n, hn, h1n⟩ := is_unit_ideal.mp h; is_unit_ideal.mpr (pow_nat_one n ▸ h1n),
          (· ▸ radical.of_unit α)⟩

      protected theorem proper_iff {I : Ideal α} : I.radical.proper_ideal ↔ I.proper_ideal :=
        not_iff_not.mpr radical.eq_unit_ideal_iff

      protected theorem add_eq_one {I J : Ideal α} (h : I.radical + J.radical = 1) : I + J = 1 := by
        have := congrArg Ideal.radical h
        rw [←radical.add, radical.of_unit] at this
        exact radical.eq_unit_ideal_iff.mp this
    end radical

    protected theorem is_radical.eq_rad {I : Ideal α} (hI : I.is_radical) : I.radical = I :=
      Ideal.antisymm (fun x hx => let ⟨n, hn0, hxn⟩ := hx; hI x n hn0 hxn) (radical.sub_self I)

    theorem prime_radical {P : Ideal α} (hP : P.is_prime) : P.is_radical := fun x n hn hxn => by
      induction n with
      | zero   => contradiction
      | succ n ih =>
        byCases hn' : n = 0
        { rw [hn', pow_nat_1] at hxn; exact hxn }
        { exact Or.elim (hP.right (x^n) x (pow_nat_succ x n ▸ hxn)) (ih hn') id }

    def is_primary : Prop := I.proper_ideal ∧ ∀ a b : α, a * b ∈ I → a ∈ I ∨ b ∈ I.radical

    theorem is_primary_of_prime {I : Ideal α} (hI : I.is_prime) : I.is_primary :=
      And.imp_right (fun h a b hab => Or.imp_right (Ideal.radical.sub_self I ·) (h a b hab)) hI

    theorem is_primary_of_radical_maximal {I : Ideal α} (h : I.radical.is_maximal) : I.is_primary :=
      ⟨Ideal.proper_ideal_subset (radical.sub_self I) h.left, fun a b hab => by
        apply or_iff_not_imp_right.mpr; intro hb
        have := (h.right (Ideal.add.subset I.radical (principal b))).resolve_left
          fun h => hb (h ▸ Ideal.add.subset' _ _ (generator_in_principal b))
        have : I.radical + (principal b).radical = 1 :=
          unit_ideal_in (this ▸ Ideal.add.subset_add_subset (Subset.refl _) (radical.sub_self _))
        let ⟨i, hi, j, ⟨k, hk⟩, hij⟩ := is_unit_ideal.mp (radical.add_eq_one this)
        rw [←mul_one a, ←hij, ←hk, mul_distrib_left, ←mul_assoc]
        exact I.add_closed (I.mul_closed a hi) (I.mul_closed' hab k)⟩

    theorem contraction_radical [Ring β] (f : α →ᵣ₁ β) (I : Ideal β) : contractionᵣ₁ f I.radical = (contractionᵣ₁ f I).radical :=
      Ideal.ext'.mpr fun x => ⟨fun ⟨n, hn, hnx⟩ => ⟨n, hn, by rw [←f.preserve_pow x n] at hnx; exact hnx⟩,
        fun ⟨n, hn, hnx⟩ => ⟨n, hn, f.preserve_pow x n ▸ hnx⟩⟩

    theorem contraction_is_primary [Ring β] (f : α →ᵣ₁ β) {I : Ideal β} (hI : I.is_primary) : (contractionᵣ₁ f I).is_primary :=
      ⟨contraction.proper_of_preserve_one f.preserve_mul_right f.preserve_one hI.left, fun a b hab =>
        (hI.right (f a) (f b) (f.preserve_mul a b ▸ hab)).imp_right (fun h => contraction_radical f I ▸ h)⟩

    theorem radical_prime_of_primary {I : Ideal α} (hI : I.is_primary) : I.radical.is_prime :=
      ⟨radical.proper_iff.mpr hI.left, fun a b ⟨n, hn, habn⟩ => or_iff_not_imp_left.mpr fun ha =>
        radical.is_radical I b n hn ((hI.right (a ^ n) (b ^ n) (pow_nat_mul_distrib a b n
          ▸ habn)).resolve_left (fun ha' => ha (radical.is_radical I a n hn (radical.sub_self I ha'))))⟩

    theorem radical_minimal_prime_of_primary {I : Ideal α} (hI : I.is_primary) : I.radical.minimal_prime_ideal_of I :=
      ⟨radical_prime_of_primary hI, radical.sub_self I, fun hJ hIJ hJI => Ideal.antisymm hJI (is_radical.eq_rad (prime_radical hJ) ▸ radical.subset hIJ)⟩

    theorem radical_pow_of_prime {P : Ideal α} (hP : P.is_prime) (n : Nat) (hn : n ≠ 0) : (P ^ n).radical = P :=
      Ideal.antisymm (fun x ⟨k, hk, hkx⟩ => prime_radical hP x k hk (product.pow_subset P n hn hkx)) (fun x hx => ⟨n, hn, product.pow_contains n hx⟩)


  end Ideal

  namespace Ring
    open QuotientRing
    variable (α : Type _) [Ring α]

    def nil_radical : Ideal α := (0 : Ideal α).radical

    protected theorem nil_radical.def : (0 : Ideal α).radical = nil_radical α := rfl

    def is_reduced : Prop := nil_radical α = 0

    abbrev reduced := QClass (nil_radical α)

    theorem reduced_reduced : is_reduced (reduced α) :=
      Ideal.is_zero_ideal.mpr fun a ⟨n, hn0, han⟩ =>
        @Quotient.ind α (QSetoid _) (fun (x : QClass _) => x^n = 0 → x = 0) (fun x (hxn : toQuotient _ _ ^ n = 0) =>
          let ⟨m, hm0, hxnm⟩ : x^n ∈ nil_radical α := is_zero.mp (preserve_pow_nat _ x n ▸ hxn)
          is_zero.mpr ⟨n * m, (Nat.mul_neq_zero n m).mpr ⟨hn0, hm0⟩, pow_nat_comp x n m ▸ hxnm⟩) a han

    noncomputable def jacobson_radical : Ideal α := ⋂₀ Ring.MaxSpec α

    variable {α}

    theorem nil_radical_proper (h : Ring.is_NonTrivial α) : (nil_radical α).proper_ideal :=
      fun h' => let ⟨n, hn, h1n⟩ := Ideal.is_unit_ideal.mp h'; absurd (pow_nat_one n ▸ h1n) h

    theorem maximal_subset_jacobson {M : Ideal α} (hM : M.is_maximal) : jacobson_radical α ⊆ M :=
      fun x hx => Ideal.sIntersection.mem.mp hx M hM

  end Ring
end M4R
