import M4R.Algebra.Ring.MaxPrimeIdeal

namespace M4R

  namespace Ideal
    structure chain (α : Type _) [Ring α] where
      f        : Nat → Ideal α
      hsubsets : ∀ n, f n ⊆ f n.succ

    namespace chain
      variable [Ring α] (c : chain α)

      instance chain_coefun : CoeFun (chain α) (fun _ => Nat → Ideal α) where coe := f

      def is_stable : Prop := ∃ N, ∀ n, N ≤ n → c n = c N

      def is_prime : Prop := ∀ n, (c n).is_prime

      def strict_infinite : Prop := ∀ n, c n ≠ c n.succ

      def strict_stable : Prop := ∃ N, (∀ n, n < N → c n ≠ c n.succ) ∧ (∀ n, N ≤ n → c n = c N)

      def strict : Prop := strict_stable c ∨ strict_infinite c

    end chain
  end Ideal

  open Ideal

  namespace Ring
    namespace krull_dim
      open Ideal

      structure prime_chain (α : Type _) [Ring α] extends chain α where
        hprime : tochain.is_prime

      structure strict_infinite_chain (α : Type _) [Ring α] extends prime_chain α where
        hstrict_inf : tochain.strict_infinite

      structure strict_stable_chain (α : Type _) [Ring α] extends chain α where
        hstrict_stab : tochain.strict_stable

      noncomputable def strict_stable_chain.length [Ring α] (c : strict_stable_chain α) : Nat :=
        Classical.choose c.hstrict_stab

      def krull_dim_infinite (α : Type _) [Ring α] : Prop := Nonempty (strict_infinite_chain α) ∨
        (∀ n, ∃ c : strict_stable_chain α, n ≤ c.length)

      def has_krull_dim (α : Type _) [Ring α] : Prop := (∀ c : prime_chain α, ¬c.strict_infinite) ∧
        ∃ c : strict_stable_chain α, ∀ d : strict_stable_chain α, d.length ≤ c.length

      theorem has_krull_dim_iff_not_infinite [NonTrivialRing α] : has_krull_dim α ↔ ¬krull_dim_infinite α := by
        simp only [has_krull_dim, krull_dim_infinite, not_or_iff_and_not, not_forall, not_exists, Nat.not_le]
        apply Iff.and
        { rw [←not_exists, not_iff_not]; exact ⟨fun ⟨c, hc⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨c, hc⟩⟩ }
        { exact ⟨fun ⟨c, hc⟩ => ⟨c.length.succ, fun d => Nat.lt_succ_of_le (hc d)⟩,
          fun ⟨c, hc⟩ => by
            -- need the fact that any non trivial ring contains a prime ideal
            sorry⟩ }

      noncomputable def dim [Ring α] (h : has_krull_dim α) : Nat := (Classical.choose h.right).length

    end krull_dim
  end Ring

  def Ring.is_noetherian (α : Type _) [Ring α] : Prop := ∀ c : chain α, c.is_stable

  class NoetherianRing (α : Type _) extends Ring α where
    noetherian : Ring.is_noetherian α

  namespace NoetherianRing

    theorem ideal_finitely_generated [NoetherianRing α] (I : Ideal α) : I.finitely_generated := by
      apply Ideal.iff_finite_subbasis'.mpr
      intro S hS hIS
      let c : chain α := {
          f        := sorry
          hsubsets := sorry
        }
      have := NoetherianRing.noetherian c
      sorry

  end NoetherianRing
end M4R
