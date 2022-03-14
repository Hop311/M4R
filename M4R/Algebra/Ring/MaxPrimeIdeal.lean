import M4R.Algebra.Ring.Field
import M4R.Algebra.Ring.Quotient

namespace M4R
  open Group Monoid CommMonoid NCSemiring Ring QuotientRing

  namespace Ideal
    def is_prime [Ring α] (I : Ideal α) : Prop :=
      I.proper_ideal ∧ ∀ r s, r * s ∈ I → r ∈ I ∨ s ∈ I

    def is_maximal [Ring α] (I : Ideal α) : Prop :=
      I.proper_ideal ∧ ∀ {J : Ideal α}, I ⊆ J → J = I ∨ J = 1

    theorem maximal_neq [Ring α] {I : Ideal α} (h : I.is_maximal) : ∀ {J : Ideal α}, I ⊊ J → J = 1 := by
      intro J ⟨hIJ, x, hxI, hxJ⟩;
      apply (h.right hIJ).resolve_left fun heq => by rw [heq] at hxJ; exact hxI hxJ

    instance ProperIdealNonTrivialRing [Ring α] {I : Ideal α} (hI : I.proper_ideal) : NonTrivialRing (QClass I) where
      toNonTrivial.one_neq_zero := by
        intro h10;
        have := @Quotient.exact α (QSetoid I) 0 1 h10.symm;
        simp only [HasEquiv.Equiv, Setoid.r, QRel] at this
        rw [neg_zero, zero_add] at this
        exact hI (Ideal.is_unit_ideal.mpr this)

    theorem NonTrivialRingProperIdeal [Ring α] {I : Ideal α} (h : is_NonTrivial (QClass I)) : I.proper_ideal := by
      intro hu;
      have : (1 : QClass I) = (0 : QClass I) := by
        apply Eq.symm; apply Quot.sound; simp only [Setoid.r, QRel]
        rw [neg_zero, zero_add]; exact Ideal.is_unit_ideal.mp hu
      exact h this

    theorem maximal_has_inverses [Ring α] {I : Ideal α} (hI : I.is_maximal) :
      ∀ {a : α}, toQuotient I a ≠ 0 → ∃ r : α, (toQuotient I a) * (toQuotient I r) = 1 := by
        intro a ha;
        have : I ⊊ I + (principal a) :=
          ⟨Ideal.add.subset I (principal a), a, non_zero.mp ha, 0, I.has_zero, a, ⟨1, mul_one a⟩, zero_add a⟩
        have ⟨i, hi, j, ⟨r, hj⟩, hij⟩ :=
          is_unit_ideal.mp (maximal_neq hI this)
        exact ⟨r, Quot.sound (by
            simp only [QRel]
            rw [hj, add_comm, ←sub_right.mp hij]
            exact hi)⟩
    theorem maximal_has_inverses' [Ring α] {I : Ideal α} (hI : I.is_maximal) :
      ∀ {a : QClass I}, a ≠ 0 → ∃ r : QClass I, a * r = 1 :=
        @Quotient.ind α (QSetoid I) (fun (a : QClass I) => a ≠ 0 → ∃ r : QClass I, a * r = 1) (fun _ ha =>
          have ⟨r, hr⟩ := maximal_has_inverses hI ha
          ⟨toQuotient I r, hr⟩)
    noncomputable def maximal_inv [Ring α] {I : Ideal α} (hI : I.is_maximal) : {a : QClass I} → a ≠ 0 → QClass I :=
      fun ha => Classical.choose (maximal_has_inverses' hI ha)

    noncomputable instance MaximalField [Ring α] {I : Ideal α} (hI : I.is_maximal) : Field (QClass I) where
      toNonTrivial := (ProperIdealNonTrivialRing hI.left).toNonTrivial
      mul_comm := by
        apply Function.Quotient.ind₂; intros; apply Quot.sound; simp only [QRel]
        rw [mul_comm, neg_add]; exact I.has_zero
      inv := maximal_inv hI
      mul_inv := fun ha => Classical.choose_spec (maximal_has_inverses' hI ha)
      inv_mul := fun ha => by
        rw [mul_comm];
        exact Classical.choose_spec (maximal_has_inverses' hI ha)

    theorem FieldMaximal [Ring α] {I : Ideal α} (h : is_Field (QClass I)) : I.is_maximal := by
      simp only [is_maximal, is_Field] at *
      exact ⟨NonTrivialRingProperIdeal h.left, by
        intro J hIJ;
        cases Classical.em (I = J) with
        | inl heq => exact Or.inl heq.symm 
        | inr hneq =>
          apply Or.inr; apply is_unit_ideal.mpr;
          let ⟨x, xJ, nxI⟩ := Classical.choice (Set.minus.nonempty 
            (Set.subset.neq_proper hIJ (fun h' => hneq (Ideal.ext.mp h'))))
          let ⟨b, hb⟩ := h.right (non_zero.mpr nxI)
          exact @Quotient.ind α (QSetoid I) (fun (c : QClass I) => c = b → 1 ∈ J) (fun b' hb' => by
            rw [←hb'] at hb;
            have := @Quotient.exact α (QSetoid I) _ _ hb
            simp only [HasEquiv.Equiv, Setoid.r, QRel] at this
            have := J.add_closed (J.mul_closed b' xJ) (hIJ this)
            rw [mul_comm, ←add_assoc, add_neg, zero_add] at this
            exact this) b rfl⟩

    instance PrimeIntegralDomain [Ring α] {I : Ideal α} (hI : I.is_prime) : IntegralDomain (QClass I) where
      toNonTrivial := (ProperIdealNonTrivialRing hI.left).toNonTrivial
      mul_comm := by
        apply Function.Quotient.ind₂; intro a b
        apply Quot.sound; simp [QRel]
        rw [mul_comm, neg_add]
        exact I.has_zero
      integral := @Function.Quotient.ind₂ α α (QRel I) (QRel I)
          (fun (a b : QClass I) => a ≠ 0 → b ≠ 0 → a * b ≠ 0)
          (fun a b ha hb => non_zero.mpr fun hab =>
            Or.elim (hI.right a b hab) (non_zero.mp ha) (non_zero.mp hb))

    theorem IntegralDomainPrime [Ring α] {I : Ideal α} (h : is_IntegralDomain (QClass I)) : I.is_prime :=
      ⟨NonTrivialRingProperIdeal h.left, by
        simp [is_IntegralDomain] at h
        intro r s hrs
        apply Classical.byContradiction
        intro h'
        simp only [not_or_iff_and_not] at h'
        exact non_zero.mp (h.right (non_zero.mpr h'.left) (non_zero.mpr h'.right)) hrs⟩

    theorem maximal_is_prime [Ring α] {I : Ideal α} (h : I.is_maximal) : I.is_prime :=
      IntegralDomainPrime (MaximalField h).to_is_IntegralDomain

  end Ideal
  namespace Ring
    def Spec (α : Type _) [Ring α] : Set (Ideal α) := {I | I.is_prime}
    def MaxSpec (α : Type _) [Ring α] : Set (Ideal α) := {I | I.is_maximal}

    theorem MaxSpec_sub_Spec {α : Type _} [Ring α] : MaxSpec α ⊆ Spec α :=
      fun I => Ideal.maximal_is_prime
  end Ring
end M4R