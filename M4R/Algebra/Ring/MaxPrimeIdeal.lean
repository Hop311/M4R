import M4R.Algebra.Ring.Field
import M4R.Algebra.Ring.Quotient

namespace M4R
  open Group Monoid CommMonoid NCSemiring Ring QuotientRing

  namespace Ideal
    def is_prime [Ring α] (I : Ideal α) : Prop :=
      I.proper_ideal ∧ ∀ r s, r * s ∈ I → r ∈ I ∨ s ∈ I

    def is_maximal [Ring α] (I : Ideal α) : Prop :=
      I.proper_ideal ∧ ∀ {J : Ideal α}, I ⊆ J → J = I ∨ J = 1

    theorem maximal_neq [Ring α] {I : Ideal α} (h : I.is_maximal) : ∀ {J : Ideal α}, I ⊊ J → J = 1 :=
      fun ⟨hIJ, x, hxI, hxJ⟩ => (h.right hIJ).resolve_left fun heq => by rw [heq] at hxJ; exact hxI hxJ

    theorem zero_prime [IntegralDomain α] : (0 : Ideal α).is_prime :=
      ⟨Ideal.proper_iff_notin.mpr ⟨1, (absurd · Ideal.one_notin_zero_ideal)⟩,
        fun _ _ => NCIntegralDomain.integral'⟩
    theorem one_not_prime [Ring α] : ¬(1 : Ideal α).is_prime := fun h => h.left rfl
    theorem one_not_maximal [Ring α] : ¬(1 : Ideal α).is_maximal := fun h => h.left rfl

    def minimal_prime_ideal_of [Ring α] (P I : Ideal α) : Prop :=
      P.is_prime ∧ I ⊆ P ∧ ∀ {J : Ideal α}, J.is_prime → I ⊆ J → J ⊆ P → J = P

    theorem minimal_prime_ideal_of.right_proper [Ring α] {P I : Ideal α} (h : P.minimal_prime_ideal_of I) : I.proper_ideal :=
      Ideal.proper_ideal_subset h.right.left h.left.left

    theorem minimal_prime_of_prime [Ring α] {P : Ideal α} (hP : P.is_prime) : P.minimal_prime_ideal_of P :=
      ⟨hP, Subset.refl P, fun _ h₁ h₂ => (Ideal.antisymm h₂ h₁)⟩

    theorem ProperIdeal_is_NonTrivial [Ring α] {I : Ideal α} (hI : I.proper_ideal) : Ring.is_NonTrivial (QClass I) := by
      intro h10;
      have := @Quotient.exact α (QSetoid I) 0 1 h10.symm;
      simp only [HasEquiv.Equiv, Setoid.r, QRel] at this
      rw [neg_zero, zero_add] at this
      exact hI (Ideal.is_unit_ideal.mpr this)

    instance ProperIdealNonTrivialRing [Ring α] {I : Ideal α} (hI : I.proper_ideal) : NonTrivialRing (QClass I) :=
      (ProperIdeal_is_NonTrivial hI).toNonTrivialRing

    theorem NonTrivialRingProperIdeal [Ring α] {I : Ideal α} (h : Ring.is_NonTrivial (QClass I)) : I.proper_ideal := by
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

    theorem maximal_is_Field [Ring α] {I : Ideal α} (hI : I.is_maximal) : Ring.is_Field (QClass I) :=
      ⟨ProperIdeal_is_NonTrivial hI.left, fun hx => ⟨maximal_inv hI hx,
        Classical.choose_spec (maximal_has_inverses' hI hx)⟩⟩

    noncomputable instance MaximalField [Ring α] {I : Ideal α} (hI : I.is_maximal) : Field (QClass I) :=
      (maximal_is_Field hI).toField

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

    theorem contraction_prime [Ring α] [Ring β] (f : α →ᵣ₁ β) {P : Ideal β} (hP : P.is_prime) :
      (contractionᵣ₁ f P).is_prime :=
        ⟨contraction.proper_of_preserve_one f.preserve_mul_left f.preserve_one hP.left,
          fun r s (h : _ ∈ P) => by rw [f.preserve_mul] at h; exact hP.right _ _ h⟩

    theorem quotient_extension_maximal [Ring α] {I : Ideal α} {P : Ideal α} (hP₁ : P.is_maximal) (hP₂ : I ⊆ P) :
      (extension (QuotientRing.natural_hom I).hom P).is_maximal :=
        ⟨fun h => hP₁.left (by
          have := congrArg (contractionᵣ₁ (QuotientRing.natural_hom I) ·) h
          simp [quotient_extension_contraction hP₂] at this
          exact this ▸ Ideal.is_unit_ideal.mpr trivial),
        by
          intro J hJ
          have : P ⊆ contractionᵣ₁ (QuotientRing.natural_hom I) J :=
            fun x hx => hJ (from_set.contains_mem ⟨x, hx, rfl⟩)
          exact Or.imp (fun h => contraction_extension_eq_of_surjective (natural_hom I).preserve_mul_left
            (natural_hom.surjective I) J ▸ congrArg (extension (QuotientRing.natural_hom I).hom ·) h)
            (fun h => contraction_extension_eq_of_surjective (natural_hom I).preserve_mul_left
              (natural_hom.surjective I) J ▸ extension_unit_of_surjective (natural_hom.surjective I)
              ▸ congrArg (extension (QuotientRing.natural_hom I).hom ·) h) (hP₁.right this)⟩

    theorem quotient_contraction_maximal [Ring α] {I : Ideal α} {M : Ideal (QClass I)} (hM : M.is_maximal) :
      (contractionᵣ₁ (QuotientRing.natural_hom I) M).is_maximal :=
        ⟨contraction.proper_of_preserve_one (QuotientRing.natural_hom I).preserve_mul_left
          (QuotientRing.natural_hom I).preserve_one hM.left,
        fun hJ => by
          have hIJ := Subset.trans (quotient_contraction_contains M) hJ
          rw [←quotient_extension_contraction hIJ] at hJ
          have := contraction.of_subset_of_surjective _ (natural_hom.surjective I) hJ
          exact (hM.right this).imp (fun h => quotient_extension_contraction hIJ ▸
            congrArg (contractionᵣ₁ (natural_hom I)) h) (quotient_extension_unit hIJ)⟩
  end Ideal
  namespace Ring

    def Spec (α : Type _) [Ring α] : Set (Ideal α) := {I | I.is_prime}
    def MaxSpec (α : Type _) [Ring α] : Set (Ideal α) := {I | I.is_maximal}

    theorem maxspec_sub_spec {α : Type _} [Ring α] : MaxSpec α ⊆ Spec α :=
      fun I => Ideal.maximal_is_prime

    theorem ideal_0_or_1 [Ring α] (h : is_Field α) (I : Ideal α) : I = 0 ∨ I = 1 :=
      or_iff_not_imp_right.mpr fun hproper => Ideal.is_zero_ideal.mpr fun x hxI =>
        Classical.byContradiction fun hx0 => hproper (Ideal.is_unit_ideal'.mpr ⟨x, h.right hx0, hxI⟩)
  end Ring
  namespace Field
    variable [Field α]

    theorem ideal_0_or_1 (I : Ideal α) : I = 0 ∨ I = 1 :=
      Ring.ideal_0_or_1 to_is_Field I

    theorem zero_maximal : (0 : Ideal α).is_maximal :=
      ⟨Ideal.proper_iff_notin.mpr ⟨1, Ideal.one_notin_zero_ideal⟩,
        fun _ => ideal_0_or_1 _⟩

    theorem spec_eq_zero : Ring.Spec α = Set.singleton 0 :=
      Set.singleton.ext.mpr fun I => ⟨fun h => Or.elim (ideal_0_or_1 I) id fun h' =>
        absurd (h' ▸ h : (1 : Ideal α).is_prime) Ideal.one_not_prime, (· ▸ Ideal.zero_prime)⟩

    theorem maxspec_eq_zero : Ring.MaxSpec α = Set.singleton 0 :=
      Set.subset.antisymm (spec_eq_zero ▸ Ring.maxspec_sub_spec) fun I => (· ▸ zero_maximal)

  end Field
end M4R
