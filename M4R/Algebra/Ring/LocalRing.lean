import M4R.Algebra.Ring.Noetherian

namespace M4R
  open Semiring localisation Ideal QuotientRing

  class LocalRing (α : Type _) extends Ring α where
    loc : ∃ m : Ideal α, Ring.MaxSpec α = Set.singleton m

  namespace LocalRing
    open Classical

    variable {α : Type _} [LocalRing α]

    noncomputable def m : Ideal α := choose LocalRing.loc
    theorem m_maxspec : Ring.MaxSpec α = Set.singleton m := choose_spec LocalRing.loc
    theorem m_max : (m : Ideal α).is_maximal := (m_maxspec ▸ rfl : m ∈ Ring.MaxSpec α)
    theorem m_proper : (m : Ideal α).proper_ideal := m_max.left

    theorem maximal_is_m {I : Ideal α} (hI : I.is_maximal) : I = m :=
      (m_maxspec ▸ hI : I ∈ Set.singleton m)

    theorem units {a : α} : isUnit a ↔ a ∉ m :=
      ⟨fun h₁ h₂ => absurd (is_unit_ideal'.mpr ⟨a, h₁, h₂⟩) m_proper,
       not_imp_symm fun ha =>
        let ⟨I, haI, hI⟩ := t1_1 (unit_not_principal ha)
        maximal_is_m hI ▸ haI (generator_in_principal a)⟩

    theorem subset_m {I : Ideal α} (hI : I.proper_ideal) : I ⊆ m :=
      fun x hx => byContradiction fun h =>
        absurd (Ideal.is_unit_ideal'.mpr ⟨x, units.mpr h, hx⟩) hI

    theorem nontrivial (α : Type _) [LocalRing α] : Ring.is_NonTrivial α :=
      fun h => units.mp (isUnit_1 : isUnit (1 : α)) (h ▸ m.has_zero)

    def residue_field (α : Type _) [LocalRing α] := QClass (m : Ideal α)

    theorem localisation_at.is_max [Ring α] {P : Ideal α} (hP : P.is_prime) :
      ∀ I, I.is_maximal ↔ I = localiseₚ hP P :=
        have : ∀ I : Ideal (localisationₚ hP), I ⊈ localiseₚ hP P → I = 1 := fun I hI =>
          let ⟨x, hx₁, hx₂⟩ := NotSubset.exists_def.mp hI
          is_unit_ideal'.mpr ⟨x,
            let ⟨r, s, hs, he⟩ := exists_frac x
            he ▸ is_unit (fun hr => hx₂ (localise_ideal.exists_frac.mpr ⟨r, s, hr, hs, he⟩)) hs, hx₁⟩
        fun I =>
          ⟨fun hI => ((hI.right (of_not_not (mt (this I) hI.left))).resolve_right
            (localise_ideal.proper.mpr (PrimeComp.disjoint hP))).symm,
          fun h => by rw [h]; exact ⟨localise_ideal.proper.mpr (PrimeComp.disjoint hP), fun hJ =>
            or_iff_not_imp_left.mpr fun h => this _ fun h' => h (Ideal.antisymm h' hJ)⟩⟩

    instance localisation_at [Ring α] {P : Ideal α} (hP : P.is_prime) : LocalRing (localisationₚ hP) where
      loc := ⟨localiseₚ hP P, Set.singleton.ext.mpr (localisation_at.is_max hP)⟩

    theorem localisation_at.m_def [Ring α] {P : Ideal α} (hP : P.is_prime) : localiseₚ hP P = m :=
      maximal_is_m ((localisation_at.is_max hP _).mpr rfl)

  end LocalRing

  open LocalRing localisation_at Monoid Group

  class NoetherianLocalRing (α : Type _) extends LocalRing α, NoetherianRing α

  namespace NoetherianLocalRing

    instance localisation_NoetherianLocalRing [NoetherianRing α] {P : Ideal α} (hP : P.is_prime) :
      NoetherianLocalRing (localisationₚ hP) where
        noetherian := NoetherianRing.localiastion_noetherian (PrimeComp hP)

    protected theorem m_finitely_generated (α : Type _) [NoetherianLocalRing α] : (m : Ideal α).finitely_generated :=
      NoetherianRing.ideal_finitely_generated m

    theorem local_krull_principal_ideal_theorem [NoetherianLocalRing α] {a : α} (ha : ¬isUnit a)
      (hP : m.minimal_prime_ideal_of (principal a)) : (m : Ideal α).height_le 1 := by
      /-  • by contradiction : assume height m > 1, i.e. ∃ P Q : Ideal α, both prime, s.t. P ⊊ Q ⊊ m
          • we have Spec (R/aR) = {m(R/aR)} (from 3.28 : primes of R/I ↔ primes of R containing I)
          • we also know R/aR is an Artinian local ring (from 8.45 : artinian (i.e. descending chain conditiion) ↔
            noetherian and all primes maximal)
          • form descending chain in Artinian ring (using symbolic power, which includes pow_nat from semiring structure)
          • Artinian → stable
          • Nakayama's lemma  -/
        let RaR := QClass (principal a)
        have : Ring.Spec RaR = Ring.MaxSpec RaR :=
          Set.subset.antisymm (fun Q hQ => by
            let Q' := contraction (QuotientRing.natural_hom (principal a)) Q
            have h₁ : principal a ⊆ Q' := fun x hx => ((natural_hom.kernel (principal a)).mpr hx ▸
              Q.has_zero : QuotientRing.natural_hom (principal a) x ∈ Q)
            have h₂ : Q'.is_prime := Ideal.contraction_prime _ hQ
            have := quotient_maximal m_max (subset_m (unit_not_principal ha))
            rw [←hP.right.right h₂ h₁ (subset_m h₂.left), contraction_extension_eq_of_surjective
              (natural_hom.surjective (principal a)) Q] at this
            exact this) Ring.maxspec_sub_spec
        sorry

  end NoetherianLocalRing

  namespace NoetherianRing

    theorem krull_principal_ideal_theorem [NoetherianRing α] {a : α} (ha : ¬isUnit a)
      {P : Ideal α} (hP : P.minimal_prime_ideal_of (principal a)) : P.height_le 1 :=
        have : m.minimal_prime_ideal_of (principal (natural_homₚ hP.left a)) :=
          localise_ideal.principal _ a ▸ m_def hP.left ▸ minimal_prime_localisation
            hP (PrimeComp.disjoint hP.left)
        have := NoetherianLocalRing.local_krull_principal_ideal_theorem (fun h =>
          absurd (unit_ideal_in (unit_principal h ▸ this.right.left :
            (1 : Ideal (localisationₚ hP.left)) ⊆ m)) m_proper) this
        local_height_le hP.left (PrimeComp.disjoint hP.left) 1
          (m_def hP.left ▸ this : height_le (localiseₚ hP.left P) 1)

  end NoetherianRing

  namespace NoetherianLocalRing

    protected theorem has_krull_dim (α : Type _) [NoetherianLocalRing α] : Ring.krull_dim.has_krull_dim α := by
      sorry

  end NoetherianLocalRing

  class RegularLocalRing (α : Type _) extends NoetherianLocalRing α where
    regular : (NoetherianLocalRing.m_finitely_generated α).minimal_generator_count =
                Ring.krull_dim.dim (NoetherianLocalRing.has_krull_dim α)

end M4R
