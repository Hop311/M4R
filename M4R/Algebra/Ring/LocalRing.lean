import M4R.Algebra.Ring.Noetherian

namespace M4R

  class LocalRing (α : Type _) extends NonTrivialRing α where
    loc : ∃ m : Ideal α, Ring.MaxSpec α = Set.singleton m

  namespace LocalRing
    open Classical QuotientRing Semiring

    variable {α : Type _} [LocalRing α]

    noncomputable def m : Ideal α := choose LocalRing.loc
    theorem m_maxspec : Ring.MaxSpec α = Set.singleton m := choose_spec LocalRing.loc
    theorem m_max : (m : Ideal α).is_maximal := (m_maxspec ▸ rfl : m ∈ Ring.MaxSpec α)
    theorem m_proper : (m : Ideal α).proper_ideal := m_max.left

    theorem maximal_is_m {I : Ideal α} (hI : I.is_maximal) : I = m :=
      (m_maxspec ▸ hI : I ∈ Set.singleton m)

    theorem units {a : α} : isUnit a ↔ a ∉ m :=
      ⟨fun h₁ h₂ => absurd (Ideal.is_unit_ideal'.mpr ⟨a, h₁, h₂⟩) m_proper,
       not_imp_symm fun ha =>
        let ⟨I, haI, hI⟩ := t1_1 (Ideal.unit_not_principal ha)
        maximal_is_m hI ▸ haI (Ideal.generator_in_principal a)⟩

    def residue_field (α : Type u) [LocalRing α] := QClass (m : Ideal α)

    open localisation NCSemiring
    instance localisation_at [NonTrivialRing α] {P : Ideal α} (hP : P.is_prime) : LocalRing (localisation (PrimeComplement hP)) where
      loc := ⟨localise_ideal _ P,
        have : ∀ I : Ideal (localisation (PrimeComplement hP)), I ⊈ localise_ideal _ P → I = 1 := fun I hI =>
          let ⟨x, hx₁, hx₂⟩ := NotSubset.exists_def.mp hI
          Ideal.is_unit_ideal'.mpr ⟨x,
            let ⟨r, s, hs, he⟩ := exists_frac x
            he ▸ is_unit (fun hr => hx₂ (localise_ideal.exists_frac.mpr ⟨r, s, hr, hs, he⟩)) hs, hx₁⟩
        Set.singleton.ext.mpr fun I =>
          ⟨fun hI => ((hI.right (of_not_not (mt (this I) hI.left))).resolve_right
            (localise_ideal.proper.mpr (PrimeComplement.disjoint hP))).symm,
          fun h => by rw [h]; exact ⟨localise_ideal.proper.mpr (PrimeComplement.disjoint hP), fun hJ =>
            or_iff_not_imp_left.mpr fun h => this _ fun h' => h (Ideal.antisymm h' hJ)⟩
          ⟩⟩
      toNonTrivial := ⟨localisation.nontrivial.mpr (iff_not_not.mpr P.has_zero)⟩

  end LocalRing

  class NoetherianLocalRing (α : Type _) extends LocalRing α, NoetherianRing α
  namespace NoetherianLocalRing
    open LocalRing

    protected theorem m_finitely_generated (α : Type _) [NoetherianLocalRing α] : (m : Ideal α).finitely_generated :=
      NoetherianRing.ideal_finitely_generated m

    protected theorem has_krull_dim (α : Type _) [NoetherianLocalRing α] : Ring.krull_dim.has_krull_dim α := by
      sorry

  end NoetherianLocalRing 

  class RegularLocalRing (α : Type _) extends NoetherianLocalRing α where
    regular : (NoetherianLocalRing.m_finitely_generated α).minimal_generator_count =
                Ring.krull_dim.dim (NoetherianLocalRing.has_krull_dim α)

end M4R
