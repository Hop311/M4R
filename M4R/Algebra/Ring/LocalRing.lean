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

    theorem not_unit {a : α} : ¬isUnit a ↔ a ∈ m := (iff_not_comm.mp units).symm

    theorem subset_m {I : Ideal α} (hI : I.proper_ideal) : I ⊆ m :=
      fun x hx => byContradiction fun h =>
        absurd (Ideal.is_unit_ideal'.mpr ⟨x, units.mpr h, hx⟩) hI

    theorem nontrivial (α : Type _) [LocalRing α] : Ring.is_NonTrivial α :=
      fun h => units.mp (isUnit_1 : isUnit (1 : α)) (h ▸ m.has_zero)

    def residue_field (α : Type _) [LocalRing α] := QClass (m : Ideal α)

    instance localisation_at [Ring α] {P : Ideal α} (hP : P.is_prime) : LocalRing (localisationₚ hP) where
      loc := ⟨localiseₚ hP P, Set.singleton.ext.mpr (localisation_at.is_max hP)⟩

    theorem localisation_at.m_def [Ring α] {P : Ideal α} (hP : P.is_prime) : localiseₚ hP P = m :=
      maximal_is_m ((localisation_at.is_max hP _).mpr rfl)

    theorem jacobson_radical_eq_m (α : Type _) [LocalRing α] : Ring.jacobson_radical α = m :=
      Ideal.antisymm (Ring.maximal_subset_jacobson m_max)
        fun x hx => Ideal.sIntersection.mem.mpr fun I hI => maximal_is_m hI ▸ hx

    theorem proper_subset_jacobson_radical [LocalRing α] {I : Ideal α} (hI : I.proper_ideal) : I ⊆ Ring.jacobson_radical α :=
      jacobson_radical_eq_m α ▸ subset_m hI

    instance quotient_LocalRing [LocalRing α] {I : Ideal α} (hI : I.proper_ideal) : LocalRing (QClass I) where
      loc := ⟨extension (QuotientRing.natural_hom I).hom m, Set.ext.mp fun x => ⟨fun hx =>
        quotient_contraction_injective ((quotient_extension_contraction (subset_m hI)).symm ▸
          maximal_is_m (quotient_contraction_maximal hx)),
      fun hx => hx ▸ Ideal.quotient_extension_maximal m_max (subset_m hI)⟩⟩

  end LocalRing

  open LocalRing localisation_at Monoid Group NCSemiring CommMonoid

  class NoetherianLocalRing (α : Type _) extends LocalRing α, NoetherianRing α

  namespace NoetherianLocalRing

    instance localisation_NoetherianLocalRing [NoetherianRing α] {P : Ideal α} (hP : P.is_prime) :
      NoetherianLocalRing (localisationₚ hP) where
        noetherian := NoetherianRing.localisation_noetherian (PrimeComp hP)

    protected theorem m_finitely_generated (α : Type _) [NoetherianLocalRing α] : (m : Ideal α).finitely_generated :=
      NoetherianRing.ideal_finitely_generated m

    theorem local_krull_principal_ideal_theorem [NoetherianLocalRing α] {a : α} (ha : ¬isUnit a)
      (hP : m.minimal_prime_ideal_of (principal a)) : (m : Ideal α).height_le 1 :=
        let RaR := QClass (principal a)
        have : Ring.Spec RaR ⊆ Ring.MaxSpec RaR := fun Q hQ => by
          let Q' := contractionᵣ₁ (QuotientRing.natural_hom (principal a)) Q
          have h₁ : principal a ⊆ Q' := fun x hx => (natural_hom.kernel.mpr hx ▸ Q.has_zero :
            QuotientRing.natural_hom (principal a) x ∈ Q)
          have h₂ : Q'.is_prime := Ideal.contraction_prime _ hQ
          have := quotient_extension_maximal m_max (subset_m (unit_not_principal ha))
          rw [←hP.right.right h₂ h₁ (subset_m h₂.left)] at this
          exact contraction_extension_eq_of_surjective (QuotientRing.natural_hom (principal a)).preserve_mul_left
            (natural_hom.surjective (principal a)) Q ▸ this
        have : ∀ Q Q' : Ideal α, Q.is_prime → Q'.is_prime → Q' ⊊ Q → Q ⊊ m → False := fun Q Q' hQ hQ' hQ'Q hQm => by
          have haQ : a ∉ Q := fun h => absurd (hP.right.right hQ (principal_in h) hQm.left) (Ideal.subsetneq.mp hQm).right
          let c : chain RaR := ⟨fun n => extension (QuotientRing.natural_hom (principal a)) (symbolic_power hQ n.succ)⟩
          have hc : c.descending := fun n => extension.subset _ (symbolic_power.descending hQ n.succ)
          let ⟨N, hN⟩ := ArtinianRing.artinian_of_primes_maximal this c hc
          have he := quotient_extension_injective (hN N.succ (Nat.le_succ N))
          have : symbolic_power hQ N.succ = symbolic_power hQ N.succ.succ + principal a * symbolic_power hQ N.succ :=
            Ideal.antisymm (fun x hx =>
              let ⟨i, hi, j, ⟨c, hc⟩, hij⟩ : x ∈ symbolic_power hQ N.succ.succ + principal a := he ▸ add.subset (symbolic_power hQ N.succ) (principal a) hx
              ⟨i, hi, j,
                have : x - i = c * a := mul_comm a c ▸ hc ▸ Group.sub_eq.mpr (add_comm i j ▸ hij.symm)
                have : c * a ∈ symbolic_power hQ N.succ := this ▸ (symbolic_power hQ N.succ).sub_closed hx (symbolic_power.descending hQ N.succ hi)
                have := ((symbolic_power.primary hQ N.succ_ne_zero).right c a this).resolve_right
                  fun ha => absurd (symbolic_power.rad_eq hQ N.succ_ne_zero ▸ ha) haQ
                from_set.contains_mem ⟨a, generator_in_principal a, c, this, hc.symm⟩, hij⟩)
              (add.subset_add (symbolic_power.descending hQ N.succ) (product.subset_right))
          have h₁ : extension (QuotientRing.natural_hom (symbolic_power hQ N.succ.succ)).hom m ⊆ Ring.jacobson_radical _ :=
            @proper_subset_jacobson_radical _ (LocalRing.quotient_LocalRing (symbolic_power.primary hQ (N.succ.succ_ne_zero)).left) _
              (quotient_extension_proper (Subset.trans (symbolic_power.subset_base hQ N.succ.succ_ne_zero) hQm.left) m_proper)
          have h₂ : extension (QuotientRing.natural_hom (symbolic_power hQ N.succ.succ)).hom (symbolic_power hQ N.succ) =
            extension (QuotientRing.natural_hom (symbolic_power hQ N.succ.succ)).hom (m * symbolic_power hQ N.succ) :=
              Ideal.antisymm (by
                conv => lhs rw [this, QuotientRing.natural_hom.extension_add_I];
                exact extension.subset _ (Ideal.product.mul_subset_mul (Ideal.principal_in (not_unit.mp ha)) (Subset.refl _)))
                (extension_mul _ _ _ ▸ product.subset_right)
          rw [extension_mul] at h₂
          have := Ideal.antisymm (quotient_extension_zero.mp (Ring.nakayama (NoetherianRing.ideal_finitely_generated _) h₁ h₂)) (symbolic_power.descending hQ N.succ)
          have h₁ : localiseₚ hQ Q ⊆ Ring.jacobson_radical _ := by
            rw [jacobson_radical_eq_m, localisation_at.m_def]; exact Subset.refl m
          have h₂ : localiseₚ hQ Q ^ N.succ = localiseₚ hQ Q ^ N.succ.succ :=
            ((extension_pow (natural_homₚ hQ).toRMulMap Q N.succ_ne_zero).symm.trans ((extension_contraction_extension
              (natural_homₚ hQ).preserve_mul_left (Q ^ N.succ)).trans ((congrArg (localiseₚ hQ) this).trans (extension_contraction_extension
              (natural_homₚ hQ).preserve_mul_left (Q ^ N.succ.succ)).symm))).trans (extension_pow (natural_homₚ hQ).toRMulMap Q N.succ.succ_ne_zero)
          conv at h₂ => rhs rw [pow_nat_succ, mul_comm]
          have := congrArg Ideal.radical (Ring.nakayama (NoetherianRing.ideal_finitely_generated _) h₁ h₂)
          rw [radical_pow_of_prime (localisation_at.prime hQ) N.succ N.succ_ne_zero, Ring.nil_radical.def] at this
          have : delocaliseₚ hQ (localiseₚ hQ Q) ⊆ delocaliseₚ hQ (localiseₚ hQ Q') := contraction.subset
            (natural_homₚ hQ).preserve_mul_left (this ▸ Ring.nil_radical.eq_prime_intersection (localisationₚ hQ)
            ▸ Ideal.sIntersection.contains (localise_ideal.prime hQ' (PrimeComp.disjoint_subset hQ hQ'Q.left)))
          exact absurd (Ideal.antisymm hQ'Q.left (localise_ideal.prime_loc_deloc hQ (PrimeComp.disjoint_subset hQ (Subset.refl Q))
            ▸ localise_ideal.prime_loc_deloc hQ' (PrimeComp.disjoint_subset hQ hQ'Q.left) ▸ this)) (Ideal.subsetneq.mp hQ'Q).right
        ⟨fun c hc => this (c.tochain 1) (c.tochain 2) (c.hprime 1) (c.hprime 2) (Ideal.subsetneq.mpr ⟨c.hdescend 1, (hc 1).symm⟩)
            (Ideal.subsetneq.mpr (by simp only [←c.hbase]; exact ⟨c.hdescend 0, (hc 0).symm⟩)),
          fun c => Classical.byContradiction fun h =>
            this (c.tochain 1) (c.tochain 2) (c.hprime 1) (c.hprime 2) (Ideal.subsetneq.mpr ⟨c.hdescend 1,
              (c.length_spec.left 1 (Nat.not_le.mp h)).symm⟩) (Ideal.subsetneq.mpr (by simp only [←c.hbase]; exact ⟨c.hdescend 0,
              (c.length_spec.left 0 (Nat.lt_trans Nat.zero_lt_one (Nat.not_le.mp h))).symm⟩)), maximal_is_prime m_max⟩

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
