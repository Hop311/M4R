import M4R.Algebra.Ring.ChainProperties

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
        let ⟨I, haI, hI⟩ := exists_maximal_containing (unit_not_principal ha)
        maximal_is_m hI ▸ haI (generator_in_principal a)⟩

    theorem not_unit {a : α} : ¬isUnit a ↔ a ∈ m := (iff_not_comm.mp units).symm

    theorem subset_m {I : Ideal α} (hI : I.proper_ideal) : I ⊆ m :=
      fun x hx => byContradiction fun h =>
        absurd (Ideal.is_unit_ideal'.mpr ⟨x, units.mpr h, hx⟩) hI

    theorem nontrivial (α : Type _) [LocalRing α] : Ring.is_NonTrivial α :=
      fun h => units.mp (isUnit_1 : isUnit (1 : α)) (h ▸ m.has_zero)

    def residue_field (α : Type _) [LocalRing α] := QClass (m : Ideal α)

    instance localisation_at [Ring α] {P : Ideal α} (hP : P.is_prime) : LocalRing (localisationₚ hP) where
      loc := ⟨localiseₚ hP P, Set.singleton.ext.mpr (localisationₚ.is_max hP)⟩

    theorem localisation_at.m_def [Ring α] {P : Ideal α} (hP : P.is_prime) : localiseₚ hP P = m :=
      maximal_is_m ((localisationₚ.is_max hP _).mpr rfl)

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

    theorem quotient_LocalRing.m_def [LocalRing α] {I : Ideal α} (hI : I.proper_ideal) :
      extension (QuotientRing.natural_hom I).hom m = @m _ (quotient_LocalRing hI) :=
        @maximal_is_m _ (quotient_LocalRing hI) _ (quotient_extension_maximal m_max (subset_m hI))

  end LocalRing

  open LocalRing localisation_at Monoid Group NCSemiring CommMonoid

  class NoetherianLocalRing (α : Type _) extends LocalRing α, NoetherianRing α

  namespace NoetherianLocalRing

    instance localisation_NoetherianLocalRing [NoetherianRing α] {P : Ideal α} (hP : P.is_prime) :
      NoetherianLocalRing (localisationₚ hP) where
        noetherian := NoetherianRing.localisation_noetherian (PrimeComp hP)

    instance quotient_NotherianLocalRing [NoetherianLocalRing α] {I : Ideal α} (hI : I.proper_ideal) :
      NoetherianLocalRing (QClass I) where
        toLocalRing := quotient_LocalRing hI
        noetherian  := NoetherianRing.quotient_noetherian I

    protected theorem m_finitely_generated (α : Type _) [NoetherianLocalRing α] : (m : Ideal α).finitely_generated :=
      NoetherianRing.ideal_finitely_generated m

    theorem local_krull_principal_ideal_theorem [NoetherianLocalRing α] {a : α}
      (hP : m.minimal_prime_ideal_of (principal a)) : (m : Ideal α).height_le 1 :=
        let RaR := QClass (principal a)
        have : Ring.Spec RaR ⊆ Ring.MaxSpec RaR := fun Q hQ => by
          let Q' := contractionᵣ₁ (QuotientRing.natural_hom (principal a)) Q
          have h₁ : principal a ⊆ Q' := fun x hx => (natural_hom.kernel.mpr hx ▸ Q.has_zero :
            QuotientRing.natural_hom (principal a) x ∈ Q)
          have h₂ : Q'.is_prime := Ideal.contraction_prime _ hQ
          have := quotient_extension_maximal m_max (subset_m hP.right_proper)
          rw [←hP.right.right h₂ h₁ (subset_m h₂.left)] at this
          exact contraction_extension_eq_of_surjective (QuotientRing.natural_hom (principal a)).preserve_mul_right
            (natural_hom.surjective (principal a)) Q ▸ this
        have : ∀ Q Q' : Ideal α, Q.is_prime → Q'.is_prime → Q' ⊊ Q → Q ⊊ m → False := fun Q Q' hQ hQ' hQ'Q hQm => by
          have haQ : a ∉ Q := fun h => absurd (hP.right.right hQ (principal_in h) hQm.left) (Ideal.subsetneq.mp hQm).right
          let c : chain RaR := fun n => extension (QuotientRing.natural_hom (principal a)) (symbolic_power hQ n.succ)
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
                conv => lhs rw [this, QuotientRing.natural_hom.extension_add_I]
                exact extension.subset _ (Ideal.product.mul_subset_mul hP.right.left (Subset.refl _)))
                (extension_mul _ _ _ ▸ product.subset_right)
          rw [extension_mul] at h₂
          have := Ideal.antisymm (quotient_extension_zero.mp (Ring.nakayama (NoetherianRing.ideal_finitely_generated _) h₁ h₂)) (symbolic_power.descending hQ N.succ)
          have h₁ : localiseₚ hQ Q ⊆ Ring.jacobson_radical _ := by
            rw [jacobson_radical_eq_m, localisation_at.m_def]; exact Subset.refl m
          have h₂ : localiseₚ hQ Q ^ N.succ = localiseₚ hQ Q ^ N.succ.succ :=
            ((extension_pow (natural_homₚ hQ).toRMulMap Q N.succ_ne_zero).symm.trans ((extension_contraction_extension
              (natural_homₚ hQ).preserve_mul_right (Q ^ N.succ)).trans ((congrArg (localiseₚ hQ) this).trans (extension_contraction_extension
              (natural_homₚ hQ).preserve_mul_right (Q ^ N.succ.succ)).symm))).trans (extension_pow (natural_homₚ hQ).toRMulMap Q N.succ.succ_ne_zero)
          conv at h₂ => rhs rw [pow_nat_succ, mul_comm]
          have := congrArg Ideal.radical (Ring.nakayama (NoetherianRing.ideal_finitely_generated _) h₁ h₂)
          rw [radical_pow_of_prime (localisationₚ.prime hQ) N.succ N.succ_ne_zero, Ring.nil_radical.def] at this
          have : delocaliseₚ hQ (localiseₚ hQ Q) ⊆ delocaliseₚ hQ (localiseₚ hQ Q') := contraction.subset
            (natural_homₚ hQ).preserve_mul_right (this ▸ Ring.nil_radical.eq_prime_intersection (localisationₚ hQ)
            ▸ Ideal.sIntersection.contains (localise_ideal.prime hQ' (PrimeComp.disjoint_subset hQ hQ'Q.left)))
          exact absurd (Ideal.antisymm hQ'Q.left (localise_ideal.prime_loc_deloc hQ (PrimeComp.disjoint_subset hQ (Subset.refl Q))
            ▸ localise_ideal.prime_loc_deloc hQ' (PrimeComp.disjoint_subset hQ hQ'Q.left) ▸ this)) (Ideal.subsetneq.mp hQ'Q).right
        height_le_of_strict_lt (maximal_is_prime m_max) fun c hc h => Classical.byContradiction fun he =>
          this (c 1) (c 2) (hc.right.right 1) (hc.right.right 2) (Ideal.subsetneq.mpr ⟨hc.right.left 1, Ne.symm he⟩)
            (Ideal.subsetneq.mpr (hc.left ▸ ⟨hc.right.left 0, (h 0 Nat.zero_lt_one).symm⟩))

    theorem local_krull_height_theorem {α : Type u} [NoetherianLocalRing α] (f : Finset α) (hP : m.minimal_prime_ideal_of (from_set f.toSet))
      (ih : ∀ m, m < f.length → ∀ (α : Type u) [NoetherianRing α] (f : Finset α) (hfm : f.length = m) (P : Ideal α),
        P.minimal_prime_ideal_of (from_set f.toSet) → P.height_le f.length) : (m : Ideal α).height_le f.length :=
          (f.length.le_or_lt 0).elim
            (fun hf0 => by
              have hf0 := Nat.le_zero.mp hf0
              rw [Finset.eq_empty_of_length_eq_zero hf0] at hP
              exact hf0 ▸ Ideal.height_le_of_eq (Ideal.height_eq_zero.mpr (from_set.empty ▸ hP)))
            fun hf0 =>
              /-
                • sufficient to show height Q ≤ f.length - 1 for any prime ideal Q such that Q ⊊ m with no prime Q' in between (NOT Q ⊊ Q' ⊊ m)
                • from_set f ⊈ Q as m is minimal prime, so f must contain at least one generator g ∉ Q
                • use artinian_of_primes_maximal on R/(Q + principal g) (primes in R/(Q + gR) correspond to primes P in R s.t.
                  Q + gR ⊊ P (i.e. only m, which is also maximal in the quotient))
                • artinian → nilradical nilpotent, and nilradical = m / (Q + gR) (⋂₀ of primes = {m})
                • (m/(Q + gR)) ^ n = 0 → m ^ n ⊆ Q + gR → all generators in x ∈ f (apart from g) satisfy x ^ n ∈ Q + principal g,
                  i.e. xᵢ ^ n = dᵢ + rᵢg, xᵢ ∈ f ∖ { g }, dᵢ ∈ Q, rᵢ ∈ R
                • any prime ideal containing all the dᵢ's and g must contain all of f, and so must equal m. Thus, letting d = {d₁, ..., dᵢ} (of length f.length-1),
                  we have : M / (from_set d) is a minimal prime ideal of principal (natural_hom (from_set d) g) (or principal g / (from_set d)?).
                • Using krull_principal_ideal_theorem (maybe even local version?) we have height (m / (from_set d)) ≤ 1, and so Q must be a minimal prime of from_set d,
                  otherwise if there exists a prime Q' s.t. from_set d ⊆ Q' ⊊ Q, we would have Q' / (from_set d) ⊊ Q / (from_set d) ⊊ m / (from_set d),
                  violating the height condition.
                • As Q is a minimal prime of from_set d (with d.length + 1 = f.length), ih gives height Q ≤ n - 1
              -/
              have : ∀ Q : Ideal α, Q.is_prime → Q ⊊ m → (∀ Q' : Ideal α, Q'.is_prime → Q ⊆ Q' → Q' ⊊ m → Q' ⊆ Q) → Q.height_le f.length.pred := fun Q hQ hQm hQmax => by
                let ⟨g, hgf, hgQ⟩ : ∃ g : α, g ∈ f ∧ g ∉ Q := Classical.byContradiction fun h =>
                  absurd ((hP.right.right hQ (from_set.ideal_contained fun x hx => of_not_not (not_and.mp
                    (not_exists.mp h x) hx)) hQm.left) ▸ Subset.refl _) (ProperSubset.toNotSubset hQm)
                have hprimes_maximal : Ring.Spec (QClass (Q + principal g)) ⊆ Ring.MaxSpec (QClass (Q + principal g)) := fun Q' hQ' =>
                  have := contraction_prime (QuotientRing.natural_hom (Q + principal g)) hQ'
                  Classical.byContradiction fun h' => absurd (Subset.trans (quotient_contraction_contains Q')
                    (hQmax _ this (Subset.trans (add.subset Q (principal g)) (quotient_contraction_contains Q'))
                    (Ideal.subsetneq.mpr ⟨subset_m this.left, fun h => absurd (quotient_of_contraction_maximal
                    (h ▸ m_max)) h'⟩)) (add.subset' _ _ (generator_in_principal g))) hgQ
                have : Ring.MaxSpec (QClass (Q + principal g)) = Set.singleton (extension (QuotientRing.natural_hom (Q + principal g)).hom m) :=
                  Set.ext.mp fun I => ⟨fun hI => contraction_extension_eq_of_surjective (QuotientRing.natural_hom (Q + principal g)).preserve_mul_right
                    (natural_hom.surjective (Q + principal g)) I ▸ congrArg (extension (QuotientRing.natural_hom (Q + principal g)).hom ·)
                    (maximal_is_m (quotient_contraction_maximal hI)), fun hI => hI ▸ quotient_extension_maximal m_max (add.subset_add hQm.left
                    (principal_in (hP.right.left (from_set.contains_mem hgf))))⟩
                let ⟨n, hn, hnm⟩ := ArtinianRing.nilradical_nilpotent (ArtinianRing.artinian_of_primes_maximal hprimes_maximal)
                rw [Ring.nil_radical.eq_prime_intersection, Set.subset.antisymm hprimes_maximal (fun _ => maximal_is_prime),
                  this, sIntersection.single, ←extension_pow _ _ hn, quotient_extension_zero] at hnm
                have hxQg : ∀ x ∈ f, x ^ n ∈ Q + principal g := fun x hx =>
                  hnm (product.pow_contains n (hP.right.left (from_set.contains_mem hx)))
                let d : Finset α := ((f.erase g).elems.pmap (fun x hx => Classical.choose (hxQg x hx))
                  (fun x hx => (Finset.mem_erase.mp hx).right)).to_finset
                have hdQ : from_set d.toSet ⊆ Q := from_set.ideal_contained fun x hx =>
                  let ⟨a, ha, hx⟩ := UnorderedList.mem_pmap.mp (UnorderedList.mem_to_finset.mp hx)
                  hx ▸ (Classical.choose_spec (hxQg a (Finset.mem_erase.mp ha).right)).left
                have hdproper := proper_ideal_subset hdQ hQ.left
                have : (extension (QuotientRing.natural_hom (from_set d.toSet)).hom m).minimal_prime_ideal_of
                  (principal (QuotientRing.natural_hom (from_set d.toSet) g)) :=
                    ⟨quotient_extension_prime (maximal_is_prime m_max) (Subset.trans hdQ hQm.left),
                    from_set.contains_principal ⟨g, hP.right.left (from_set.contains_mem hgf), rfl⟩,
                    by
                      intro J hJ hgJ hJm
                      have : f.toSet ⊆ (contractionᵣ₁ (QuotientRing.natural_hom (from_set d.toSet)) J).subset := fun x hxf => by
                        byCases hxg : x = g
                        { rw [←extension_principal] at hgJ
                          apply contraction.subset (QuotientRing.natural_hom (from_set d.toSet)).preserve_mul_right hgJ;
                          rw [←natural_hom.extension_add_I, hxg]
                          exact extension_contraction _ _ (add.subset' (from_set d.toSet) (principal g) (generator_in_principal g)) }
                        { have := Classical.choose_spec (Classical.choose_spec (hxQg x hxf)).right;
                          exact prime_radical (contraction_prime (QuotientRing.natural_hom (from_set d.toSet)) hJ) x n hn
                            (this.right ▸ (contractionᵣ₁ (QuotientRing.natural_hom (from_set d.toSet)) J).add_closed
                              (quotient_contraction_contains J (from_set.contains_mem (UnorderedList.mem_to_finset.mpr
                              (UnorderedList.mem_pmap.mpr ⟨x, Finset.mem_erase.mpr ⟨hxg, hxf⟩, rfl⟩))))
                            (Subset.trans (extension_principal _ g ▸ extension_contraction _ _) (contraction.subset (QuotientRing.natural_hom
                              (from_set d.toSet)).preserve_mul_right hgJ) this.left)) }
                      have := hP.right.right (contraction_prime _ hJ) (from_set.ideal_contained this) (quotient_extension_contraction
                        (Subset.trans hdQ hQm.left) ▸ contraction.subset (QuotientRing.natural_hom (from_set d.toSet)).preserve_mul_right hJm)
                      exact contraction_extension_eq_of_surjective _ (natural_hom.surjective _) J ▸
                        congrArg (extension (QuotientRing.natural_hom (from_set d.toSet)).hom ·) this⟩
                rw [quotient_LocalRing.m_def hdproper] at this
                have := @local_krull_principal_ideal_theorem _ (quotient_NotherianLocalRing hdproper) _ this
                have : Q.minimal_prime_ideal_of (from_set d.toSet) := ⟨hQ, hdQ, by
                  intro J hJ hdJ hJQ
                  exact Classical.byContradiction fun hneJQ => absurd this (Ideal.height_gt_one (quotient_extension_prime hJ hdJ)
                    (quotient_extension_prime hQ hdQ) (maximal_is_prime (@m_max _ (quotient_LocalRing hdproper)))
                    (quotient_extension_subsetneq hdJ (Ideal.subsetneq.mpr ⟨hJQ, hneJQ⟩))
                    (quotient_LocalRing.m_def hdproper ▸ quotient_extension_subsetneq hdQ hQm))⟩
                have hdf : d.length < f.length := by
                  apply Nat.lt_of_le_of_lt (UnorderedList.to_finset_length_le _)
                  rw [UnorderedList.pmap_length]
                  conv => rhs rw [f.erase_cons hgf, Finset.length_cons]
                  exact Nat.lt.base _
                exact Q.height_le_trans (Nat.le_of_succ_le_succ (Nat.succ_pred_eq_of_pos hf0 ▸ hdf))
                  (ih d.length hdf α d rfl Q this)
              Nat.succ_pred_eq_of_pos hf0 ▸ height_le_succ (maximal_is_prime m_max) fun Q hQ hQm =>
                let ⟨P, ⟨hP, hPm, hQP⟩, hPmax⟩ := @NoetherianRing.exists_maximal _ _ {P : Ideal α | P.is_prime ∧ P ⊊ m ∧ Q ⊆ P} ⟨Q, hQ, hQm, Subset.refl Q⟩
                have := this P hP hPm (fun Q' hQ' hPQ' hQm' => hPmax Q' ⟨hQ', hQm', Subset.trans hQP hPQ'⟩ hPQ' ▸ Subset.refl _)
                height_le_subset hQ hQP this

  end NoetherianLocalRing

  namespace NoetherianRing

    theorem krull_principal_ideal_theorem [NoetherianRing α] {a : α}
      {P : Ideal α} (hP : P.minimal_prime_ideal_of (principal a)) : P.height_le 1 :=
        have : m.minimal_prime_ideal_of (principal (natural_homₚ hP.left a)) :=
          localise_ideal.principal _ a ▸ m_def hP.left ▸ minimal_prime_localisation
            hP (PrimeComp.disjoint hP.left)
        local_height_le hP.left (PrimeComp.disjoint hP.left) 1 (m_def hP.left ▸
          NoetherianLocalRing.local_krull_principal_ideal_theorem this : height_le (localiseₚ hP.left P) 1)

    theorem krull_height_theorem [NoetherianRing α] {f : Finset α} {P : Ideal α}
      (hP : P.minimal_prime_ideal_of (from_set f.toSet)) : P.height_le f.length :=
        Nat.strong_induction (fun n => ∀ (α : Type _) [NoetherianRing α] (f : Finset α) (hfn : f.length = n) (P : Ideal α),
          P.minimal_prime_ideal_of (from_set f.toSet) → P.height_le f.length)
          (fun n ih α hα f hfn P hP =>
            let f' : Finset (localisationₚ hP.left) := (f.map (natural_homₚ hP.left)).to_finset
            have hf' : f'.length ≤ f.length := f.length_map (natural_homₚ hP.left).hom ▸
              (f.map (natural_homₚ hP.left).hom).to_finset_length_le
            have : m.minimal_prime_ideal_of (from_set f'.toSet) := by
              exact extension_from_finset (natural_homₚ hP.left).preserve_mul_right f ▸ m_def hP.left
                ▸ minimal_prime_localisation hP (PrimeComp.disjoint hP.left)
            have := NoetherianLocalRing.local_krull_height_theorem f' this (fun m hm => ih m (hfn ▸ Nat.lt_of_lt_of_le hm hf'))
            P.height_le_trans hf' (local_height_le hP.left (PrimeComp.disjoint hP.left) f'.length (m_def hP.left ▸ this :
                height_le (localiseₚ hP.left P) f'.length))) f.length α f rfl P hP

  end NoetherianRing

  namespace NoetherianLocalRing

    protected theorem has_krull_dim (α : Type _) [NoetherianLocalRing α] : Ring.krull_dim.has_krull_dim α :=
      let ⟨f, hf⟩ := NoetherianLocalRing.m_finitely_generated α
      Ring.krull_dim.has_krull_dim_of_maximal_height_le ⟨m, m_max⟩ f.length fun M hM =>
        NoetherianRing.krull_height_theorem (maximal_is_m hM ▸ hf ▸ minimal_prime_of_prime (maximal_is_prime m_max))

  end NoetherianLocalRing

  class RegularLocalRing (α : Type _) extends NoetherianLocalRing α where
    regular : (NoetherianLocalRing.m_finitely_generated α).minimal_generator_count =
                Ring.krull_dim.dim (NoetherianLocalRing.has_krull_dim α)

end M4R
