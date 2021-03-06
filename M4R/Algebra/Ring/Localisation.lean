import M4R.Algebra.Ring.Radical
import M4R.Algebra.Ring.Field

namespace M4R
  open NCRing Semiring NCSemiring Group CommMonoid Monoid

  structure MultiplicativeSet (α : Type _) [Ring α] where
    subset     : Set α
    has_one    : 1 ∈ subset
    mul_closed : ∀ {a b : α}, a ∈ subset → b ∈ subset → a * b ∈ subset
  instance MultiplicativeSet.MultiplicativeSetMem [Ring α]: Mem α (MultiplicativeSet α) where mem := fun x S => x ∈ S.subset

  theorem MultiplicativeSet.disjoint_ideal_proper [Ring α] {S : MultiplicativeSet α}
    {I : Ideal α} (hIS : Set.disjoint I.subset S.subset) : I.proper_ideal := fun h =>
      absurd (Ideal.is_unit_ideal.mp h) (Set.disjoint.elementwise.mp (hIS.comm) 1 S.has_one)

  theorem MultiplicativeSet.pow_closed [Ring α] (S : MultiplicativeSet α) {a : α} (ha : a ∈ S) (n : Nat) :
    a ^ n ∈ S := by
      induction n with
      | zero => exact S.has_one
      | succ n ih => exact pow_nat_succ a n ▸ S.mul_closed ih ha

  def PrimeComp [Ring α] {P : Ideal α} (hP : P.is_prime) : MultiplicativeSet α where
    subset     := P.subsetᶜ
    has_one    := Ideal.proper_iff_1_notin.mp hP.left
    mul_closed := fun h₁ h₂ h₃ => Or.elim (hP.right _ _ h₃) h₁ h₂

  theorem PrimeComp.disjoint [Ring α] {P : Ideal α} (hP : P.is_prime) : Set.disjoint P.subset (PrimeComp hP).subset :=
    Set.disjoint.elementwise.mpr fun _ => iff_not_not.mpr

  theorem PrimeComp.disjoint_subset [Ring α] {P : Ideal α} (hP : P.is_prime) {I : Ideal α} (hIP : I ⊆ P) : Set.disjoint I.subset (PrimeComp hP).subset :=
    Set.ext.mp fun x => ⟨fun hx => absurd (hIP hx.left) hx.right, fun _ => by contradiction⟩

  def frac [Ring α] (S : MultiplicativeSet α) := α × ↑S.subset

  namespace frac
    variable [Ring α] {S : MultiplicativeSet α} (f : frac S)

    protected abbrev mk (r : α) ⦃s : α⦄ (hs : s ∈ S) : frac S := (r, ⟨s, hs⟩)

    abbrev num : α := f.fst
    abbrev denom : α := f.snd.val
    abbrev num_eq (r : α) {s : α} (hs : s ∈ S) : (frac.mk r hs).num = r := rfl
    abbrev denom_eq (r : α) {s : α} (hs : s ∈ S) : (frac.mk r hs).denom = s := rfl
    theorem denom_in_S : denom f ∈ S := f.snd.property

    theorem ext : ∀ {x y : frac S},  x = y ↔ x.num = y.num ∧ x.denom = y.denom
    | (x₁, x₂), (y₁, y₂) =>
      ⟨fun h => have ⟨h₁, h₂⟩ := Prod.mk.inj h; ⟨h₁, congrArg Subtype.val h₂⟩,
       fun ⟨h₁, h₂⟩ => Prod.mk.injEq x₁ x₂ y₁ y₂ ▸ ⟨h₁, Set.elementExt h₂⟩⟩

    protected def r (x y : frac S) : Prop := ∃ s ∈ S, s * x.num * y.denom = s * y.num * x.denom

    protected instance setoid (S : MultiplicativeSet α) : Setoid (frac S) where
      r     := frac.r
      iseqv := {
        refl  := fun _ => ⟨1, S.has_one, rfl⟩
        symm  := fun ⟨s, hs, h⟩ => ⟨s, hs, h.symm⟩
        trans := by
          intro x y z ⟨s₁, hs₁, h₁⟩ ⟨s₂, hs₂, h₂⟩
          exact ⟨s₁ * s₂ * y.denom, S.mul_closed (S.mul_closed hs₁ hs₂) y.denom_in_S, by
            rw [mul_right_comm s₁, mul_right_comm _ s₂, mul_right_comm s₁, h₁]
            conv => rhs rw [mul_right_comm s₁, mul_right_comm _ y.denom, mul_assoc _ z.num,
              mul_assoc s₁, ←mul_assoc s₂, ←h₂, mul_right_comm s₂, ←mul_assoc, mul_right_comm s₁,
              mul_right_comm _ _ x.denom, ←mul_assoc]⟩
      }

  end frac

  def localisation [Ring α] (S : MultiplicativeSet α) := Quotient (frac.setoid S)

  namespace localisation
    variable [Ring α] {S : MultiplicativeSet α}

    def of_frac : frac S → localisation S := Quotient.mk

    abbrev of_frac' (r : α) {s : α} (hs : s ∈ S) : localisation S :=
      of_frac (frac.mk r hs)

    theorem equiv {x y : frac S} : of_frac x = of_frac y ↔
      ∃ s ∈ S, s * x.num * y.denom = s * y.num * x.denom :=
        ⟨Quotient.exact, @Quotient.sound (frac S) (frac.setoid S) x y⟩

    theorem equiv' {r₁ r₂ s₁ s₂ : α} {hs₁ : s₁ ∈ S} {hs₂ : s₂ ∈ S} :
      of_frac' r₁ hs₁ = of_frac' r₂ hs₂ ↔ ∃ s ∈ S, s * r₁ * s₂ = s * r₂ * s₁ := equiv

    protected instance zero_inst : Zero (localisation S) where zero := of_frac' 0 S.has_one
    protected theorem zero_def : (0 : localisation S) = of_frac' 0 S.has_one := rfl
    protected instance one_inst : One (localisation S) where one := of_frac' 1 S.has_one
    protected theorem one_def : (1 : localisation S) = of_frac' 1 S.has_one := rfl

    protected def add : localisation S → localisation S → localisation S :=
      Function.Quotient.map₂ _ _ _ (frac.setoid S).refl (frac.setoid S).refl
        (fun x y => frac.mk (x.num * y.denom + y.num * x.denom) (S.mul_closed x.denom_in_S y.denom_in_S))
        fun a₁ a₂ b₁ b₂ ⟨sa, hsaS, hsae⟩ ⟨sb, hsbS, hsbe⟩ =>
          ⟨sa * sb, S.mul_closed hsaS hsbS, (by
            simp only [mul_distrib_left, mul_distrib_right, ←mul_assoc]
            rw [mul_right_comm sa, mul_right_comm _ _ a₂.denom, mul_right_comm _ _ a₂.denom, hsae,
              mul_right_comm, mul_right_comm _ a₁.denom, mul_right_comm _ a₁.denom, mul_right_comm sa]
            conv => lhs rhs rw [mul_right_comm, mul_right_comm _ _ b₂.denom, mul_assoc sa, mul_assoc sa, hsbe,
              ←mul_assoc, ←mul_assoc, mul_right_comm, mul_right_comm _ b₁.denom, mul_right_comm _ b₁.denom] :
            sa * sb * (a₁.num * b₁.denom + b₁.num * a₁.denom) * (a₂.denom * b₂.denom)
              = sa * sb * (a₂.num * b₂.denom + b₂.num * a₂.denom) * (a₁.denom * b₁.denom))⟩
    protected instance add_inst : Add (localisation S) where add := localisation.add

    protected def neg : localisation S → localisation S :=
      Function.Quotient.map _ _ (fun f => frac.mk (-f.num) f.denom_in_S)
        fun a₁ a₂ ⟨s, hsS, hse⟩ => ⟨s, hsS, (by simp only [mul_neg, neg_mul, hse] :
          s * -a₁.num * a₂.denom = s * -a₂.num * a₁.denom)⟩
    protected instance neg_inst : Neg (localisation S) where neg := localisation.neg

    protected def mul : localisation S → localisation S → localisation S :=
      Function.Quotient.map₂ _ _ _ (frac.setoid S).refl (frac.setoid S).refl
        (fun x y => frac.mk (x.num * y.num) (S.mul_closed x.denom_in_S y.denom_in_S))
        fun a₁ a₂ b₁ b₂ ⟨sa, hsaS, hsae⟩ ⟨sb, hsbS, hsbe⟩ =>
          ⟨sa * sb, S.mul_closed hsaS hsbS, (by
            simp only [←mul_assoc]; rw [mul_right_comm _ _ a₂.denom, mul_right_comm sa,
              mul_right_comm _ sb, hsae, mul_assoc, mul_assoc, ←mul_assoc sb, hsbe,
              ←mul_assoc, ←mul_assoc, mul_right_comm _ _ sb, mul_right_comm sa, mul_right_comm _ a₁.denom] :
              sa * sb * (frac.num a₁ * frac.num b₁) * (frac.denom a₂ * frac.denom b₂) =
                sa * sb * (frac.num a₂ * frac.num b₂) * (frac.denom a₁ * frac.denom b₁))⟩
    protected instance mul_inst : Mul (localisation S) where mul := localisation.mul

    protected instance ring (S : MultiplicativeSet α) : Ring (localisation S) := Ring.construct {
      add_zero := Quot.ind fun _ => Quot.sound ⟨1, S.has_one, by
        simp only [frac.denom_eq, mul_one, zero_mul, add_zero]⟩
      add_assoc := Function.Quotient.ind₃ _ _ _ fun x y z => Quot.sound ⟨1, S.has_one, by
        simp only [one_mul, mul_distrib_left, mul_distrib_right, ←mul_assoc, ←add_assoc]
        conv => rhs rw [mul_right_comm y.num, mul_right_comm z.num]⟩
      add_neg := Quot.ind fun _ => Quot.sound ⟨1, S.has_one, by
        simp only [one_mul, mul_one, zero_mul, ←mul_distrib_right, Group.add_neg]⟩
      add_comm := Quotient.ind₂ fun x y => Quot.sound ⟨1, S.has_one, by
        simp only [frac.num_eq, frac.denom_eq]; rw [add_comm, mul_comm y.denom]⟩
      mul_one := Quot.ind fun _ => Quot.sound ⟨1, S.has_one, by
        simp only [frac.denom_eq, mul_one]⟩
      mul_assoc := Function.Quotient.ind₃ _ _ _ fun _ _ _ => Quot.sound ⟨1, S.has_one, by
        simp only [←mul_assoc]⟩
      mul_distrib_left := Function.Quotient.ind₃ _ _ _ fun x y z => Quot.sound ⟨1, S.has_one, by
        simp only [frac.num_eq, frac.denom_eq, one_mul]; rw [mul_distrib_left]
        conv => rhs rw [mul_comm x.denom, mul_comm x.denom, mul_left_comm x.denom,
          ←mul_assoc _ _ x.denom, ←mul_assoc _ _ x.denom, ←mul_distrib_right]
        simp only [←mul_assoc]⟩
      mul_comm := Quotient.ind₂ fun x y => Quot.sound ⟨1, S.has_one, by
        simp only [frac.num_eq, frac.denom_eq]; rw [mul_comm y.num, mul_comm y.denom]⟩
    }

    protected theorem trivial : (1 : localisation S) = (0 : localisation S) ↔ 0 ∈ S :=
      ⟨fun h => by
        rw [localisation.one_def, localisation.zero_def] at h
        let ⟨s, hs, he⟩ := equiv.mp h
        simp only [mul_one, mul_zero] at he
        exact he ▸ hs,
      fun h => by
        rw [localisation.one_def, localisation.zero_def]
        exact equiv.mpr ⟨0, h, by simp only [zero_mul]⟩⟩

    protected theorem nontrivial : (localisation.ring S).is_NonTrivial ↔ 0 ∉ S :=
      not_iff_not.mpr localisation.trivial

    def natural_hom (S : MultiplicativeSet α) : α →ᵣ₁ localisation S where
      hom           := (of_frac' · S.has_one)
      preserve_zero := rfl
      preserve_add  := fun _ _ => equiv.mpr ⟨1, S.has_one, by simp only [frac.denom_eq, mul_one]⟩
      preserve_one  := rfl
      preserve_mul  := fun _ _ => equiv.mpr ⟨1, S.has_one, by simp only [frac.denom_eq, mul_one]⟩
      preserve_neg  := fun _ => rfl

    theorem natural_hom_def (S : MultiplicativeSet α) (r : α) : natural_hom S r = of_frac' r S.has_one := rfl

    theorem natural_hom_factor (r : α) {s : α} (hs : s ∈ S) :
      of_frac' r hs = of_frac' 1 hs * natural_hom S r :=
        equiv'.mpr ⟨1, S.has_one, by simp only [one_mul, mul_one]⟩

    noncomputable def localise_ideal (S : MultiplicativeSet α) : Ideal α → Ideal (localisation S) :=
      Ideal.extension (natural_hom S)

    def delocalise_ideal (S : MultiplicativeSet α) : Ideal (localisation S) → Ideal α :=
      Ideal.contractionᵣ₁ (natural_hom S)

    theorem localise_ideal.contains_mul {I : Ideal α} {r s : α} (hr : r ∈ I) (hs : s ∈ S) :
      of_frac' r hs ∈ localise_ideal S I :=
        natural_hom_factor r hs ▸ Ideal.from_set.contains_mem_mul _ ⟨r, hr, rfl⟩

    theorem exists_frac (x : localisation S) : ∃ (r s : α) (hs : s ∈ S), x = of_frac' r hs :=
      @Quot.ind _ _ (fun x : localisation S => ∃ (r s : α) (hs : s ∈ S), x = of_frac' r hs)
        (fun f => ⟨f.num, f.denom, f.denom_in_S, equiv.mpr ⟨1, S.has_one, rfl⟩⟩) x

    protected theorem localise_ideal.exists_frac {I : Ideal α} {x : localisation S} :
      x ∈ localise_ideal S I ↔ ∃ (r s : α) (hr : r ∈ I) (hs : s ∈ S), x = of_frac' r hs := ⟨fun hx =>
        Ideal.from_set.induction (fun x => ∃ (r s : α) (hr : r ∈ I) (hs : s ∈ S), x = of_frac' r hs) hx
          ⟨0, 1, I.has_zero, S.has_one, rfl⟩
          (fun x ⟨y, hy, he⟩ => ⟨y, 1, hy, S.has_one, he.symm⟩)
          (fun x y ⟨rx, sx, hrx, hsx, hex⟩ ⟨ry, sy, hry, hsy, hey⟩ => ⟨rx * sy + ry * sx, sx * sy,
            I.add_closed (I.mul_closed' hrx sy) (I.mul_closed' hry sx), S.mul_closed hsx hsy,
            by rw [hex, hey]; rfl⟩)
          (fun x y ⟨r, s, hr, hs, he⟩ =>
            @Quot.ind _ _ (fun x : localisation S => ∃ (r s : α) (hr : r ∈ I) (hs : s ∈ S), x * y = of_frac' r hs)
              (fun f => ⟨f.num * r, f.denom * s, I.mul_closed f.num hr, S.mul_closed f.denom_in_S hs, he ▸ rfl⟩) x),
        fun ⟨r, s, hr, hs, he⟩ => he ▸ localise_ideal.contains_mul hr hs⟩

    theorem is_unit {r s : α} (hr : r ∈ S) (hs : s ∈ S) :
      isUnit (of_frac' r hs) :=
        ⟨of_frac' s hr, equiv.mpr ⟨1, S.has_one, by simp only [mul_one, one_mul]; exact mul_comm r s⟩⟩

    theorem localise_ideal.proper {I : Ideal α} :
      (localise_ideal S I).proper_ideal ↔ Set.disjoint I.subset S.subset :=
        not_iff_not.mp ⟨fun h => by
          apply Set.disjoint.not_disjoint_iff_nonempty.mpr
          let ⟨r, s, hr, hs, he⟩ := localise_ideal.exists_frac.mp (Ideal.is_unit_ideal.mp (of_not_not h))
          rw [localisation.one_def] at he
          let ⟨t, ht, he⟩ := equiv.mp he
          simp only [mul_one] at he
          exact ⟨t * r, I.mul_closed t hr, he ▸ S.mul_closed ht hs⟩,
        fun h =>
          let ⟨s, hsI, hsS⟩ := Set.disjoint.not_disjoint_iff_nonempty.mp h
          iff_not_not.mpr (Ideal.is_unit_ideal'.mpr ⟨of_frac' s hsS, is_unit hsS hsS,
            localise_ideal.contains_mul hsI hsS⟩)⟩

    theorem localise_ideal.primary_numerator {Q : Ideal α} (hQ : Q.is_primary) (hQS : Set.disjoint Q.subset S.subset)
      {r s : α} {hs : s ∈ S} : of_frac' r hs ∈ localise_ideal S Q ↔ r ∈ Q := ⟨fun h => by
        let ⟨r', s', hr', hs', he⟩ := localise_ideal.exists_frac.mp h
        let ⟨t, ht, he⟩ := equiv.mp he
        rw [mul_right_comm] at he
        exact (hQ.right r (t * s') (by rw [mul_comm, he, mul_right_comm]; exact Q.mul_closed _ hr')).resolve_right
          (fun ⟨n, hn, h⟩ => Set.disjoint.elementwise.mp hQS _ h (S.pow_closed (S.mul_closed ht hs') n)),
        fun hr => localise_ideal.exists_frac.mpr ⟨r, s, hr, hs, rfl⟩⟩

    theorem localise_ideal.primary_loc_deloc {Q : Ideal α} (hQ : Q.is_primary) (hQS : Set.disjoint Q.subset S.subset) :
      delocalise_ideal S (localise_ideal S Q) = Q :=
        Ideal.antisymm (fun a ha => (localise_ideal.primary_numerator hQ hQS).mp ha) (Ideal.extension_contraction _ Q)

    theorem localise_ideal.prime_numerator {P : Ideal α} (hP : P.is_prime) (hPS : Set.disjoint P.subset S.subset)
      {r s : α} {hs : s ∈ S} : of_frac' r hs ∈ localise_ideal S P ↔ r ∈ P := primary_numerator (Ideal.is_primary_of_prime hP) hPS

    theorem localise_ideal.prime_loc_deloc {P : Ideal α} (hP : P.is_prime) (hPS : Set.disjoint P.subset S.subset) :
      delocalise_ideal S (localise_ideal S P) = P := primary_loc_deloc (Ideal.is_primary_of_prime hP) hPS

    theorem localise_ideal.prime {P : Ideal α} (hP : P.is_prime) (hPS : Set.disjoint P.subset S.subset) :
      (localise_ideal S P).is_prime := ⟨localise_ideal.proper.mpr hPS,
        fun x y hxy => by
          let ⟨rx, sx, hsx, hex⟩ := exists_frac x
          let ⟨ry, sy, hsy, hey⟩ := exists_frac y
          have : x * y = of_frac' (rx * ry) (S.mul_closed hsx hsy) := by rw [hex, hey]; rfl
          rw [this] at hxy
          exact Or.imp (hex ▸ (localise_ideal.prime_numerator hP hPS).mpr)
            (hey ▸ (localise_ideal.prime_numerator hP hPS).mpr)
            (hP.right rx ry ((localise_ideal.prime_numerator hP hPS).mp hxy))⟩

    theorem delocalise_ideal.prime {P : Ideal (localisation S)} (hP : P.is_prime) :
      (delocalise_ideal S P).is_prime := Ideal.contraction_prime _ hP

    theorem delocalise_ideal.deloc_loc (I : Ideal (localisation S)) :
      localise_ideal S (delocalise_ideal S I) = I :=
        Ideal.antisymm (Ideal.contraction_extension _ I)
          fun x hx =>
            let ⟨r, s, hs, he⟩ := exists_frac x
            have : r ∈ delocalise_ideal S I :=
              have : natural_hom S r = of_frac' s S.has_one * of_frac' r hs :=
                equiv'.mpr ⟨1, S.has_one, by simp only [one_mul, mul_one]; exact mul_comm r s⟩
              (this ▸ I.mul_closed _ (he ▸ hx) : _ ∈ I)
            he ▸ localise_ideal.contains_mul this hs

    theorem localise_ideal.principal (S : MultiplicativeSet α) (a : α) :
      localise_ideal S (Ideal.principal a) = Ideal.principal (natural_hom S a) :=
        Ideal.extension_principal (natural_hom S).toRMulMap a

    abbrev localisationₚ [Ring α] {P : Ideal α} (hP : P.is_prime) := localisation (PrimeComp hP)

    noncomputable def localiseₚ [Ring α] {P : Ideal α} (hP : P.is_prime) (I : Ideal α) :
      Ideal (localisationₚ hP) := localise_ideal (PrimeComp hP) I

    def delocaliseₚ [Ring α] {P : Ideal α} (hP : P.is_prime) (I : Ideal (localisationₚ hP)) :
      Ideal α := delocalise_ideal (PrimeComp hP) I

    abbrev natural_homₚ [Ring α] {P : Ideal α} (hP : P.is_prime) : α →ᵣ₁ localisationₚ hP := natural_hom (PrimeComp hP)

    theorem localisationₚ.is_max [Ring α] {P : Ideal α} (hP : P.is_prime) :
      ∀ I, I.is_maximal ↔ I = localiseₚ hP P :=
        have : ∀ I : Ideal (localisationₚ hP), I ⊈ localiseₚ hP P → I = 1 := fun I hI =>
          let ⟨x, hx₁, hx₂⟩ := NotSubset.exists_def.mp hI
          Ideal.is_unit_ideal'.mpr ⟨x,
            let ⟨r, s, hs, he⟩ := exists_frac x
            he ▸ is_unit (fun hr => hx₂ (localise_ideal.exists_frac.mpr ⟨r, s, hr, hs, he⟩)) hs, hx₁⟩
        fun I =>
          ⟨fun hI => ((hI.right (of_not_not (mt (this I) hI.left))).resolve_right
            (localise_ideal.proper.mpr (PrimeComp.disjoint hP))).symm,
          fun h => by rw [h]; exact ⟨localise_ideal.proper.mpr (PrimeComp.disjoint hP), fun hJ =>
            or_iff_not_imp_left.mpr fun h => this _ fun h' => h (Ideal.antisymm h' hJ)⟩⟩

    theorem localisationₚ.maximal [Ring α] {P : Ideal α} (hP : P.is_prime) : (localiseₚ hP P).is_maximal :=
      (localisationₚ.is_max hP _).mpr rfl

    theorem localisationₚ.prime [Ring α] {P : Ideal α} (hP : P.is_prime) : (localiseₚ hP P).is_prime :=
      Ideal.maximal_is_prime (maximal hP)

    noncomputable def symbolic_power [Ring α] {P : Ideal α} (hP : P.is_prime) (n : Nat) : Ideal α :=
      delocaliseₚ hP (localiseₚ hP (P ^ n))

    namespace symbolic_power
      theorem zero_eq_unit [Ring α] {P : Ideal α} (hP : P.is_prime) : symbolic_power hP 0 = 1 :=
        Ideal.antisymm (Ideal.in_unit_ideal _) (fun x hx => Ideal.from_set.contains_mem ⟨x, hx, rfl⟩)

      theorem primary [Ring α] {P : Ideal α} (hP : P.is_prime) {n : Nat} (hn : n ≠ 0) : (symbolic_power hP n).is_primary := by
        have h₁ : localiseₚ hP (P ^ n) = localiseₚ hP P ^ n := Ideal.extension_pow (natural_hom (PrimeComp hP)).toRMulMap P hn
        have h₂ : ((localiseₚ hP P) ^ n).is_primary := Ideal.is_primary_of_radical_maximal (by
          rw [Ideal.radical_pow_of_prime (Ideal.maximal_is_prime (localisationₚ.maximal hP)) n hn]; exact localisationₚ.maximal hP)
        simp only [symbolic_power, h₁]; exact Ideal.contraction_is_primary _ h₂

      theorem proper [Ring α] {P : Ideal α} (hP : P.is_prime) {n : Nat} (hn : n ≠ 0) : (symbolic_power hP n).proper_ideal :=
        (primary hP hn).left

      theorem rad_eq [Ring α] {P : Ideal α} (hP : P.is_prime) {n : Nat} (hn : n ≠ 0) : (symbolic_power hP n).radical = P := by
        simp only [symbolic_power]
        have h₁ : localiseₚ hP (P ^ n) = localiseₚ hP P ^ n := Ideal.extension_pow (natural_hom (PrimeComp hP)).toRMulMap P hn
        have h₂ : delocaliseₚ hP (localiseₚ hP P ^ n).radical = (delocaliseₚ hP (localiseₚ hP P ^ n)).radical :=
          Ideal.contraction_radical (natural_hom (PrimeComp hP)) (localiseₚ hP P ^ n)
        have h₃ : (localiseₚ hP P ^ n).radical = localiseₚ hP P := Ideal.radical_pow_of_prime (localisationₚ.prime hP) n hn
        rw [h₁, ←h₂, h₃]; exact localise_ideal.prime_loc_deloc hP (PrimeComp.disjoint hP)

      theorem descending [Ring α] {P : Ideal α} (hP : P.is_prime) (n : Nat) : symbolic_power hP n.succ ⊆ symbolic_power hP n :=
        Ideal.contraction.subset (natural_hom (PrimeComp hP)).preserve_mul_right (Ideal.extension.subset _ (Ideal.product.pow_succ_subset P n))

      theorem subset_base [Ring α] {P : Ideal α} (hP : P.is_prime) {n : Nat} (hn : n ≠ 0) : symbolic_power hP n ⊆ P := by
        have := Ideal.radical.sub_self (symbolic_power hP n); rw [rad_eq hP hn] at this; exact this
    end symbolic_power
  end localisation

end M4R
