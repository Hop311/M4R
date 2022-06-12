import M4R.Algebra.Ring.Ideal

namespace M4R
  open Monoid CommMonoid Group NCSemiring Semiring

  namespace QuotientRing

    def QRel [Ring α] (I : Ideal α) (a b : α) : Prop := -a + b ∈ I
    theorem QRel.refl [Ring α] (I : Ideal α) (a : α) : QRel I a a := by
      simp only [QRel]; rw [neg_add]; exact I.has_zero
    theorem QRel.symm [Ring α] (I : Ideal α) {a b : α} : QRel I a b → QRel I b a := by
      simp only [QRel]; intro h
      rw [←neg_neg a, ←neg_add_distrib]
      exact I.neg_closed h
    theorem QRel.trans [Ring α] (I : Ideal α) {a b c : α} : QRel I a b → QRel I b c → QRel I a c := by
      simp only [QRel]; intro h₁ h₂
      have := I.add_closed h₁ h₂
      rw [add_assoc, ←add_assoc b, add_neg, zero_add] at this
      exact this

    instance QEquivalence [Ring α] (I : Ideal α) : Equivalence (QRel I) where
      refl  := QRel.refl I
      symm  := QRel.symm I
      trans := QRel.trans I

    instance QSetoid [Ring α] (I : Ideal α) : Setoid α where
      r := QRel I
      iseqv := QEquivalence I

    def QClass [Ring α] (I : Ideal α) : Type _ := Quotient (QSetoid I)

    def toQuotient [Ring α] (I : Ideal α) (a : α) : QClass I := @Quotient.mk α (QSetoid I) a

    theorem toQuotient.def₁ [Ring α] (I : Ideal α) (a : α) : @Quotient.mk α (QSetoid I) a = toQuotient I a := rfl
    theorem toQuotient.def₂ [Ring α] (I : Ideal α) (a : α) : @Quot.mk α (QSetoid I).r a = toQuotient I a := rfl

    theorem QClass.equiv [Ring α] (I : Ideal α) : ∀ a b : α, toQuotient I a = toQuotient I b ↔ -a + b ∈ I := fun a b =>
      ⟨@Quotient.exact α (QSetoid I) a b, @Quotient.sound α (QSetoid I) a b⟩

    def QuotAdd [Ring α] (I : Ideal α) : QClass I → QClass I → QClass I :=
      Function.Quotient.map₂ (QRel I) (QRel I) (QRel I)
        (QRel.refl I) (QRel.refl I) (· + ·) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp only [QRel] at *
          rw [neg_add_distrib, add_comm (-b₁), add_assoc, ←add_assoc (-b₁), add_comm (-b₁), add_assoc, ←add_assoc]
          exact I.add_closed ha hb)

    def QuotNeg [Ring α] (I : Ideal α) : QClass I → QClass I :=
      Function.Quotient.map (QRel I) (QRel I) (- ·)
        (fun x y hxy => by
          simp only [QRel] at *; rw [←neg_add_distrib, add_comm]; exact I.neg_closed hxy)

    def QuotMul [Ring α] (I : Ideal α) : QClass I → QClass I → QClass I :=
      Function.Quotient.map₂ (QRel I) (QRel I) (QRel I)
        (QRel.refl I) (QRel.refl I) (· * ·) (fun a₁ a₂ b₁ b₂ ha hb => by
          simp only [QRel] at *
          have := I.add_closed (I.mul_closed b₁ ha) (I.mul_closed a₂ hb)
          rw [mul_distrib_left, mul_distrib_left, NCRing.mul_neg, mul_comm, mul_comm b₁, add_assoc,
            ←add_assoc (a₂ * b₁), NCRing.mul_neg, add_neg, zero_add] at this; exact this)
  end QuotientRing

  open QuotientRing

  instance QuotientRing {α : Type _} [Ring α] (I : Ideal α) : Ring (QClass I) := Ring.construct
    {
      zero := toQuotient I 0
      one  := toQuotient I 1
      add  := QuotAdd I
      neg  := QuotNeg I
      mul  := QuotMul I
      add_zero := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QRel]
        rw [add_zero, neg_add]; exact I.has_zero
      add_assoc := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QRel]
        rw [add_assoc, neg_add]; exact I.has_zero
      add_neg := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QRel]
        rw [add_neg, neg_add]; exact I.has_zero
      add_comm := by
        apply Function.Quotient.ind₂; intro a _; apply Quot.sound; simp only [QRel]
        rw [add_comm a, neg_add]; exact I.has_zero
      mul_one := by
        apply Quot.ind; intros; apply Quot.sound; simp only [QRel]
        rw [mul_one, neg_add]; exact I.has_zero
      mul_assoc := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QRel]
        rw [mul_assoc, neg_add]; exact I.has_zero
      mul_distrib_left := by
        apply Function.Quotient.ind₃; intros; apply Quot.sound; simp only [QRel]
        rw [mul_distrib_left, neg_add]; exact I.has_zero
      mul_comm := by
        apply Function.Quotient.ind₂; intros; apply Quot.sound; simp only [QRel]
        rw [mul_comm, neg_add]; exact I.has_zero
    }

  namespace QuotientRing

    theorem non_zero [Ring α] {I : Ideal α} {a : α} : toQuotient I a ≠ 0 ↔ a ∉ I :=
      ⟨by intro hI ha; apply hI; apply Quot.sound; simp only [Setoid.r, QRel]; rw [add_zero]; exact I.neg_closed ha,
      by
        intro ha hI; apply ha; have := @Quotient.exact α (QSetoid I) _ _ hI
        simp only [HasEquiv.Equiv, Setoid.r, QRel] at this; rw [add_zero] at this; rw [←neg_neg a]
        exact I.neg_closed this⟩

    theorem is_zero [Ring α] {I : Ideal α} {a : α} : toQuotient I a = 0 ↔ a ∈ I :=
      not_iff_not.mp non_zero

    protected theorem trivial_zero [Ring α] (x : QClass (1 : Ideal α)) : x = 0 :=
      @Quot.ind _ _ (· = (0 : QClass 1)) (fun _ => is_zero.mpr trivial) x

    theorem preserve_pow_nat [Ring α] (I : Ideal α) (a : α) (n : Nat) : (toQuotient I a) ^ n = toQuotient I (a ^ n) := by
      induction n with
      | zero      => rfl
      | succ n ih => rw [pow_nat_succ, pow_nat_succ, ih]; rfl

    def natural_hom [Ring α] (I : Ideal α) : α →ᵣ₁ QClass I where
      hom           := toQuotient I
      preserve_zero := rfl
      preserve_add  := fun _ _ => rfl
      preserve_neg  := fun _ => rfl
      preserve_one  := rfl
      preserve_mul  := fun _ _ => rfl

    theorem natural_hom.def [Ring α] (I : Ideal α) (a : α) : toQuotient I a = natural_hom I a := rfl

    theorem natural_hom.surjective [Ring α] (I : Ideal α) : Function.surjective (natural_hom I).hom :=
      @Quot.ind _ _ (fun x : QClass I => ∃ y, natural_hom I y = x) (fun y => ⟨y, rfl⟩)

    theorem natural_hom.kernel [Ring α] {I : Ideal α} {x : α} : natural_hom I x = 0 ↔ x ∈ I :=
      ⟨fun h => zero_add x ▸ neg_zero ▸ (QClass.equiv I 0 x).mp h.symm,
      fun hx => ((QClass.equiv I 0 x).mpr (neg_zero.symm ▸ (zero_add x).symm ▸ hx)).symm⟩

    open Ideal

    theorem natural_hom.extension_add_I [Ring α] (I J : Ideal α) :
      extension (natural_hom I) (I + J) = extension (natural_hom I).hom J :=
        congrArg from_set (Set.ext.mp fun x => ⟨fun ⟨y, ⟨i, hi, j, hj, hij⟩, hyx⟩ =>
          ⟨j, hj, by rw [←hyx, ←hij, (natural_hom I).preserve_add, natural_hom.kernel.mpr hi, zero_add]⟩,
        fun ⟨y, hy, hyx⟩ => ⟨y, Ideal.add.subset' I J hy, hyx⟩⟩)

    theorem quotient_contraction_contains [Ring α] {I : Ideal α} (J : Ideal (QClass I)) : I ⊆ contractionᵣ₁ (natural_hom I) J :=
      fun x hx => (natural_hom.kernel.mpr hx ▸ J.has_zero : natural_hom I x ∈ J)

    theorem quotient_extension_contraction [Ring α] {I J : Ideal α} (h : I ⊆ J) :
      contractionᵣ₁ (natural_hom I) (extension (natural_hom I) J) = J :=
        Ideal.antisymm (fun x hx =>
          from_set.induction (fun y => ∀ x : α, natural_hom I x = y → x ∈ J) hx
            (fun x hx => h (natural_hom.kernel.mp hx))
            (fun x ⟨z, hz, hzx⟩ y hyx => by
              rw [←zero_add y, ←add_neg z, add_assoc]
              exact J.add_closed hz (h ((QClass.equiv I z y).mp (hyx ▸ hzx : natural_hom I z = natural_hom I y))))
            (fun x y hx hy z hz => by
              let ⟨x', hx'⟩ := natural_hom.surjective I x
              let ⟨y', hy'⟩ := natural_hom.surjective I y
              rw [←hx', ←hy'] at hz
              have := J.add_closed (J.add_closed (hx x' hx') (hy y' hy')) (h ((QClass.equiv I (x' + y') z).mp hz.symm))
              rw [←add_assoc, add_neg, zero_add] at this
              exact this)
            (fun x y hy z hz => by
              let ⟨x', hx'⟩ := natural_hom.surjective I x
              let ⟨y', hy'⟩ := natural_hom.surjective I y
              rw [←hx', ←hy'] at hz
              have := J.add_closed (J.mul_closed x' (hy y' hy')) (h ((QClass.equiv I (x' * y') z).mp hz.symm))
              rw [←add_assoc, add_neg, zero_add] at this
              exact this) x rfl) (extension_contraction _ J)

    theorem quotient_extension_injective [Ring α] {I J K : Ideal α} (h : extension (natural_hom I) J = extension (natural_hom I).hom K) :
      J + I = K + I := by
        have := congrArg (contractionᵣ₁ (natural_hom I)) h
        rw [←natural_hom.extension_add_I I J, quotient_extension_contraction (Ideal.add.subset I J), Ideal.add.comm I J,
          ←natural_hom.extension_add_I I K, quotient_extension_contraction (Ideal.add.subset I K), Ideal.add.comm I K] at this
        exact this

    theorem quotient_extension_subsetneq [Ring α] {I J K : Ideal α} (hIJ : I ⊆ J) (hJK : J ⊊ K) : extension (natural_hom I) J ⊊ extension (natural_hom I).hom K :=
      Ideal.subsetneq.mpr ⟨extension.subset _ hJK.left, fun h => absurd (((add.of_subset hIJ).symm.trans (quotient_extension_injective h)).trans
        (add.of_subset (Subset.trans hIJ hJK.left))) (Ideal.subsetneq.mp hJK).right⟩

    theorem quotient_contraction_injective [Ring α] {I : Ideal α} : Function.injective (contractionᵣ₁ (natural_hom I)) :=
      contraction_injective_of_surjective _ (natural_hom.surjective I)

    theorem quotient_extension_proper [Ring α] {I : Ideal α} {J : Ideal α} (hIJ : I ⊆ J) (hJ : J.proper_ideal) : (extension (natural_hom I).hom J).proper_ideal :=
      fun h => absurd (((add.of_subset hIJ).symm.trans (quotient_extension_injective (extension_unit_of_surjective (natural_hom.surjective I) ▸ h))).trans
        (add.of_subset (in_unit_ideal I))) hJ

    theorem quotient_extension_unit [Ring α] {I : Ideal α} {J : Ideal α} (hIJ : I ⊆ J) (hJ : extension (natural_hom I).hom J = 1) : J = 1 :=
      Classical.byContradiction fun h => absurd hJ (quotient_extension_proper hIJ h)

    theorem quotient_extension_zero [Ring α] {I J : Ideal α} : extension (natural_hom I).hom J = 0 ↔ J ⊆ I :=
      Iff.trans Ideal.extension_zero ⟨fun h x hx => natural_hom.kernel.mp (h hx),
        fun h x hx => natural_hom.kernel.mpr (h hx)⟩

    abbrev quotient_zero.inv_map [Ring α] : QClass (0 : Ideal α) → α :=
      Quot.lift id (fun x y h => by
        have := congrArg (x + ·) h
        simp only [←add_assoc, add_neg, zero_add, add_zero] at this
        exact this.symm)

    theorem quotient_zero_iso (α : Type _) [Ring α] : α ≅ᵣ QClass (0 : Ideal α) where
      toRMulMap       := (natural_hom 0).toRMulMap
      inv             := quotient_zero.inv_map
      left_inv        := fun x => @Quot.ind _ _ (fun y : QClass 0 => ∀ x, y = natural_hom 0 x →
        quotient_zero.inv_map y = x) (fun _ _ h => h ▸ rfl) (natural_hom 0 x) x rfl
      right_inv       := @Quot.ind _ _ (fun x : QClass 0 => natural_hom 0 (quotient_zero.inv_map x) = x)
        (fun _ => rfl)

    abbrev sub_quotient_hom.map [Ring α] {I J : Ideal α} (hIJ : I ⊆ J) : QClass I → QClass J :=
      Quot.lift (natural_hom J) fun x y h => (QClass.equiv J x y).mpr (hIJ h)

    def sub_quotient_hom [Ring α] {I J : Ideal α} (hIJ : I ⊆ J) : QClass I →ᵣ₁ QClass J where
      hom           := sub_quotient_hom.map hIJ
      preserve_zero := rfl
      preserve_add  := @Quotient.ind₂ _ _ (QSetoid I) (QSetoid I) (fun x y : QClass I =>
        sub_quotient_hom.map hIJ (x + y) = sub_quotient_hom.map hIJ x  + sub_quotient_hom.map hIJ y)
        fun _ _ => rfl
      preserve_neg  := Quot.ind fun _ => rfl
      preserve_one  := rfl
      preserve_mul  := @Quotient.ind₂ _ _ (QSetoid I) (QSetoid I) (fun x y : QClass I =>
        sub_quotient_hom.map hIJ (x * y) = sub_quotient_hom.map hIJ x  * sub_quotient_hom.map hIJ y)
        fun _ _ => rfl

    theorem sub_quotient_hom.surjective [Ring α] {I J : Ideal α} (hIJ : I ⊆ J) :
      Function.surjective (sub_quotient_hom hIJ).hom :=
        @Quot.ind _ _ (fun x : QClass J => ∃ y, sub_quotient_hom hIJ y = x)
          fun x => ⟨natural_hom I x, rfl⟩

    theorem sub_quotient_hom.def [Ring α] {I J : Ideal α} (hIJ : I ⊆ J) (x : α) :
      sub_quotient_hom hIJ (natural_hom I x) = natural_hom J x := rfl

    theorem sub_quotient_hom.kernel [Ring α] {I J : Ideal α} (hIJ : I ⊆ J) :
      (sub_quotient_hom hIJ).kernel.subset = (extension (natural_hom I) J).subset :=
        Set.ext.mp fun x =>
          ⟨@Quot.ind _ _ (fun x : QClass I => x ∈ (sub_quotient_hom hIJ).kernel.subset → x ∈ (extension (natural_hom I) J).subset)
            (fun x hx => from_set.contains_mem ⟨x, natural_hom.kernel.mp (sub_quotient_hom.def hIJ _ ▸ hx), rfl⟩) x,
          @Quot.ind _ _ (fun x : QClass I => x ∈ (extension (natural_hom I) J).subset → x ∈ (sub_quotient_hom hIJ).kernel.subset)
            (fun x hx => by
              rw [extension_eq_image_of_surjective_mul_closed (natural_hom I).toRMulMap (natural_hom.surjective I) J] at hx
              let ⟨y, hy₁, hy₂⟩ := hx
              have := J.add_closed hy₁ (hIJ ((QClass.equiv I y x).mp hy₂))
              rw [←add_assoc, add_neg, zero_add] at this
              exact natural_hom.kernel.mpr this) x⟩

    open NCRing
    variable [Ring α] (I : Ideal α) (a : α)

    abbrev ideal_quotient_map.map : QClass (ideal_quotient I a) → QClass I :=
      Quot.lift (fun x => natural_hom I (a * x)) fun x y h =>
        (QClass.equiv I _ _).mpr (mul_neg a x ▸ mul_distrib_left a (-x) y ▸ h)
    theorem ideal_quotient_map.map_def [Ring α] (I : Ideal α) (a x : α) :
      ideal_quotient_map.map I a (natural_hom (ideal_quotient I a) x) = natural_hom I (a * x) := rfl

    def ideal_quotient_map : QClass (ideal_quotient I a) →₋ QClass I where
      hom           := ideal_quotient_map.map I a
      preserve_zero := @Quot.ind _ _ (fun x : QClass (ideal_quotient I a) => x = 0 → ideal_quotient_map.map I a x = 0)
        (fun x hx => natural_hom.kernel.mpr (natural_hom.kernel.mp hx : x ∈ ideal_quotient I a))
        (0 : QClass (ideal_quotient I a)) rfl
      preserve_add  := @Quotient.ind₂ _ _ (QSetoid (ideal_quotient I a)) (QSetoid (ideal_quotient I a))
          (fun x y : QClass (ideal_quotient I a) => ideal_quotient_map.map I a (x + y) =
            ideal_quotient_map.map I a x + ideal_quotient_map.map I a y) (fun _ _ => by
              simp only [toQuotient.def₁, natural_hom.def, ideal_quotient_map.map_def,
                ←(natural_hom I).preserve_add, ←mul_distrib_left]; rfl)
      preserve_neg  := Quot.ind (fun x => by
          simp only [toQuotient.def₂, natural_hom.def, ideal_quotient_map.map_def,
            ←(natural_hom I).preserve_neg, ←mul_neg]; rfl)

    theorem ideal_quotient_map.def [Ring α] (I : Ideal α) (a x : α) :
      ideal_quotient_map I a (natural_hom (ideal_quotient I a) x) = natural_hom I (a * x) := rfl

    theorem ideal_quotient_map.preserve_mul_right : preserve_mul_right (ideal_quotient_map I a).toMHomomorphism :=
      fun x y => @Quotient.ind₂ _ _ (QSetoid (ideal_quotient I a)) (QSetoid (ideal_quotient I a))
        (fun x y : QClass (ideal_quotient I a) => ∃ c : QClass I, ideal_quotient_map I a (x * y) =
        c * ideal_quotient_map I a y) (fun x y => ⟨natural_hom I x, (by rw [mul_left_comm, (natural_hom I).preserve_mul] :
          natural_hom I (a * (x * y)) = natural_hom I x * natural_hom I (a * y))⟩) x y

    theorem ideal_quotient_map.injective : Function.injective (ideal_quotient_map I a).hom :=
      @Quotient.ind₂ _ _ (QSetoid (ideal_quotient I a)) (QSetoid (ideal_quotient I a))
        (fun x y : QClass (ideal_quotient I a) => ideal_quotient_map I a x = ideal_quotient_map I a y → x = y)
        (fun x y h => (QClass.equiv _ _ _).mpr (mul_distrib_left _ _ _ ▸ mul_neg _ _ ▸
          (QClass.equiv _ _ _).mp h : a * (-x + y) ∈ I))

    theorem ideal_quotient_map.extension_eq_image : ∀ J, (extension (ideal_quotient_map I a) J).subset =
      Function.image' (ideal_quotient_map I a).hom J.subset :=
        extension_eq_image_of_left_surjective (ideal_quotient_map I a)
          (@Quotient.ind₂ _ _ (QSetoid I) (QSetoid (ideal_quotient I a)) (fun (x : QClass I)
            (y' : QClass (ideal_quotient I a)) => ∃ x', ideal_quotient_map I a (x' * y') = x * ideal_quotient_map I a y')
            (fun x y' => ⟨natural_hom (ideal_quotient I a) x, by
              simp only [toQuotient.def₁, natural_hom.def, ideal_quotient_map.def]
              rw [←(natural_hom I).preserve_mul, mul_left_comm]; rfl⟩))

    theorem ideal_quotient_map.extension_contraction_eq : ∀ J, contraction (ideal_quotient_map.preserve_mul_right I a)
      (extension (ideal_quotient_map I a).hom J) = J :=
        extension_contraction_eq_of_injective_eq_image (ideal_quotient_map.preserve_mul_right I a)
          (ideal_quotient_map.injective I a) (ideal_quotient_map.extension_eq_image I a)

    theorem ideal_quotient_map.extension_injective : Function.injective (extension (ideal_quotient_map I a).hom) :=
      extension_injective_of_extension_contraction (ideal_quotient_map.preserve_mul_right I a)
        (ideal_quotient_map.extension_contraction_eq I a)

    theorem ideal_quotient_map.image : (ideal_quotient_map I a).image.subset = (principal (natural_hom I a)).subset :=
      Set.ext.mp fun x => ⟨fun ⟨y, hy⟩ => hy ▸ @Quot.ind _ _ (fun y : QClass (ideal_quotient I a) => ideal_quotient_map I a y ∈ principal (natural_hom I a))
        (fun y => ⟨natural_hom I y, by rw [toQuotient.def₂, natural_hom.def, ideal_quotient_map.def, (natural_hom I).preserve_mul]⟩) y,
        fun ⟨y, hy⟩ => hy ▸ @Quot.ind _ _ (fun y : QClass I => natural_hom I a * y ∈ (ideal_quotient_map I a).image.subset) (fun y =>
          ⟨natural_hom (ideal_quotient I a) y, by rw [toQuotient.def₂, natural_hom.def, ←(natural_hom I).preserve_mul, ←ideal_quotient_map.def]⟩) y⟩

    private abbrev sub_kernel_lift [Ring β] (f : α →ᵣ β) {I : Ideal α} (hI : I ⊆ f.kernel_ideal) : QClass I → β :=
      fun x => Quot.lift f.hom (fun a b (h : _ ∈ _) => by
        have : _ = _ := hI h
        rw [f.preserve_add, f.preserve_neg, sub_right, zero_add] at this
        exact neg_inj this) x

    def quotient_sub_kernel [Ring β] (f : α →ᵣ β) {I : Ideal α} (hI : I ⊆ f.kernel_ideal) : QClass I →ᵣ β := {
      hom := sub_kernel_lift f hI
      preserve_zero := @Quot.ind _ _ (fun x : QClass I => x = 0 → sub_kernel_lift f hI x = 0)
        (fun x hx => hI (natural_hom.kernel.mp hx)) _ rfl
      preserve_add := @Quotient.ind₂ _ _ (QSetoid I) (QSetoid I) (fun x y : QClass I => sub_kernel_lift f hI (x + y) =
        sub_kernel_lift f hI x + sub_kernel_lift f hI y) f.preserve_add
      preserve_neg := @Quot.ind _ _ (fun x : QClass I => sub_kernel_lift f hI (-x) = -sub_kernel_lift f hI x) f.preserve_neg
      preserve_mul := @Quotient.ind₂ _ _ (QSetoid I) (QSetoid I) (fun x y : QClass I => sub_kernel_lift f hI (x * y) =
        sub_kernel_lift f hI x * sub_kernel_lift f hI y) f.preserve_mul
    }

    def quotient_kernel [Ring β] (f : α →ᵣ β) : QClass f.kernel_ideal →ᵣ β := quotient_sub_kernel f (Subset.refl _)

    theorem quotient_kernel_injective [Ring β] (f : α →ᵣ β) : Function.injective (quotient_kernel f).hom :=
      @Quotient.ind₂ _ _ (QSetoid f.kernel_ideal) (QSetoid f.kernel_ideal) (fun x y : QClass f.kernel_ideal =>
        quotient_kernel f x = quotient_kernel f y → x = y) fun x y (h : f x = f y) => (QClass.equiv _ x y).mpr
          (by rw [f.preserve_add, f.preserve_neg, h, neg_add] : f _ = 0)

    theorem chinese_remainder_theorem (I J : Ideal α) (hIJ : Ideal.coprime I J) :
      QClass (I ∩ J) ≅ᵣ QClass I × QClass J :=
        let f : α →ᵣ QClass I × QClass J := {
          hom := fun x => (natural_hom I x, natural_hom J x)
          preserve_zero := rfl
          preserve_add := fun _ _ => rfl
          preserve_neg := fun _ => rfl
          preserve_mul := fun _ _ => rfl
        }
        have : I ∩ J = f.kernel_ideal := Ideal.ext'.mpr fun x =>
          ⟨fun hx => (by rw [←natural_hom.kernel.mpr hx.left, ←natural_hom.kernel.mpr hx.right] : f x = (0, 0)),
          fun hx => ⟨natural_hom.kernel.mp (Prod.mk.inj hx).left, natural_hom.kernel.mp (Prod.mk.inj hx).right⟩⟩
        this ▸ RIsomorphism.of_bijection (quotient_kernel f) ⟨quotient_kernel_injective f,
          fun (x, y) => let ⟨i, hi, j, hj, hij⟩ := is_unit_ideal.mp hIJ; @Quotient.ind₂ _ _ (QSetoid I) (QSetoid J)
            (fun (x : QClass I) (y : QClass J) => ∃ a : QClass f.kernel_ideal, quotient_kernel f a = (x, y))
              (fun x y => ⟨natural_hom _ (x * j + y * i),
                have : ∀ (x y i j : α) (I : Ideal α), i + j = 1 → i ∈ I → natural_hom I (x * j + y * i) = natural_hom I x :=
                  fun x y i j I hij hi => (QClass.equiv _ _ _).mpr (by
                    rw [(sub_right.mp (add_comm i j ▸ hij) : j = 1 + -i), mul_distrib_left, mul_one, mul_neg_swap, add_assoc,
                    ←mul_distrib_right, neg_add_distrib, add_assoc, neg_add, add_zero, ←neg_mul]; exact I.mul_closed _ hi)
                Prod.mk.injEq _ _ _ _ ▸ ⟨this x y i j I hij hi, add_comm _ _ ▸ this y x j i J (add_comm i j ▸ hij) hj⟩⟩) x y⟩

  end QuotientRing
end M4R
